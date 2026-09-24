#!/usr/bin/env node
// A gallery of what the "Arrange" button does, for tuning it: every case in lib/arrange.js, before
// and after arranging, with the energy of each layout term by term (see client/arrange.js).
//
//   node test/arrange-gallery.js [--only name,name] [--out dir]
//
// It serves static/ itself (build it first: npm run build, or npm run build:static), and writes
// <out>/index.html (by default test-results/arrange-gallery/) with the screenshots beside it.

const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const { chromium } = require('@playwright/test');
const { Olorin } = require('./helpers/olorin');
const { arrangeCases, loadCase } = require('./lib/arrange');

const PORT = process.env.OLORIN_PORT || 8125;
const VIEWPORT = { width: 1400, height: 900 };

function parseArgs() {
    const args = process.argv.slice(2);
    const out = { only: null, out: path.join(__dirname, '..', 'test-results', 'arrange-gallery') };
    for (let i = 0; i < args.length; i++) {
        if (args[i] === '--only') out.only = args[++i].split(',');
        else if (args[i] === '--out') out.out = path.resolve(args[++i]);
        else throw new Error('Unknown argument: ' + args[i]);
    }
    return out;
}

async function waitForServer(url) {
    for (let i = 0; i < 100; i++) {
        try { if ((await fetch(url)).ok) return; } catch (e) { /* not up yet */ }
        await new Promise((r) => setTimeout(r, 100));
    }
    throw new Error('The static server never came up at ' + url);
}

// Screenshot the whole diagram, however far it extends past the window, by growing the window to
// fit it for the moment.
async function shoot(page, file) {
    const size = await page.evaluate(() => {
        const c = document.getElementById('canvas');
        return { w: c.scrollWidth, h: c.scrollHeight };
    });
    await page.setViewportSize({ width: Math.max(VIEWPORT.width, size.w + 120),
                                 height: Math.max(VIEWPORT.height, size.h + 20) });
    await page.evaluate(() => { const d = document.getElementById('diagram'); d.scrollLeft = 0; d.scrollTop = 0; });
    await page.locator('#diagram').screenshot({ path: file });
    await page.setViewportSize(VIEWPORT);
}

// What a layout looks like on the page, measured rather than predicted: how many wire labels cover
// a block or another label, how many wires run backwards, and how much room it all takes.
async function measure(olorin) {
    const [labels, obstacles] = await Promise.all([olorin.overlappingLabels(), olorin.overlappingObstacles()]);
    const geo = await olorin.page.evaluate(() => {
        let backward = 0;
        const conns = window.__olorin.connections();
        const model = window.__olorin.layoutModel();
        const byId = Object.fromEntries(model.blocks.map((b) => [b.id, b]));
        const portX = (b, p) => b.x + p.dx + (p.right ? b.w : 0);
        model.wires.forEach((w) => {
            const s = byId[w.src.block], t = byId[w.tgt.block];
            if (s !== t && portX(t, t.ports[w.tgt.port]) < portX(s, s.ports[w.src.port])) backward++;
        });
        const c = document.getElementById('canvas');
        return { backward, width: c.scrollWidth, height: c.scrollHeight, wires: conns.length };
    });
    return { labelOverlaps: labels.length, labelOnBlock: obstacles.length, ...geo };
}

const fmt = (e) => Object.entries(e).map(([k, v]) => `${k} ${Math.round(v)}`).join(', ');
const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;');

async function main() {
    const opts = parseArgs();
    fs.mkdirSync(opts.out, { recursive: true });
    const server = spawn(process.execPath, [path.join(__dirname, 'server.js'), String(PORT)],
                         { stdio: 'ignore' });
    const browser = await chromium.launch();
    const rows = [];
    try {
        await waitForServer(`http://localhost:${PORT}/`);
        let cases = arrangeCases();
        if (opts.only) cases = cases.filter((c) => opts.only.includes(c.name));
        for (const c of cases) {
            // A fresh page each time, so nothing one case leaves open gets in the next one's way.
            const page = await browser.newPage({ viewport: VIEWPORT, baseURL: `http://localhost:${PORT}` });
            const olorin = new Olorin(page);
            await olorin.open({ code: c.level.code });
            process.stdout.write(`${c.name} (${c.level.name}) ... `);
            try {
                await loadCase(olorin, c);
                await shoot(page, path.join(opts.out, `${c.name}-before.png`));
                const measuredBefore = await measure(olorin);
                const result = await page.evaluate(async () => {
                    const t0 = performance.now();
                    const r = await window.__olorin.arrangement();
                    r.ms = Math.round(performance.now() - t0);
                    return r;
                });
                await page.click('#arrangeProof');
                await page.waitForFunction(() => !window.__olorin.arranging());
                await shoot(page, path.join(opts.out, `${c.name}-after.png`));
                const measuredAfter = await measure(olorin);
                rows.push({ c, result, measuredBefore, measuredAfter, complete: await olorin.isComplete() });
                console.log(`\n    energy   ${fmt(result.energy.before)}  ->  ${fmt(result.energy.after)}`
                            + `\n    crossings ${result.crossings}, through blocks ${result.through}, ${result.ms}ms`
                            + `\n    measured ${fmt(measuredBefore)}  ->  ${fmt(measuredAfter)}`);
            } catch (e) {
                rows.push({ c, error: e.message });
                console.log('FAILED: ' + e.message);
            }
            await page.close();
        }
    } finally {
        await browser.close();
        server.kill();
    }

    const html = `<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>Arrange gallery</title>
<style>
body { font-family: sans-serif; margin: 16px; }
.case { border-top: 1px solid #ccc; padding: 12px 0; }
.shots { display: flex; gap: 12px; align-items: flex-start; }
.shots figure { margin: 0; flex: 1; min-width: 0; }
.shots img { width: 100%; border: 1px solid #ddd; }
.meta { font-size: 13px; color: #444; }
.bad { color: #b00; font-weight: bold; }
</style></head><body>
<h1>Arrange gallery</h1>
${rows.map(({ c, result, measuredBefore, measuredAfter, complete, error }) => `<div class="case" id="${esc(c.name)}">
<h2>${esc(c.name)} <small>(level ${esc(c.level.name)})</small></h2>
${error ? `<p class="bad">${esc(error)}</p>` : `<p class="meta">
energy before: ${esc(fmt(result.energy.before))}<br>
energy after: ${esc(fmt(result.energy.after))}<br>
crossings after: ${result.crossings}, wires through blocks: ${result.through} (worked out in ${result.ms}ms)<br>
measured before: ${esc(fmt(measuredBefore))}<br>
measured after: ${esc(fmt(measuredAfter))}<br>
${result.backward.length ? `<span class="bad">wires left running backwards: ${esc(JSON.stringify(result.backward))}</span><br>` : ''}
${result.unresolved > 0.5 ? `<span class="bad">constraints unresolved by ${Math.round(result.unresolved)}px</span><br>` : ''}
${complete ? '' : '<span class="bad">not complete after arranging</span><br>'}
regions: ${esc(Object.entries(result.regions).filter(([, r]) => r).map(([b, r]) => b + '∈' + r).join(', '))}
</p>`}
<div class="shots">
<figure><img src="${esc(c.name)}-before.png"><figcaption>before</figcaption></figure>
<figure><img src="${esc(c.name)}-after.png"><figcaption>after</figcaption></figure>
</div></div>`).join('\n')}
</body></html>`;
    fs.writeFileSync(path.join(opts.out, 'index.html'), html);
    console.log('Wrote ' + path.join(opts.out, 'index.html'));
}

main().catch((e) => { console.error(e); process.exit(1); });

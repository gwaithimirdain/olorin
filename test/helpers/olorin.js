// Page-object helper for driving the Olorin app in Playwright tests.
//
// It wraps a Playwright `page` with high-level actions that mirror real user gestures:
//   - level selection and modal/hint dismissal (real clicks)
//   - dragging a rule from the palette onto the diagram (real HTML5 drag-and-drop events)
//   - the Save / Load / Clear buttons (real clicks)
//
// Creating wire connections and reading proof state go through window.__olorin, a tiny
// test seam the app exposes only when the page is loaded with "?test" in the URL (raw
// jsPlumb endpoint dragging is not reliably reproducible via synthetic mouse events).

class Olorin {
    constructor(page) {
        this.page = page;
    }

    // Load the app, suppressing the first-visit "About" modal and handling native dialogs
    // (e.g. the Clear confirm).  Dialogs are accepted by default; setDialogAction('dismiss')
    // switches to dismissing the next ones, to test "cancel" paths.  Resolves once interactive.
    async open() {
        this._dialogAction = 'accept';
        await this.page.addInitScript(() => localStorage.setItem('visited', 'true'));
        this.page.on('dialog', (d) => (this._dialogAction === 'dismiss' ? d.dismiss() : d.accept()));
        await this.page.goto('/?test=1', { waitUntil: 'load' });
        await this.page.waitForFunction(
            () => typeof window.__olorin !== 'undefined' && typeof window.Narya !== 'undefined',
            null,
            { timeout: 30000 },
        );
    }

    // Control how native confirm()/alert() dialogs are answered: 'accept' (default) or 'dismiss'.
    setDialogAction(action) {
        this._dialogAction = action;
    }

    // The current level's display name (without the "Level: " prefix), e.g. "1-1-1".
    currentLevelName() {
        return this.page.evaluate(() => document.getElementById('currentLevel').innerText.replace(/^Level:\s*/, ''));
    }

    // Pick a built-in level by its "world-stage-level" name, e.g. "1-1-1".
    async selectLevel(name) {
        // Make sure the level chooser is open (it closes after a level is picked).
        await this.page.evaluate(() => {
            const bg = document.getElementById('levelChooseBG');
            if (getComputedStyle(bg).display === 'none') document.getElementById('selectLevel').click();
        });
        await this.page.click(`#worlds .level[data-name="${name}"]`);
        await this.page.waitForFunction(
            (n) => document.getElementById('currentLevel').innerText.includes(n),
            name,
        );
        await this.dismissHints();
    }

    // Close the level hint overlay if it's showing (it's dismissed by clicking the backdrop).
    async dismissHints() {
        await this.page.evaluate(() => {
            const h = document.getElementById('hintBG');
            if (h && getComputedStyle(h).display !== 'none') h.click();
        });
    }

    // Whether the (non-modal) "level complete" pop-up is showing.
    completeBannerVisible() {
        return this.page.isVisible('#levelCompleteBanner');
    }

    // Advance to the next level via the "Next" button in the completion pop-up.
    async next() {
        await this.page.click('#nextLevel');
        await this.dismissHints();
    }

    // Drag a palette rule (e.g. "andI") onto the diagram at (x, y) relative to the diagram's
    // top-left.  Returns the id of the newly created node.
    async dragRule(ruleId, x, y) {
        await this.page.evaluate(({ ruleId, x, y }) => {
            const src = document.getElementById(ruleId);
            const diagram = document.getElementById('diagram');
            const dt = new DataTransfer();
            const fire = (el, type, cx, cy) => el.dispatchEvent(
                new DragEvent(type, { bubbles: true, cancelable: true, dataTransfer: dt, clientX: cx, clientY: cy }));
            const sr = src.getBoundingClientRect();
            fire(src, 'dragstart', sr.x + 5, sr.y + 5);
            const dr = diagram.getBoundingClientRect();
            fire(diagram, 'dragover', dr.x + x, dr.y + y);
            fire(diagram, 'drop', dr.x + x, dr.y + y);
            fire(src, 'dragend', dr.x + x, dr.y + y);
        }, { ruleId, x, y });
        await this.dismissHints();
        // The freshly added node is the last one pushed onto the nodes list.
        return this.page.evaluate(() => {
            const ns = window.__olorin.nodes();
            return ns[ns.length - 1].id;
        });
    }

    // Connect an output/assumption port to an input/subgoal port.  Each port is identified
    // as { vertex, sort, label }, matching the app's own endpoint parameters.
    async connect(source, target) {
        await this.page.evaluate(({ s, t }) => window.__olorin.connect(s, t), { s: source, t: target });
        await this.dismissHints();
    }

    // Move a node, to exercise that positions are saved/restored.
    async moveNode(id, left, top) {
        await this.page.evaluate(({ id, left, top }) => {
            const el = document.getElementById(id);
            el.style.left = left;
            el.style.top = top;
            window.__olorin.instance && window.__olorin.instance().revalidate(el);
        }, { id, left, top });
    }

    async clear() {
        await this.page.click('#clearProof'); // confirm() auto-accepted in open()
        await this.dismissHints();
    }

    // Whether the "Saved proof found" prompt is currently showing.
    savedPromptVisible() {
        return this.page.isVisible('#savedProofBG');
    }

    // Answer the "Saved proof found" prompt: load the saved proof, or discard it.
    async loadSaved() {
        await this.page.click('#loadSavedProof');
        await this.dismissHints();
    }

    async discardSaved() {
        await this.page.click('#discardSavedProof');
        await this.dismissHints();
    }

    nodes() {
        return this.page.evaluate(() => window.__olorin.nodes());
    }

    connections() {
        return this.page.evaluate(() => window.__olorin.connections());
    }

    isComplete() {
        return this.page.evaluate(() => window.__olorin.complete());
    }

    savedKey() {
        return this.page.evaluate(() => window.__olorin.savedProofKey());
    }

    // Open the Export modal, read the JSON it shows, close it, and return the JSON string.
    async exportText() {
        await this.page.click('#exportProof');
        await this.page.waitForSelector('#exportBG', { state: 'visible' });
        const json = await this.page.inputValue('#exportJson');
        await this.page.click('#doneExport');
        return json;
    }

    // Rebuild the proof from a snapshot object (as exported/autosaved), into the current level.
    async restore(state) {
        await this.page.evaluate((s) => window.__olorin.restore(s), state);
        await this.dismissHints();
    }

    // Paste JSON into the Import modal and submit it.
    async importText(json) {
        await this.page.click('#importProof');
        await this.page.waitForSelector('#importBG', { state: 'visible' });
        await this.page.fill('#importJson', json);
        await this.page.click('#submitImport');
        await this.dismissHints();
    }

    isVisible(selector) {
        return this.page.isVisible(selector);
    }

    // A representation of the proof state that is independent of the auto-generated node
    // ids (which change when a level is reset), suitable for asserting round-trip equality.
    // Nodes are tagged by rule + position, so same-rule nodes are still distinguished.
    async structuralState() {
        const [nodes, conns] = await Promise.all([this.nodes(), this.connections()]);
        const byId = Object.fromEntries(nodes.map((n) => [n.id, n]));
        const tag = (id) => {
            const n = byId[id];
            return `${n.rule}@${n.left},${n.top}`;
        };
        const port = (p) => `${tag(p.vertex)}|${p.sort}|${p.label || ''}`;
        return {
            nodes: nodes
                .map((n) => ({ rule: n.rule, name: n.name, value: n.value, left: n.left, top: n.top, width: n.width, height: n.height }))
                .sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b))),
            connections: conns
                .map((c) => ({ source: port(c.source), target: port(c.target), ty: c.ty }))
                .sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b))),
        };
    }
}

module.exports = { Olorin };

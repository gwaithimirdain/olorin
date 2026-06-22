// Minimal static file server for the Olorin test harness.
//
// It serves the built `static/` directory with the cross-origin isolation headers
// (COOP/COEP) that the app needs for Z3's SharedArrayBuffer.  Serving the headers
// directly means the `coi-serviceworker` shim sees `crossOriginIsolated === true`
// and skips its reload dance, which keeps Playwright navigation deterministic.
//
// Usage: node test/server.js [port] [rootDir]
//   defaults: port 8123, rootDir ../static

const http = require('http');
const fs = require('fs');
const path = require('path');

const PORT = parseInt(process.argv[2] || process.env.PORT || '8123', 10);
const ROOT = path.resolve(__dirname, process.argv[3] || '../static');

const MIME = {
    '.html': 'text/html; charset=utf-8',
    '.js': 'text/javascript; charset=utf-8',
    '.mjs': 'text/javascript; charset=utf-8',
    '.css': 'text/css; charset=utf-8',
    '.json': 'application/json; charset=utf-8',
    '.wasm': 'application/wasm',
    '.svg': 'image/svg+xml',
    '.png': 'image/png',
    '.jpg': 'image/jpeg',
    '.ico': 'image/x-icon',
    '.map': 'application/json; charset=utf-8',
};

const server = http.createServer((req, res) => {
    // Cross-origin isolation, required for SharedArrayBuffer (Z3).
    res.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
    res.setHeader('Cross-Origin-Embedder-Policy', 'require-corp');
    res.setHeader('Cross-Origin-Resource-Policy', 'cross-origin');

    let urlPath = decodeURIComponent(req.url.split('?')[0]);
    if (urlPath === '/') urlPath = '/index.html';

    // Resolve and prevent path traversal outside ROOT.
    const filePath = path.join(ROOT, urlPath);
    if (!filePath.startsWith(ROOT)) {
        res.writeHead(403).end('Forbidden');
        return;
    }

    fs.readFile(filePath, (err, data) => {
        if (err) {
            res.writeHead(404).end('Not found: ' + urlPath);
            return;
        }
        const ext = path.extname(filePath).toLowerCase();
        res.setHeader('Content-Type', MIME[ext] || 'application/octet-stream');
        res.writeHead(200).end(data);
    });
});

server.listen(PORT, () => {
    console.log(`olorin test server: http://localhost:${PORT}  (root: ${ROOT})`);
});

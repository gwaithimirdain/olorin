// HTTPS static server for running the built Olorin app over a LAN.
//
// Algebra/Inequality worlds use Z3, whose WebAssembly build is multithreaded and therefore
// needs SharedArrayBuffer.  The browser only exposes SharedArrayBuffer when the page is BOTH
//   (1) cross-origin isolated  -- COOP: same-origin + COEP: require-corp headers, and
//   (2) in a secure context    -- https://… or http://localhost (NOT bare-IP http).
// A plain `http://192.168.x.x` LAN URL fails (2), so even with the headers SharedArrayBuffer is
// unavailable and Z3 dies with "pthread_create: environment does not support SharedArrayBuffer".
//
// This server sends the isolation headers AND serves over HTTPS (with an auto-generated
// self-signed certificate), which makes a bare-IP LAN URL a secure context.  The browser will warn
// about the self-signed cert the first time; accept it once per device.
//
// Usage: node scripts/serve.js [port] [rootDir]
//   defaults: port 8443, rootDir ../static
//
// For same-machine use, http://localhost is already a secure context, so test/server.js (plain
// http + COI headers) is enough there; this script is specifically for other devices on the LAN.

const https = require('https');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { execFileSync } = require('child_process');

const PORT = parseInt(process.argv[2] || process.env.PORT || '8443', 10);
const ROOT = path.resolve(__dirname, process.argv[3] || '../static');
const CERT_DIR = path.resolve(__dirname, '../.certs');
const CERT = path.join(CERT_DIR, 'cert.pem');
const KEY = path.join(CERT_DIR, 'key.pem');

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

// All non-internal IPv4 addresses, so the cert (and the printed URLs) cover however the app is
// reached on the LAN.
function lanIPv4s() {
    return Object.values(os.networkInterfaces())
        .flat()
        .filter((i) => i && i.family === 'IPv4' && !i.internal)
        .map((i) => i.address);
}

// Generate a self-signed cert whose SAN lists localhost + every detected LAN IP, so the browser's
// name-check passes (it still warns that the cert is self-signed, which is unavoidable without a CA).
function ensureCert() {
    if (fs.existsSync(CERT) && fs.existsSync(KEY)) return;
    fs.mkdirSync(CERT_DIR, { recursive: true });
    const san = ['DNS:localhost', 'IP:127.0.0.1', ...lanIPv4s().map((ip) => `IP:${ip}`)].join(',');
    console.log('Generating self-signed certificate in .certs/ (SAN: ' + san + ') ...');
    execFileSync('openssl', [
        'req', '-x509', '-newkey', 'rsa:2048', '-nodes',
        '-keyout', KEY, '-out', CERT, '-days', '365',
        '-subj', '/CN=olorin-dev', '-addext', `subjectAltName=${san}`,
    ], { stdio: 'ignore' });
}

ensureCert();

const server = https.createServer({ key: fs.readFileSync(KEY), cert: fs.readFileSync(CERT) }, (req, res) => {
    // Cross-origin isolation, required (together with HTTPS) for SharedArrayBuffer (Z3).
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

server.listen(PORT, '0.0.0.0', () => {
    console.log(`olorin: serving ${ROOT} over HTTPS (cross-origin isolated) on port ${PORT}`);
    for (const ip of ['localhost', ...lanIPv4s()]) {
        console.log(`  https://${ip}:${PORT}/`);
    }
    console.log('Self-signed cert: your browser will warn once per device; accept it to proceed.');
});

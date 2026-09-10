// The password the "?test" URL parameter takes (see TEST_MODE in client/main.js).
//
// It is written down once, in the client, and read back here rather than copied, so that changing
// the word there is the whole change: nothing in the suite spells it out.

const fs = require('fs');
const path = require('path');

const MAIN = path.join(__dirname, '..', '..', 'client', 'main.js');

let cached = null;
function testPassword() {
    if (cached !== null) return cached;
    const src = fs.readFileSync(MAIN, 'utf8');
    const m = src.match(/const\s+TEST_PASSWORD\s*=\s*["']([^"']*)["']/);
    if (!m) {
        throw new Error(`client/main.js no longer declares TEST_PASSWORD; update ${__filename}.`);
    }
    cached = m[1];
    return cached;
}

// The query string that opens the app in test mode, with anything else appended to it.
const testQuery = (extra = '') => `/?test=${encodeURIComponent(testPassword())}${extra}`;

module.exports = { testPassword, testQuery };

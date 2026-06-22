// Playwright configuration for the Olorin browser interaction tests.
//
// The tests run against the built `static/` directory served with cross-origin
// isolation headers by test/server.js.  Build the assets first (see test/README.md):
//   ./scripts/build-static.sh
//
// Then run:  npm run test:e2e

const { defineConfig, devices } = require('@playwright/test');

const PORT = process.env.OLORIN_PORT || 8123;
const URL = `http://localhost:${PORT}`;

module.exports = defineConfig({
    testDir: './test/e2e',
    fullyParallel: true,
    forbidOnly: !!process.env.CI,
    retries: process.env.CI ? 1 : 0,
    reporter: process.env.CI ? [['list'], ['html', { open: 'never' }]] : 'list',
    use: {
        baseURL: URL,
        trace: 'on-first-retry',
        // The app needs a reasonably sized viewport for the diagram layout.
        viewport: { width: 1400, height: 900 },
    },
    projects: [
        { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
    ],
    // Auto-start the static server for the duration of the run.
    webServer: {
        command: `node test/server.js ${PORT}`,
        url: URL,
        reuseExistingServer: !process.env.CI,
        stdout: 'ignore',
        stderr: 'pipe',
    },
});

const fs = require('fs');
const path = require('path');

const OUT = path.resolve(__dirname, 'static');

// Bundles loaded later than the page itself -- the worker that works out an arrangement
// (client/arrange-worker.js) -- are named for what's in them, so that a browser that reloads the
// page can't go on using an old one it has cached: the page asks for them by name.  That leaves
// the old ones lying about in static/ after each build, so they're cleared away.
class RemoveStaleChunks {
    apply(compiler) {
        compiler.hooks.afterEmit.tap('RemoveStaleChunks', (compilation) => {
            const current = new Set(Object.keys(compilation.assets));
            fs.readdirSync(OUT)
                .filter((f) => /^[\w-]+\.[0-9a-f]{8}\.bundle\.js$/.test(f) && !current.has(f))
                .forEach((f) => fs.unlinkSync(path.join(OUT, f)));
        });
    }
}

module.exports = {
    entry: {
        main: './client/main.js',
        grades: './client/grades.js',
    },
    output: {
        filename: '[name].bundle.js',
        chunkFilename: '[name].[contenthash:8].bundle.js',
        path: OUT,
    },
    mode: 'development',
    plugins: [new RemoveStaleChunks()],
};

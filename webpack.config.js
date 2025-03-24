const path = require('path');

module.exports = {
    entry: {
        main: './client/main.js',
        grades: './client/grades.js',
    },
    output: {
        filename: '[name].bundle.js',
        path: path.resolve(__dirname, 'static'),
    },
    mode: 'development',
};

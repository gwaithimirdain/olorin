// Works out an arrangement (client/arrange.js) off the main thread, since a big proof can take a
// second or two, and the page should stay alive meanwhile.  Each message is { id, model }, and is
// answered with { id, result } or, should arranging fail, { id, error }.

import { arrange } from "./arrange.js";

self.onmessage = function (e) {
    const { id, model } = e.data;
    try {
        self.postMessage({ id: id, result: arrange(model) });
    } catch(err) {
        self.postMessage({ id: id, error: String((err && err.stack) || err) });
    }
};

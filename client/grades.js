import { Parser } from '@json2csv/plainjs';
import { LEVELS, saveable, legacySaveables } from "./levels.js";

const loginError = document.getElementById("loginError");

const loginCourse = document.getElementById("loginCourse");
const loginPassword = document.getElementById("loginPassword");

const submit = document.getElementById("submit");

submit.onclick = function() {
    const course = loginCourse.value;
    const password = loginPassword.value;
    const xhr = new XMLHttpRequest();
    xhr.open('POST', '/grades', true);
    xhr.setRequestHeader('Content-Type', 'application/json;charset=UTF-8');
    let loginError = document.getElementById('loginError');
    xhr.onload = function() {
        if (xhr.status === 200) {
            let res = JSON.parse(xhr.responseText);
            if(res.error) {
                loginError.textContent = "Error: " + res.error;
                loginError.style.color = "#ff0000";
                loginError.style.visibility = 'visible';
            } else {
                const numbers = [];
                const fields = [ "email" ];
                LEVELS.forEach(function (world, x) {
                    world.stages.forEach(function (stage, y) {
                        stage.levels.forEach(function (level, z) {
                            const name = (x+1) + '-' + (y+1) + '-' + (z+1);
                            fields.push(name);
                            // DEPRECATED (see levels.js): a student who solved one of the levels
                            // whose notation changed, and hasn't opened the game since the client
                            // started migrating those records, still has it under the old key.
                            numbers.push({
                                name: name,
                                str: JSON.stringify(saveable(level)),
                                legacy: legacySaveables(level).map((s) => JSON.stringify(s)),
                            });
                        });
                    });
                });
                const opts = {
                    fields: fields,
                    transforms:  [ function(oldrec) {
                        const newrec = { email: oldrec.key };
                        numbers.forEach(function (level) {
                            const solved = oldrec.doc
                                  && (oldrec.doc[level.str]
                                      || level.legacy.map((k) => oldrec.doc[k]).find(Boolean));
                            newrec[level.name] = solved && solved.complete ? solved.difficulty + 1 : 0;
                        });
                        console.log(newrec);
                        return newrec;
                    } ],
                };
                const parser = new Parser(opts);
                const csv = parser.parse(res);
                var blob = new Blob([csv], {type: 'text/csv'});
                // This seems to be the standard hack to pop up a save-as dialog box from javascript
                let a = document.createElement("a");
                a.style = "display: none";
                document.body.appendChild(a);
                let url = window.URL.createObjectURL(blob);
                a.href = url;
                a.download = 'grades.csv';
                a.click();
                window.URL.revokeObjectURL(url);                                                
            }
        } else {
            let res = JSON.parse(xhr.responseText);
            loginError.innerText = 'Error: ' + res.error;
            // Why is this color not getting used from the HTML style attribute?
            loginError.style.color = "#ff0000";
            loginError.style.visibility = 'visible';
        }
    };
    const data = { course: course, password: password };
    xhr.send(JSON.stringify(data));
};

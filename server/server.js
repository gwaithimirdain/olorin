const PORT = 80;
const http = require('http');
const cradle = require('cradle');
const fs = require('fs');
const path = require('path');
const child_process = require('child_process');
const tmp = require('tmp');
tmp.setGracefulCleanup();

const configPath = path.join(__dirname, 'config.json');
let config;
try {
    const rawConfig = fs.readFileSync(configPath, 'utf-8');
    config = JSON.parse(rawConfig);
} catch (err) {
    console.error('Failed to read or parse config.json:', err);
    process.exit(1);
}

const connection = new cradle.Connection('http://127.0.0.1', 5984, { auth: config });

const courseDB = connection.database('courses');
courseDB.exists((err, exists) => {
    if (err || !exists) {
	console.error('No courses database:', err);
    }
});

const studentDB = connection.database('students');
studentDB.exists((err, exists) => {
    if (err || !exists) {
	console.error('No students database:', err);
    }
});

const server = http.createServer(async (req, res) => {
    // Serve static files for GET requests to /static/...
    if (req.method === 'GET') {
	let url = (req.url === '/' ? '/index.html' : req.url);
	const filePath = path.join(__dirname, 'static', url);
	fs.readFile(filePath, (err, data) => {
	    if (err) {
		res.writeHead(404, { 'Content-Type': 'text/plain' });
		res.end('File not found');
	    } else {
		// A simple guess for content type by extension
		const ext = path.extname(filePath);
		let contentType = 'text/plain';
		if (ext === '.html') contentType = 'text/html';
		if (ext === '.js') contentType = 'text/javascript';
		if (ext === '.wasm') contentType = 'application/wasm';
		if (ext === '.css') contentType = 'text/css';
		if (ext === '.svg') contentType = 'image/svg+xml';
		// Send the data
		res.writeHead(200, { 'Content-Type': contentType });
		res.end(data);
	    }
	});
    } else if (req.method === 'POST') {
	let body = '';
	req.on('data', (chunk) => { body += chunk; });
	req.on('end', () => {
	    try {
		const data = JSON.parse(body);
		handlePost(res, req.url, data);
	    } catch (parseErr) {
		res.writeHead(400, { 'Content-Type': 'application/json' });
		res.end(JSON.stringify({ error: 'Invalid JSON: ' + parseErr.message }));
	    }
	});
    } else {
	res.writeHead(404, { 'Content-Type': 'text/plain' });
	res.end('Not Found');
    }
});

server.listen(PORT, () => {
    console.log(`Server running on http://localhost:${PORT}`);
});

function handlePost(res, url, data) {
    if(url === '/login') {
	courseDB.get(data.course, function (err, course) {
	    if(err || course.error) {
		res.writeHead(500, { 'Content-Type': 'application/json' });
		res.end(JSON.stringify({ error: 'Invalid Course ID' }));
	    } else if(course.students.includes(data.email)) {
		studentDB.get(data.email, function (err, student) {
		    if(err || student.error) {
			studentDB.save(data.email, {}, function (err, createResponse) {
			    if(err) {
				res.writeHead(500, { 'Content-Type': 'application/json' });
				res.end(JSON.stringify({ error: 'Error creating user' }));
			    } else {
				res.writeHead(200, { 'Content-Type': 'application/json' });
				res.end(JSON.stringify({ visited: false }));
			    }
			});
		    } else {
			res.writeHead(200, { 'Content-Type': 'application/json' });
			student.visited = true;
			res.end(JSON.stringify(student));
		    }
		});
	    } else {
		res.writeHead(500, { 'Content-Type': 'application/json' });
		res.end(JSON.stringify({ error: 'That email is not enrolled in that course' }));
	    }
	})
    } else if (url === '/solve') {
	studentDB.get(data.email, function (err, student) {
	    if(err || student.error) {
		res.writeHead(500, { 'Content-Type': 'application/json' });
		res.end(JSON.stringify({ error: 'Invalid user: ' + student.error }));
	    } else {
		student[data.key] = data.value;
		// Save the most recent difficulty and world they solved something with
		student.difficulty = data.difficulty;
		student.world = data.world;
		studentDB.save(student, function (err, saveResponse) {
		    if(err || saveResponse.error) {
			res.writeHead(500, { 'Content-Type': 'application/json' });
			res.end(JSON.stringify({ error: 'Error saving:' + (err || saveResponse.error) }));
		    } else {
			res.writeHead(200, { 'Content-Type': 'application/json' });
			res.end(JSON.stringify({ok : "Saved"}));
		    }
		});
	    }
	});
    } else {
	res.writeHead(404, { 'Content-Type': 'text/plain' });
	res.end('Not Found');
    }
}

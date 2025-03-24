const PORT = 443;
const https = require('https');
const cradle = require('cradle');
const fs = require('fs');
const path = require('path');

const configPath = path.join(__dirname, 'config.json');
let config;
try {
    const rawConfig = fs.readFileSync(configPath, 'utf-8');
    config = JSON.parse(rawConfig);
} catch (err) {
    console.error('Failed to read or parse config.json:', err);
    process.exit(1);
}

const httpsOptions = {
    key: fs.readFileSync(path.join(__dirname, config.keyfile)),
    cert: fs.readFileSync(path.join(__dirname, config.crtfile))
};

const connection = new cradle.Connection(
    'http://127.0.0.1', 5984,
    { auth:
      { username: config.username,
	password: config.password,
      },
    });

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

const server = https.createServer(httpsOptions, async (req, res) => {
    if (req.method === 'GET') {
	let url = (req.url === '/' ? '/index.html' : req.url);
	const filePath = path.join(__dirname, 'sslstatic', url);
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
    console.log(`Secure server running on http://localhost:${PORT}`);
});

function handlePost(res, url, data) {
    if (url === '/grades') {
	courseDB.get(data.course, function (err, course) {
	    if(err || course.error || (course.password != data.password)) {
		res.writeHead(500, { 'Content-Type': 'application/json' });
		res.end(JSON.stringify({ error: 'Invalid Login' }));
	    } else {
		studentDB.get(course.students, function (err, students) {
		    if(err || students.error) {
			res.writeHead(500, { 'Content-Type': 'application/json' });
			res.end(JSON.stringify({ error: 'Error ' + students.error }));
		    } else {
			res.writeHead(200, { 'Content-Type': 'application/json' });
			res.end(JSON.stringify(students));
		    }
		});
	    }
	});
    } else {
	res.writeHead(404, { 'Content-Type': 'text/plain' });
	res.end('Not Found');
    }
}

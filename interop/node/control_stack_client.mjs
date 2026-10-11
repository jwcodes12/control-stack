/**
 * Minimal language-independent control-stack broker client for Node.js.
 * This transports exactly one JSON request per Unix socket connection.
 *
 * Authentication is performed by the TRUSTED broker using SO_PEERCRED,
 * never by a UID field in this client. The socket directory and broker
 * identity must be provisioned/trusted by the host. This module alone
 * does not confine a Node process, and does not validate the server's UID.
 */
import net from 'node:net';
import { pathToFileURL } from 'node:url';

const MAX_REQUEST_BYTES = 1_500_000;
const MAX_REPLY_BYTES = 20_000;

export function request(socketPath, payload, timeoutMs = 6000) {
  if (typeof socketPath !== 'string' || !socketPath || !payload ||
      Object.getPrototypeOf(payload) !== Object.prototype ||
      typeof payload.op !== 'string') {
    return Promise.reject(new TypeError('invalid endpoint or request'));
  }
  let frame;
  try {
    frame = Buffer.from(JSON.stringify(payload) + '\n', 'utf8');
  } catch (error) {
    return Promise.reject(error);
  }
  if (frame.length > MAX_REQUEST_BYTES) {
    return Promise.reject(new RangeError('request too large'));
  }
  return new Promise((resolve, reject) => {
    const conn = net.createConnection({ path: socketPath });
    let chunks = [];
    let size = 0;
    let settled = false;
    const fail = error => {
      if (settled) return;
      settled = true;
      conn.destroy();
      reject(error);
    };
    conn.setTimeout(timeoutMs, () => fail(new Error('broker timeout')));
    conn.on('error', fail);
    conn.on('connect', () => conn.write(frame));
    conn.on('data', chunk => {
      if (settled) return;
      size += chunk.length;
      if (size >= MAX_REPLY_BYTES) {
        fail(new Error('broker response too large'));
        return;
      }
      chunks.push(chunk);
      const received = Buffer.concat(chunks, size);
      const end = received.indexOf(10);
      if (end >= 0) {
        if (end !== received.length - 1) {
          fail(new Error('unexpected trailing response bytes'));
          return;
        }
        try {
          const decoder = new TextDecoder('utf-8', { fatal: true });
          const parsed = JSON.parse(decoder.decode(received.subarray(0, end)));
          if (!parsed || Array.isArray(parsed) || typeof parsed !== 'object' ||
              typeof parsed.ok !== 'boolean') {
            throw new Error('invalid broker response shape');
          }
          settled = true;
          conn.end();
          resolve(parsed);
        } catch (error) {
          fail(error);
        }
      }
    });
    conn.on('end', () => {
      if (!settled) fail(new Error('broker closed without response'));
    });
  });
}

// Demonstration CLI: JSON payload on stdin, single newline response on stdout.
// Never supply secret/staged artifact content as a shell command-line argument.
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const endpoint = process.argv[2];
  if (!endpoint) {
    console.error('usage: node control_stack_client.mjs SOCKET < REQUEST_JSON');
    process.exitCode = 2;
  } else {
    const pieces = [];
    for await (const piece of process.stdin) pieces.push(piece);
    try {
      const req = JSON.parse(Buffer.concat(pieces).toString('utf8'));
      const result = await request(endpoint, req);
      process.stdout.write(JSON.stringify(result) + '\n');
    } catch (err) {
      // No source body, endpoint, or attached credentials in error strings.
      console.error('BROKER_CLIENT_ERROR');
      process.exitCode = 1;
    }
  }
}

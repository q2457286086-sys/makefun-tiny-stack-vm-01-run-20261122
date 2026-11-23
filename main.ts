// tiny-stack-vm-01: a stack machine for make.fun's tiny stack ISA (ISA.md).
// For every /input/<id> (program.bin + input.bin) it writes
// /output/<id>/stdout.bin (the exact bytes written) and exit.txt (0-255).
// Node 22, standard library only; MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR
// stand in for /input and /output on a local run.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
const STEP_MAX = 1_000_000;
const OUT_MAX = 65_536;

// Immediates are little-endian. Runs one program; returns { out, exit }.
function run(prog, input) {
  const mem = new Int32Array(256);
  const st = [];
  const calls = [];
  const out = [];
  let pc = 0;
  let ip = 0;
  let steps = 0;
  const done = (exit) => ({ out, exit });
  const trap = (code) => done(code);

  for (;;) {
    if (steps >= STEP_MAX) return trap(10);
    if (pc < 0 || pc >= prog.length) return trap(9);
    const op = prog[pc];
    let ilen = 0;
    if (op === 0x01) ilen = 1;
    else if (op === 0x02) ilen = 4;
    else if (op >= 0x30 && op <= 0x33) ilen = 2;
    else if (
      op > 0x07 && !(op >= 0x10 && op <= 0x22) &&
      !(op >= 0x30 && op <= 0x34) &&
      !(op >= 0x40 && op <= 0x41) &&
      !(op >= 0x50 && op <= 0x53)
    ) return trap(5);
    if (pc + 1 + ilen > prog.length) return trap(9);
    const next = pc + 1 + ilen;
    steps++;
    const need = (n) => st.length < n ? trap(2) : 0;
    const room = () => st.length >= 256 ? trap(3) : 0;
    let t;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: { // PUSH8, sign-extended
        if ((t = room())) return t;
        const b = prog[pc + 1];
        st.push(b >= 128 ? b - 256 : b);
        break;
      }
      case 0x02: { // PUSH32, little-endian signed
        if ((t = room())) return t;
        st.push(
          prog[pc + 1] | (prog[pc + 2] << 8) |
          (prog[pc + 3] << 16) | (prog[pc + 4] << 24),
        );
        break;
      }
      case 0x03: if ((t = need(1))) return t; st.pop(); break; // POP
      case 0x04: { // DUP
        if ((t = need(1))) return t;
        if ((t = room())) return t;
        st.push(st[st.length - 1]);
        break;
      }
      case 0x05: { // SWAP
        if ((t = need(2))) return t;
        const a = st[st.length - 1];
        st[st.length - 1] = st[st.length - 2];
        st[st.length - 2] = a;
        break;
      }
      case 0x06: { // OVER
        if ((t = need(2))) return t;
        if ((t = room())) return t;
        st.push(st[st.length - 2]);
        break;
      }
      case 0x07: { // ROT ( a b c -- b c a )
        if ((t = need(3))) return t;
        const a = st[st.length - 3];
        st[st.length - 3] = st[st.length - 2];
        st[st.length - 2] = st[st.length - 1];
        st[st.length - 1] = a;
        break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14:
      case 0x15: case 0x16: case 0x18: case 0x19: case 0x1a:
      case 0x1c: case 0x1d: case 0x1e: case 0x20: case 0x21:
      case 0x22: {
        if ((t = need(2))) return t;
        const b = st.pop();
        const a = st.pop();
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { // DIV, truncate toward zero
          if (b === 0) return trap(4);
          r = Math.trunc(a / b) | 0;
        } else if (op === 0x14) { // MOD, sign of a
          if (b === 0) return trap(4);
          r = (a % b) | 0;
        } else if (op === 0x15) { // DIVU
          if (b === 0) return trap(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU
          if (b === 0) return trap(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        st.push(r);
        break;
      }
      case 0x17: if ((t = need(1))) return t; st.push((-st.pop()) | 0); break; // NEG
      case 0x1b: if ((t = need(1))) return t; st.push(~st.pop()); break; // NOT
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ
        let off = prog[pc + 1] | (prog[pc + 2] << 8);
        if (off >= 32768) off -= 65536;
        if (op === 0x30) { pc = next + off; continue; }
        if ((t = need(1))) return t;
        const v = st.pop();
        if ((op === 0x31 && v === 0) || (op === 0x32 && v !== 0)) {
          pc = next + off;
          continue;
        }
        break;
      }
      case 0x33: { // CALL, unsigned target
        if (calls.length >= 64) return trap(7);
        calls.push(next);
        pc = prog[pc + 1] | (prog[pc + 2] << 8);
        continue;
      }
      case 0x34: { // RET
        if (calls.length === 0) return trap(8);
        pc = calls.pop();
        continue;
      }
      case 0x40: { // LOAD
        if ((t = need(1))) return t;
        const a = st.pop();
        if (a < 0 || a > 255) return trap(6);
        st.push(mem[a]);
        break;
      }
      case 0x41: { // STORE ( v addr -- )
        if ((t = need(2))) return t;
        const a = st.pop();
        const v = st.pop();
        if (a < 0 || a > 255) return trap(6);
        mem[a] = v;
        break;
      }
      case 0x50: { // PRINT, decimal ASCII, no newline
        if ((t = need(1))) return t;
        const s = String(st.pop());
        if (out.length + s.length > OUT_MAX) return trap(11);
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        break;
      }
      case 0x51: { // PUTC
        if ((t = need(1))) return t;
        if (out.length + 1 > OUT_MAX) return trap(11);
        out.push(st.pop() & 255);
        break;
      }
      case 0x52: { // IN, -1 once the input is used up
        if ((t = room())) return t;
        st.push(ip < input.length ? input[ip++] : -1);
        break;
      }
      case 0x53: { // EXIT, low byte of the code
        if ((t = need(1))) return t;
        return done(st.pop() & 255);
      }
    }
    pc = next;
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const prog = readFileSync(join(IN_DIR, id, "program.bin"));
  const input = readFileSync(join(IN_DIR, id, "input.bin"));
  const { out, exit } = run(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, "stdout.bin"), Buffer.from(out));
  writeFileSync(join(OUT_DIR, id, "exit.txt"), `${exit}\n`);
}

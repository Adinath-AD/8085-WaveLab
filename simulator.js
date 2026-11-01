// 8085 WaveLab – DSO edition
// Educational 8085 instruction subset with a virtual 8-bit DAC and DSO display.

const $ = (id) => document.getElementById(id);

const examples = {
  triangle: `; TRIANGULAR WAVEFORM
START: XRA A
UP:    OUT 00H
       INR A
       CPI FFH
       JNZ UP
DOWN:  OUT 00H
       DCR A
       CPI 00H
       JNZ DOWN
       JMP START`,

  square: `; SQUARE WAVEFORM – approximately 50% duty cycle
START: MVI A, FFH
       MVI B, 80H
HIGH:  OUT 00H
       DCR B
       JNZ HIGH
       MVI A, 00H
       MVI B, 80H
LOW:   OUT 00H
       DCR B
       JNZ LOW
       JMP START`,

  ramp: `; RAMP / SAWTOOTH WAVEFORM
START: XRA A
RAMP:  OUT 00H
       INR A
       JMP RAMP`
};

let cpu;
let program = [];
let labels = {};
let chart;
let running = false;
let timer = null;
let samples = [];
let totalSamples = 0;
let nextSampleIndex = 0;
let instructionCount = 0;
let lastInstruction = "Not started";
let assembledSnapshot = "";
let dsoFrozen = false;
let autoSetPending = false;
let lastVisibleSamples = [];

const MAX_STORED_SAMPLES = 12000;
const RENDER_EVERY_N_SAMPLES = 8;
const TIME_BASES = [0.1, 0.2, 0.5, 1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000];
const VOLTS_PER_DIV = [0.05, 0.1, 0.2, 0.5, 1, 2, 5, 10];

const hex = (n, digits = 2) => (n & 0xFFFF).toString(16).toUpperCase().padStart(digits, "0") + "H";
const byte = (n) => n & 0xFF;

function parseNumber(raw) {
  const s = String(raw).trim().toUpperCase();
  if (/^[0-9A-F]+H$/.test(s)) return parseInt(s.slice(0, -1), 16);
  if (/^0X[0-9A-F]+$/.test(s)) return parseInt(s.slice(2), 16);
  if (/^[0-9]+$/.test(s)) return parseInt(s, 10);
  throw new Error(`Invalid number "${raw}"`);
}

const parity = (v) => (v.toString(2).replace(/0/g, "").length % 2) === 0;
const signed = (v) => (v & 0x80) !== 0;

function instructionSize(op) {
  if (["MVI", "ADI", "SUI", "ANI", "ORI", "XRI", "CPI", "IN", "OUT"].includes(op)) return 2;
  if (op === "LXI" || ["JMP", "JNZ", "JZ", "JC", "JNC"].includes(op)) return 3;
  return 1;
}

function assemble(source, start) {
  const rawLines = source.split(/\r?\n/);
  const parsed = [];
  let address = start;
  const labelMap = {};

  for (let i = 0; i < rawLines.length; i++) {
    let line = rawLines[i].split(";")[0].trim();
    if (!line) continue;

    let label = null;
    const match = line.match(/^([A-Za-z_][\w]*):\s*(.*)$/);
    if (match) {
      label = match[1].toUpperCase();
      line = match[2].trim();
    }

    if (label) {
      if (labelMap[label] !== undefined) throw new Error(`Line ${i + 1}: Duplicate label ${label}`);
      labelMap[label] = address;
    }
    if (!line) continue;

    const parts = line.match(/^(\S+)(?:\s+(.*))?$/);
    const op = parts[1].toUpperCase();
    const operandText = (parts[2] || "").trim();
    const args = operandText ? operandText.split(",").map(x => x.trim().toUpperCase()) : [];
    const allowed = ["MVI", "MOV", "LXI", "XRA", "INR", "DCR", "CPI", "OUT", "IN", "JNZ", "JZ", "JMP", "JC", "JNC", "HLT", "NOP", "ADI", "SUI", "ANI", "ORI", "XRI"];
    const expected = { MVI: 2, MOV: 2, LXI: 2, XRA: 1, INR: 1, DCR: 1, CPI: 1, OUT: 1, IN: 1, JNZ: 1, JZ: 1, JMP: 1, JC: 1, JNC: 1, HLT: 0, NOP: 0, ADI: 1, SUI: 1, ANI: 1, ORI: 1, XRI: 1 };

    if (!allowed.includes(op)) throw new Error(`Line ${i + 1}: Unknown instruction "${op}"`);
    if (args.length !== expected[op]) throw new Error(`Line ${i + 1}: ${op} expects ${expected[op]} operand(s)`);

    const size = instructionSize(op);
    parsed.push({ op, args, line: i + 1, source: rawLines[i].trim(), address, size });
    address += size;
    if (address > 0x10000) throw new Error(`Line ${i + 1}: Program exceeds 64 KB memory`);
  }

  for (const ins of parsed) {
    if (["JNZ", "JZ", "JMP", "JC", "JNC"].includes(ins.op)) {
      const target = ins.args[0];
      if (labelMap[target] === undefined) {
        try {
          const n = parseNumber(target);
          if (n > 0xFFFF) throw new Error();
          ins.target = n;
        } catch {
          throw new Error(`Line ${ins.line}: Unknown label or invalid address "${target}"`);
        }
      } else {
        ins.target = labelMap[target];
      }
    }

    if (ins.op === "OUT" || ins.op === "IN") {
      const p = parseNumber(ins.args[0]);
      if (p > 255) throw new Error(`Line ${ins.line}: I/O port must be 00H–FFH`);
      ins.port = p;
    }
    if (ins.op === "MVI" && (!isRegister(ins.args[0]) || parseNumber(ins.args[1]) > 255)) throw new Error(`Line ${ins.line}: Invalid MVI operands`);
    if (["INR", "DCR", "XRA"].includes(ins.op) && !isRegister(ins.args[0])) throw new Error(`Line ${ins.line}: Invalid register`);
    if (ins.op === "CPI" && parseNumber(ins.args[0]) > 255) throw new Error(`Line ${ins.line}: CPI value must fit in 8 bits`);
    if (ins.op === "MOV" && (!isRegister(ins.args[0]) || !isRegister(ins.args[1]))) throw new Error(`Line ${ins.line}: MOV requires two registers`);
    if (ins.op === "LXI" && (!["B", "D", "H", "SP"].includes(ins.args[0]) || parseNumber(ins.args[1]) > 65535)) throw new Error(`Line ${ins.line}: Invalid LXI operands`);
    if (["ADI", "SUI", "ANI", "ORI", "XRI"].includes(ins.op) && parseNumber(ins.args[0]) > 255) throw new Error(`Line ${ins.line}: Immediate value must fit in 8 bits`);
  }

  return { instructions: parsed, labels: labelMap };
}

function isRegister(r) {
  return ["A", "B", "C", "D", "E", "H", "L", "M"].includes(r);
}

function makeCPU(start) {
  return {
    r: { A: 0, B: 0, C: 0, D: 0, E: 0, H: 0, L: 0 },
    PC: start,
    SP: 0xFFFF,
    f: { S: 0, Z: 0, AC: 0, P: 0, CY: 0 },
    halted: false,
    memory: new Uint8Array(65536),
    ports: new Uint8Array(256)
  };
}

function getReg(name) {
  if (name === "M") return cpu.memory[(cpu.r.H << 8) | cpu.r.L];
  return cpu.r[name];
}

function setReg(name, value) {
  value = byte(value);
  if (name === "M") cpu.memory[(cpu.r.H << 8) | cpu.r.L] = value;
  else cpu.r[name] = value;
}

function setSZP(v) {
  v = byte(v);
  cpu.f.S = signed(v) ? 1 : 0;
  cpu.f.Z = v === 0 ? 1 : 0;
  cpu.f.P = parity(v) ? 1 : 0;
}

function fetchInstruction() {
  return program.find(x => x.address === cpu.PC);
}

function executeOne(refresh = true) {
  if (cpu.halted) return false;
  const ins = fetchInstruction();
  if (!ins) throw new Error(`Execution reached ${hex(cpu.PC, 4)}, which is not a program instruction. Check your jump address.`);

  const [a, b] = ins.args;
  let next = cpu.PC + ins.size;
  lastInstruction = `${hex(ins.address, 4)}  ${ins.source}`;

  switch (ins.op) {
    case "NOP": break;
    case "HLT": cpu.halted = true; break;
    case "MVI": setReg(a, parseNumber(b)); break;
    case "MOV": setReg(a, getReg(b)); break;
    case "LXI": {
      const v = parseNumber(b);
      if (a === "SP") cpu.SP = v;
      else {
        const pair = { B: "C", D: "E", H: "L" };
        cpu.r[a] = v >> 8;
        cpu.r[pair[a]] = v & 255;
      }
      break;
    }
    case "XRA": {
      const v = cpu.r.A ^ getReg(a);
      cpu.r.A = byte(v);
      cpu.f.AC = 0;
      cpu.f.CY = 0;
      setSZP(v);
      break;
    }
    case "INR": {
      const old = getReg(a), v = byte(old + 1);
      setReg(a, v);
      cpu.f.AC = (old & 15) === 15 ? 1 : 0;
      setSZP(v);
      break;
    }
    case "DCR": {
      const old = getReg(a), v = byte(old - 1);
      setReg(a, v);
      cpu.f.AC = (old & 15) === 0 ? 1 : 0;
      setSZP(v);
      break;
    }
    case "CPI": {
      const v = parseNumber(a), result = byte(cpu.r.A - v);
      cpu.f.CY = cpu.r.A < v ? 1 : 0;
      cpu.f.AC = (cpu.r.A & 15) < (v & 15) ? 1 : 0;
      setSZP(result);
      break;
    }
    case "OUT":
      cpu.ports[ins.port] = cpu.r.A;
      if (ins.port === parseNumber($("dacPort").value)) addSample(cpu.r.A);
      break;
    case "IN": cpu.r.A = cpu.ports[ins.port]; setSZP(cpu.r.A); break;
    case "JMP": next = ins.target; break;
    case "JNZ": if (!cpu.f.Z) next = ins.target; break;
    case "JZ": if (cpu.f.Z) next = ins.target; break;
    case "JC": if (cpu.f.CY) next = ins.target; break;
    case "JNC": if (!cpu.f.CY) next = ins.target; break;
    case "ADI": {
      const v = parseNumber(a), sum = cpu.r.A + v;
      cpu.f.CY = sum > 255 ? 1 : 0;
      cpu.f.AC = ((cpu.r.A & 15) + (v & 15)) > 15 ? 1 : 0;
      cpu.r.A = byte(sum);
      setSZP(cpu.r.A);
      break;
    }
    case "SUI": {
      const v = parseNumber(a), old = cpu.r.A;
      cpu.f.CY = old < v ? 1 : 0;
      cpu.f.AC = (old & 15) < (v & 15) ? 1 : 0;
      cpu.r.A = byte(old - v);
      setSZP(cpu.r.A);
      break;
    }
    case "ANI": case "ORI": case "XRI": {
      const v = parseNumber(a);
      cpu.r.A = byte(ins.op === "ANI" ? (cpu.r.A & v) : ins.op === "ORI" ? (cpu.r.A | v) : (cpu.r.A ^ v));
      cpu.f.CY = 0;
      cpu.f.AC = ins.op === "ANI" ? 1 : 0;
      setSZP(cpu.r.A);
      break;
    }
  }

  cpu.PC = next;
  instructionCount++;
  if (refresh) updateDisplay();
  return !cpu.halted;
}

function getSampleIntervalMs() {
  const value = Number($("sampleInterval").value);
  return Number.isFinite(value) && value > 0 ? value : 1;
}

function getVisibleWindowSamples() {
  const timePerDiv = Number($("timeBase").value) || 50;
  return Math.max(2, Math.ceil((timePerDiv * 10) / getSampleIntervalMs()));
}

function findRisingCrossings(data, level) {
  const crossings = [];
  for (let i = 1; i < data.length; i++) {
    if (data[i - 1].y < level && data[i].y >= level) crossings.push(data[i].index);
  }
  return crossings;
}

function chooseScaleAtLeast(options, target) {
  return options.find(value => value >= target) ?? options[options.length - 1];
}

function autoSetDso() {
  if (!samples.length) {
    showMessage("No DAC samples available. Run a waveform first, then press Auto Set.", "info");
    return;
  }

  const values = samples.map(s => s.y);
  const min = Math.min(...values);
  const max = Math.max(...values);
  const span = Math.max(max - min, 0.01);
  const center = (max + min) / 2;
  const voltsDiv = chooseScaleAtLeast(VOLTS_PER_DIV, span / 6.5);
  $("voltsPerDiv").value = String(voltsDiv);
  $("verticalOffset").value = center.toFixed(2);
  $("triggerLevel").value = center.toFixed(2);

  const crossings = findRisingCrossings(samples, center);
  let periodSamples = 0;
  if (crossings.length >= 2) {
    const gaps = [];
    for (let i = 1; i < crossings.length; i++) gaps.push(crossings[i] - crossings[i - 1]);
    periodSamples = gaps.reduce((sum, gap) => sum + gap, 0) / gaps.length;
  } else {
    periodSamples = Math.max(samples.length, 20);
  }

  const desiredTimePerDiv = (periodSamples * getSampleIntervalMs() * 2) / 10;
  const timeDiv = chooseScaleAtLeast(TIME_BASES, desiredTimePerDiv);
  $("timeBase").value = String(timeDiv);
  renderDso();
  showMessage(`DSO Auto Set complete: ${voltsDiv} V/div, ${timeDiv} ms/div.`, "success");
}

function getCurrentDisplayWindow() {
  if (!samples.length) return [];

  const interval = getSampleIntervalMs();
  const windowSamples = getVisibleWindowSamples();
  const trigger = Number($("triggerLevel").value);
  const level = Number.isFinite(trigger) ? trigger : 0;
  const crossings = findRisingCrossings(samples, level);
  const firstIndex = samples[0].index;
  const lastIndex = samples[samples.length - 1].index;

  let startIndex;
  const eligible = crossings.filter(index => index + windowSamples - 1 <= lastIndex);
  if (eligible.length) {
    startIndex = eligible[eligible.length - 1];
  } else if (crossings.length) {
    startIndex = crossings[0];
  } else {
    startIndex = Math.max(firstIndex, lastIndex - windowSamples + 1);
  }

  return samples.filter(s => s.index >= startIndex && s.index < startIndex + windowSamples);
}

function updateMeasurements(data) {
  const ids = ["maxVoltage", "minVoltage", "peakToPeak", "averageVoltage", "rmsVoltage", "frequencyValue", "periodValue", "dutyCycle"];
  if (!data || data.length === 0) {
    ids.forEach(id => { if ($(id)) $(id).textContent = "--"; });
    $("measurementState").textContent = "Waiting for signal";
    return;
  }

  const values = data.map(sample => sample.y);
  const max = Math.max(...values);
  const min = Math.min(...values);
  const avg = values.reduce((sum, value) => sum + value, 0) / values.length;
  const rms = Math.sqrt(values.reduce((sum, value) => sum + value * value, 0) / values.length);
  const threshold = (max + min) / 2;
  const crossings = findRisingCrossings(data, threshold);
  const interval = getSampleIntervalMs();
  let periodMs = null;
  let frequencyHz = null;

  if (crossings.length >= 2) {
    const gaps = [];
    for (let i = 1; i < crossings.length; i++) gaps.push(crossings[i] - crossings[i - 1]);
    const averageGap = gaps.reduce((sum, gap) => sum + gap, 0) / gaps.length;
    periodMs = averageGap * interval;
    if (periodMs > 0) frequencyHz = 1000 / periodMs;
  }

  const highCount = values.filter(value => value >= threshold).length;
  const duty = (highCount / values.length) * 100;

  $("maxVoltage").textContent = `${max.toFixed(3)} V`;
  $("minVoltage").textContent = `${min.toFixed(3)} V`;
  $("peakToPeak").textContent = `${(max - min).toFixed(3)} V`;
  $("averageVoltage").textContent = `${avg.toFixed(3)} V`;
  $("rmsVoltage").textContent = `${rms.toFixed(3)} V`;
  $("frequencyValue").textContent = frequencyHz === null ? "--" : `${frequencyHz.toFixed(2)} Hz`;
  $("periodValue").textContent = periodMs === null ? "--" : `${periodMs.toFixed(2)} ms`;
  $("dutyCycle").textContent = `${duty.toFixed(1)} %`;
  $("measurementState").textContent = `${data.length} screen samples`;
}

function renderDso() {
  if (!chart || dsoFrozen) return;
  if (!samples.length) {
    chart.data.datasets[0].data = [];
    chart.data.datasets[1].data = [];
    chart.update("none");
    lastVisibleSamples = [];
    updateMeasurements([]);
    return;
  }

  const visible = getCurrentDisplayWindow();
  lastVisibleSamples = visible;
  const interval = getSampleIntervalMs();
  const startIndex = visible.length ? visible[0].index : samples[samples.length - 1].index;
  const chartPoints = visible.map(s => ({ x: (s.index - startIndex) * interval, y: s.y }));
  const timePerDiv = Number($("timeBase").value) || 50;
  const voltsPerDiv = Number($("voltsPerDiv").value) || 1;
  const verticalOffset = Number($("verticalOffset").value) || 0;
  const triggerLevel = Number($("triggerLevel").value) || 0;
  const totalTime = timePerDiv * 10;

  chart.data.datasets[0].data = chartPoints;
  chart.data.datasets[1].data = [{ x: 0, y: triggerLevel }, { x: totalTime, y: triggerLevel }];
  chart.options.scales.x.min = 0;
  chart.options.scales.x.max = totalTime;
  chart.options.scales.y.min = verticalOffset - (4 * voltsPerDiv);
  chart.options.scales.y.max = verticalOffset + (4 * voltsPerDiv);
  chart.update("none");

  $("scopeScaleReadout").textContent = `${voltsPerDiv} V/div · ${timePerDiv} ms/div`;
  $("triggerReadout").textContent = `Rising edge · ${triggerLevel.toFixed(2)} V`;
  $("sampleSummary").textContent = `Latest DAC input: ${hex(samples[samples.length - 1].raw)} (${samples[samples.length - 1].raw}) → ${samples[samples.length - 1].y.toFixed(3)} V · ${totalSamples.toLocaleString()} samples acquired`;
  updateMeasurements(visible);
}

function addSample(value) {
  const ref = parseFloat($("referenceVoltage").value);
  if (!Number.isFinite(ref) || ref <= 0) throw new Error("Reference voltage must be greater than zero.");

  const voltage = (value / 255) * ref;
  samples.push({ index: nextSampleIndex++, y: voltage, raw: value });
  totalSamples++;
  if (samples.length > MAX_STORED_SAMPLES) samples.shift();

  $("sampleCount").textContent = totalSamples.toLocaleString();

  if (autoSetPending && samples.length >= 1200) {
    autoSetPending = false;
    autoSetDso();
  } else if (!running || totalSamples % RENDER_EVERY_N_SAMPLES === 0) {
    renderDso();
  }
}

function updateDisplay() {
  const names = ["A", "B", "C", "D", "E", "H", "L"];
  $("registerGrid").innerHTML = names.map(n => `<div class="register"><span>${n}</span><strong>${hex(cpu.r[n])}</strong></div>`).join("") +
    `<div class="register"><span>SP</span><strong>${hex(cpu.SP, 4)}</strong></div>`;
  $("flagsRow").innerHTML = Object.entries(cpu.f).map(([k, v]) => `<span class="flag ${v ? "on" : ""}">${k}: ${v}</span>`).join("");
  $("instructionCount").textContent = instructionCount.toLocaleString();
  $("pcValue").textContent = hex(cpu.PC, 4);
  $("currentInstruction").textContent = lastInstruction;
  $("statusPill").textContent = cpu.halted ? "Halted" : running ? "Running" : "Ready";
}

function showMessage(message, type = "info") {
  const el = $("messageBox");
  el.className = `message-box ${type}`;
  el.textContent = message;
}

function clearDsoSamples() {
  samples = [];
  totalSamples = 0;
  nextSampleIndex = 0;
  lastVisibleSamples = [];
  $("sampleCount").textContent = "0";
  $("sampleSummary").textContent = "No DAC samples yet. Run a program to acquire a waveform.";
  // Clear the trace even when the DSO display is currently frozen.
  if (chart) {
    chart.data.datasets[0].data = [];
    chart.data.datasets[1].data = [];
    chart.update("none");
  }
  updateMeasurements([]);
}

function resetSimulation(clearGraph = true) {
  stopRun();
  const start = parseNumber($("startAddress").value);
  if (start > 65535) throw new Error("Start address must be between 0000H and FFFFH.");
  cpu = makeCPU(start);
  instructionCount = 0;
  lastInstruction = "Not started";
  autoSetPending = false;
  dsoFrozen = false;
  $("freezeBtn").textContent = "Freeze";
  if (clearGraph) clearDsoSamples();
  updateDisplay();
}

function assembleCurrent() {
  const start = parseNumber($("startAddress").value);
  const result = assemble($("assemblyCode").value, start);
  program = result.instructions;
  labels = result.labels;
  assembledSnapshot = [$("assemblyCode").value, $("startAddress").value, $("dacPort").value, $("referenceVoltage").value].join("|");
  if (!program.length) throw new Error("The editor is empty.");

  $("listingBody").innerHTML = program.map(i => `<tr><td>${hex(i.address, 4)}</td><td>${escapeHTML(i.source)}</td><td>${i.size}</td></tr>`).join("");
  resetSimulation(true);
  showMessage(`Assembly successful: ${program.length} instruction lines, starting at ${hex(start, 4)}.`, "success");
}

function escapeHTML(s) {
  return s.replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
}

function currentSnapshot() {
  return [$("assemblyCode").value, $("startAddress").value, $("dacPort").value, $("referenceVoltage").value].join("|");
}

function ensureAssembled() {
  if (!program.length || currentSnapshot() !== assembledSnapshot) assembleCurrent();
}

function runProgram() {
  try {
    if (running) return;
    ensureAssembled();
    if (cpu.halted) resetSimulation(true);
    running = true;
    autoSetPending = samples.length === 0;
    updateDisplay();
    showMessage("Executing program and acquiring DAC samples…", "info");

    let total = 0;
    const batch = () => {
      if (!running) return;
      try {
        let n = 0;
        while (n < 500 && total < 100000 && !cpu.halted && running) {
          executeOne(false);
          n++;
          total++;
        }
        updateDisplay();
        if (cpu.halted) {
          stopRun();
          renderDso();
          showMessage("Program halted successfully.", "success");
        } else if (total >= 100000) {
          stopRun();
          autoSetPending = false;
          renderDso();
          showMessage("Execution limit reached (100,000 instructions). Samples collected so far are displayed.", "info");
        } else {
          timer = setTimeout(batch, 0);
        }
      } catch (e) {
        stopRun();
        autoSetPending = false;
        renderDso();
        showMessage(e.message, "error");
      }
    };
    batch();
  } catch (e) {
    showMessage(e.message, "error");
  }
}

function stopRun() {
  running = false;
  if (timer) clearTimeout(timer);
  timer = null;
  if (cpu) updateDisplay();
}

function stepProgram() {
  try {
    ensureAssembled();
    if (cpu.halted) {
      showMessage("The processor is halted. Press Reset before stepping again.", "info");
      return;
    }
    executeOne(true);
    showMessage(cpu.halted ? "HLT executed. Processor halted." : "Executed one instruction.", "success");
  } catch (e) {
    showMessage(e.message, "error");
  }
}

function initChart() {
  const ctx = $("waveChart").getContext("2d");
  chart = new Chart(ctx, {
    type: "line",
    data: {
      datasets: [
        {
          label: "CH1 · DAC output",
          data: [],
          borderColor: "#30d6a0",
          backgroundColor: "rgba(48,214,160,.08)",
          borderWidth: 2,
          pointRadius: 0,
          pointHoverRadius: 3,
          tension: 0,
          stepped: "after",
          fill: false
        },
        {
          label: "Trigger level",
          data: [],
          borderColor: "rgba(255,190,80,.9)",
          borderWidth: 1,
          borderDash: [6, 5],
          pointRadius: 0,
          tension: 0,
          fill: false
        }
      ]
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      animation: false,
      parsing: false,
      normalized: true,
      interaction: { intersect: false, mode: "nearest" },
      scales: {
        x: {
          type: "linear",
          min: 0,
          max: 500,
          title: { display: true, text: "Time (ms)", color: "#9fb0c8" },
          ticks: { color: "#9fb0c8", maxTicksLimit: 11 },
          grid: { color: "rgba(150,170,200,.16)" }
        },
        y: {
          min: -1.5,
          max: 6.5,
          title: { display: true, text: "Voltage (V)", color: "#9fb0c8" },
          ticks: { color: "#9fb0c8" },
          grid: { color: "rgba(150,170,200,.16)" }
        }
      },
      plugins: {
        legend: { display: false },
        tooltip: {
          callbacks: {
            label: context => ` ${context.parsed.y.toFixed(3)} V`
          }
        }
      }
    }
  });
}

function loadSelectedExample() {
  const key = $("exampleSelect").value;
  $("assemblyCode").value = examples[key] || examples.triangle;
  try {
    assembleCurrent();
    showMessage(`${$("exampleSelect").selectedOptions[0].text} example loaded and assembled. Press Run to view it on the DSO.`, "success");
  } catch (e) {
    showMessage(e.message, "error");
  }
}

$("loadExampleBtn").addEventListener("click", loadSelectedExample);
$("runBtn").addEventListener("click", runProgram);
$("stepBtn").addEventListener("click", stepProgram);
$("stopBtn").addEventListener("click", () => {
  stopRun();
  autoSetPending = false;
  renderDso();
  showMessage("Execution stopped by user. Acquired samples remain on the DSO.", "info");
});
$("resetBtn").addEventListener("click", () => {
  try {
    if (!program.length) assembleCurrent();
    else {
      resetSimulation(true);
      showMessage("Processor and DSO acquisition reset.", "success");
    }
  } catch (e) {
    showMessage(e.message, "error");
  }
});
$("clearGraphBtn").addEventListener("click", () => {
  clearDsoSamples();
  showMessage("DSO trace and measurements cleared.", "info");
});
$("autoSetBtn").addEventListener("click", autoSetDso);
$("freezeBtn").addEventListener("click", () => {
  dsoFrozen = !dsoFrozen;
  $("freezeBtn").textContent = dsoFrozen ? "Resume" : "Freeze";
  if (!dsoFrozen) renderDso();
  showMessage(dsoFrozen ? "DSO display frozen. Processor execution can continue." : "DSO display resumed.", "info");
});

["timeBase", "voltsPerDiv", "sampleInterval", "triggerLevel", "verticalOffset"].forEach(id => {
  $(id).addEventListener("change", renderDso);
});

initChart();
try {
  $("assemblyCode").value = examples.triangle;
  assembleCurrent();
} catch (e) {
  showMessage(e.message, "error");
}

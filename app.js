function divisorsOfSquare(a) {
  const square = a * a;
  const divisors = [];
  for (let h = 1; h <= Math.sqrt(square); h += 1) {
    if (square % h === 0) {
      divisors.push(h);
      if (h * h !== square) divisors.push(square / h);
    }
  }
  return divisors.sort((x, y) => x - y);
}

function initDivisorFan() {
  const svg = document.querySelector("#divisor-fan");
  const slider = document.querySelector("#a-slider");
  if (!svg || !slider) return;

  const namespace = "http://www.w3.org/2000/svg";
  let selected = 1;

  function make(name, attributes = {}) {
    const node = document.createElementNS(namespace, name);
    Object.entries(attributes).forEach(([key, value]) => node.setAttribute(key, value));
    return node;
  }

  function render() {
    const a = Number(slider.value);
    const q = 4 * a - 1;
    const divisors = divisorsOfSquare(a);
    if (!divisors.includes(selected)) selected = divisors[0];

    const rect = svg.getBoundingClientRect();
    const width = Math.max(rect.width, 420);
    const height = Math.max(rect.height, 340);
    const centerX = width / 2;
    const centerY = height / 2;
    const radius = Math.min(width, height) * 0.36;
    svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
    svg.replaceChildren();

    svg.append(make("circle", {
      cx: centerX,
      cy: centerY,
      r: radius,
      fill: "none",
      stroke: "#dedede",
      "stroke-width": "1",
    }));

    divisors.forEach((h, index) => {
      const angle = -Math.PI * 0.88 + (index / Math.max(divisors.length - 1, 1)) * Math.PI * 1.76;
      const x = centerX + Math.cos(angle) * radius;
      const y = centerY + Math.sin(angle) * radius;
      const boundary = h === 1 || h === a || h === a * a;
      const active = h === selected;

      svg.append(make("line", {
        x1: centerX,
        y1: centerY,
        x2: x,
        y2: y,
        stroke: active ? "#126dcc" : boundary ? "#6d6d6d" : "#b9cfe6",
        "stroke-width": active ? "2.5" : boundary ? "1.5" : "1",
      }));

      const group = make("g", { tabindex: "0", role: "button", "aria-label": `Select h equals ${h}` });
      group.style.cursor = "pointer";
      group.append(make("circle", {
        cx: x,
        cy: y,
        r: active ? "8" : boundary ? "6" : "5",
        fill: active ? "#126dcc" : boundary ? "#555" : "#7ca9d7",
        stroke: "#fff",
        "stroke-width": "2",
      }));
      const label = make("text", {
        x: x + (Math.cos(angle) >= 0 ? 11 : -11),
        y: y + 4,
        fill: active ? "#126dcc" : "#666",
        "font-family": "DM Mono, monospace",
        "font-size": active ? "11" : "9",
        "text-anchor": Math.cos(angle) >= 0 ? "start" : "end",
      });
      label.textContent = String(h);
      group.append(label);
      const choose = () => {
        selected = h;
        render();
      };
      group.addEventListener("click", choose);
      group.addEventListener("keydown", (event) => {
        if (event.key === "Enter" || event.key === " ") choose();
      });
      svg.append(group);
    });

    svg.append(make("circle", {
      cx: centerX,
      cy: centerY,
      r: "38",
      fill: "#fff",
      stroke: "#126dcc",
      "stroke-width": "1.5",
    }));
    const core = make("text", {
      x: centerX,
      y: centerY + 6,
      fill: "#2d2d2d",
      "font-family": "Inter, sans-serif",
      "font-size": "24",
      "font-weight": "500",
      "text-anchor": "middle",
    });
    core.textContent = `a=${a}`;
    svg.append(core);

    document.querySelector("#a-output").textContent = a;
    document.querySelector("#q-output").textContent = q;
    document.querySelector("#divisor-count").textContent = `${divisors.length} divisors`;
    document.querySelector("#h-output").textContent = selected;
    document.querySelector("#fan-congruence").textContent = `n ≡ ${(q - ((4 * selected) % q)) % q} (mod ${q})`;
  }

  slider.addEventListener("input", () => {
    selected = 1;
    render();
  });
  window.addEventListener("resize", render);
  render();
}

function formatInteger(value) {
  return value.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ",");
}

function initCertificateExplorer() {
  const nInput = document.querySelector("#n-input");
  const aInput = document.querySelector("#cert-a-input");
  const eInput = document.querySelector("#e-input");
  const status = document.querySelector("#certificate-status");
  const equation = document.querySelector("#certificate-equation");
  const details = document.querySelector("#certificate-details");
  const nextButton = document.querySelector("#next-example");
  if (!nInput || !aInput || !eInput || !status || !equation || !details) return;

  const examples = [[11, 4, 1], [3, 2, 1], [7, 6, 4], [15, 8, 4], [42, 11, 11], [30, 12, 16], [58, 20, 25]];
  let exampleIndex = 0;

  function fraction(numerator, denominator) {
    return `<span class="fraction"><b>${numerator}</b><i>${formatInteger(denominator)}</i></span>`;
  }

  function render() {
    let n;
    let a;
    let e;
    try {
      n = BigInt(nInput.value || "0");
      a = BigInt(aInput.value || "0");
      e = BigInt(eInput.value || "0");
    } catch {
      status.className = "certificate-status invalid";
      status.textContent = "Enter whole numbers only.";
      equation.innerHTML = "";
      details.innerHTML = "";
      return;
    }

    if (n < 1n || a < 1n || e < 1n) {
      status.className = "certificate-status invalid";
      status.textContent = "All three values must be positive integers.";
      equation.innerHTML = "";
      details.innerHTML = "";
      return;
    }

    const square = a * a;
    const q = 4n * a - 1n;
    const divides = square % e === 0n;
    const congruent = (n + 4n * e) % q === 0n;
    if (!divides || !congruent) {
      const residue = (q - ((4n * e) % q)) % q;
      const problems = [];
      if (!divides) problems.push(`e must divide a² = ${formatInteger(square)}`);
      if (!congruent) problems.push(`n must be congruent to ${residue} modulo ${q}`);
      status.className = "certificate-status invalid";
      status.textContent = `${problems.join("; ")}.`;
      equation.innerHTML = "";
      details.innerHTML = "";
      return;
    }

    const A = a * n;
    const x = A;
    const y = (A + e) / q;
    const z = (A + (A * A) / e) / q;
    status.className = "certificate-status";
    status.textContent = "Valid divisor-fan certificate.";
    equation.innerHTML = `${fraction(4n, n)}<strong>=</strong>${fraction(1n, x)}<strong>+</strong>${fraction(1n, y)}<strong>+</strong>${fraction(1n, z)}`;
    details.innerHTML = [
      ["q = 4a − 1", q],
      ["A = an", A],
      ["e divides a²", `${e} ∣ ${square}`],
      ["congruence", `${n} ≡ −4·${e} mod ${q}`],
    ].map(([label, value]) => `<div class="detail-item"><span>${label}</span><strong>${typeof value === "bigint" ? formatInteger(value) : value}</strong></div>`).join("");
  }

  [nInput, aInput, eInput].forEach((input) => input.addEventListener("input", render));
  nextButton?.addEventListener("click", () => {
    exampleIndex = (exampleIndex + 1) % examples.length;
    const [n, a, e] = examples[exampleIndex];
    nInput.value = n;
    aInput.value = a;
    eInput.value = e;
    render();
  });
  render();
}

function initCopyBibtex() {
  const button = document.querySelector("#copy-bibtex");
  const bibtex = document.querySelector("#bibtex code");
  if (!button || !bibtex) return;
  button.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(bibtex.textContent);
      button.querySelector("span").textContent = "Copied";
      setTimeout(() => { button.querySelector("span").textContent = "Copy"; }, 1800);
    } catch {
      button.querySelector("span").textContent = "Select text to copy";
    }
  });
}

window.addEventListener("DOMContentLoaded", () => {
  if (window.lucide) window.lucide.createIcons();
  initDivisorFan();
  initCertificateExplorer();
  initCopyBibtex();
});

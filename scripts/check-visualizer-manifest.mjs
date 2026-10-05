import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const leanRoot = fileURLToPath(new URL("..", import.meta.url));
const manifestPath = path.join(leanRoot, "docs", "visualizer", "manifest.json");
const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
const objects = manifest.objects ?? [];

if (objects.length === 0) {
  console.error("visualizer manifest has no objects");
  process.exit(1);
}

const issues = [];
const ids = new Set();
const modules = new Set();
const declarations = new Set();

for (const [index, item] of objects.entries()) {
  const label = `objects[${index}]`;
  if (typeof item.id !== "string" || item.id.length === 0) {
    issues.push(`${label} has no nonempty id`);
  } else if (ids.has(item.id)) {
    issues.push(`duplicate visualizer object id: ${item.id}`);
  } else {
    ids.add(item.id);
  }

  if (typeof item.module !== "string" || !/^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(item.module)) {
    issues.push(`${label} has an invalid Lean module name`);
    continue;
  }
  modules.add(item.module);

  if (typeof item.source !== "string") {
    issues.push(`${label} has no source path`);
  } else {
    const expectedSource = `${item.module.replaceAll(".", "/")}.lean`;
    if (item.source !== expectedSource) {
      issues.push(`${label} source must be ${expectedSource}, got ${item.source}`);
    }
    const resolvedSource = path.resolve(leanRoot, item.source);
    const relativeSource = path.relative(leanRoot, resolvedSource);
    if (relativeSource.startsWith("..") || path.isAbsolute(relativeSource)) {
      issues.push(`${label} source escapes the Lean project: ${item.source}`);
    } else if (!fs.statSync(resolvedSource, { throwIfNoEntry: false })?.isFile()) {
      issues.push(`${label} source does not exist: ${item.source}`);
    }
  }

  if (typeof item.leanName !== "string" || item.leanName.length === 0) {
    issues.push(`${label} has no Lean declaration name`);
  } else {
    declarations.add(item.leanName);
  }

  if (!Array.isArray(item.dependencies) || item.dependencies.some((dependency) => typeof dependency !== "string" || dependency.length === 0)) {
    issues.push(`${label} dependencies must be an array of Lean declaration names`);
  } else {
    for (const dependency of item.dependencies) declarations.add(dependency);
  }
}

if (issues.length > 0) {
  console.error(issues.join("\n"));
  process.exit(1);
}

const checks = [...declarations].map((name) => `#check ${name}`).join("\n");
const source = [...[...modules].map((moduleName) => `import ${moduleName}`), "set_option pp.universes false", checks, ""].join("\n");
const tempPath = path.join(os.tmpdir(), `branchingprocess-visualizer-${process.pid}.lean`);
fs.writeFileSync(tempPath, source, "utf8");

try {
  const result = spawnSync("lake", ["env", "lean", tempPath], {
    cwd: leanRoot,
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"]
  });
  if (result.error) {
    console.error(`could not run Lean: ${result.error.message}`);
    process.exit(1);
  }
  if (result.status !== 0) {
    process.stderr.write(result.stdout || "");
    process.stderr.write(result.stderr || "");
    process.exit(result.status || 1);
  }
  console.log(`Validated ${objects.length} visualizer objects, ${modules.size} modules, and ${declarations.size} Lean declarations.`);
} finally {
  fs.rmSync(tempPath, { force: true });
}

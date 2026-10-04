import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

const leanRoot = path.resolve(new URL("..", import.meta.url).pathname);
const manifestPath = path.join(leanRoot, "docs", "visualizer", "manifest.json");
const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
const objects = manifest.objects ?? [];

if (objects.length === 0) {
  console.error("visualizer manifest has no objects");
  process.exit(1);
}

const modules = [...new Set(objects.map((item) => item.module).filter(Boolean))];
const checks = objects.map((item) => `#check ${item.leanName}`).join("\n");
const source = [...modules.map((moduleName) => `import ${moduleName}`), "set_option pp.universes false", checks, ""].join("\n");
const tempPath = path.join(os.tmpdir(), `branchingprocess-visualizer-${process.pid}.lean`);
fs.writeFileSync(tempPath, source, "utf8");

try {
  const result = spawnSync("lake", ["env", "lean", tempPath], {
    cwd: leanRoot,
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"]
  });
  if (result.status !== 0) {
    process.stderr.write(result.stdout || "");
    process.stderr.write(result.stderr || "");
    process.exit(result.status || 1);
  }
  console.log(`Lean checked ${objects.length} visualizer declarations:`);
  console.log(objects.map((item) => item.leanName).join(", "));
} finally {
  fs.rmSync(tempPath, { force: true });
}

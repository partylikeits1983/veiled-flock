import { cpSync, existsSync, mkdirSync, readdirSync, rmSync, statSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const scriptDir = dirname(fileURLToPath(import.meta.url));
const frontendRoot = resolve(scriptDir, "..");
const repoRoot = resolve(frontendRoot, "..");
const sourceRoot = resolve(repoRoot, "lean");
const destinationRoot = resolve(frontendRoot, "public", "lean");

if (!existsSync(sourceRoot)) {
  throw new Error(`Lean source directory not found: ${sourceRoot}`);
}

rmSync(destinationRoot, { recursive: true, force: true });
mkdirSync(destinationRoot, { recursive: true });

function copyLeanFiles(dir, relativeDir = "") {
  let copied = 0;

  for (const entry of readdirSync(dir)) {
    const sourcePath = join(dir, entry);
    const relativePath = join(relativeDir, entry);
    const stat = statSync(sourcePath);

    if (stat.isDirectory()) {
      if (entry === ".lake") continue;
      copied += copyLeanFiles(sourcePath, relativePath);
      continue;
    }

    if (!entry.endsWith(".lean")) continue;

    const targetPath = join(destinationRoot, relativePath);
    mkdirSync(dirname(targetPath), { recursive: true });
    cpSync(sourcePath, targetPath);
    copied += 1;
  }

  return copied;
}

const count = copyLeanFiles(sourceRoot);
console.log(`Copied ${count} Lean files to frontend/public/lean`);

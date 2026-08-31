const fileCache = new Map<string, string[]>();
const basePath = process.env.NEXT_PUBLIC_BASE_PATH ?? "";

export async function fetchLeanFile(path: string): Promise<string[]> {
  const cached = fileCache.get(path);
  if (cached) return cached;

  const response = await fetch(`${basePath}/lean/${path}`);
  if (!response.ok) {
    throw new Error(`${response.status} ${response.statusText}`);
  }

  const lines = (await response.text()).split("\n");
  fileCache.set(path, lines);
  return lines;
}

export function extractByTag(lines: string[], tag: string): string | null {
  const startMarker = `-- @audit:${tag}`;
  const endMarker = "-- @audit:end";
  const startIndex = lines.findIndex((line) => line.trim() === startMarker);

  if (startIndex === -1) return null;

  const endIndex = lines.findIndex((line, index) => index > startIndex && line.trim() === endMarker);
  return lines.slice(startIndex + 1, endIndex === -1 ? lines.length : endIndex).join("\n");
}

export function findTagLine(lines: string[], tag: string): number {
  const marker = `-- @audit:${tag}`;
  const index = lines.findIndex((line) => line.trim() === marker);
  return index === -1 ? 1 : index + 2;
}

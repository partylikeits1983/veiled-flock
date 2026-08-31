# FLOCK+VEIL Website

This is a static Next.js audit-document skeleton for the FLOCK+VEIL Lean proof
artifacts.

```sh
npm install
npm run dev
```

The build copies `../lean/**/*.lean` into `public/lean/` so the source panel can
load tagged declarations.

```sh
npm run check
GITHUB_PAGES=true npm run build
```

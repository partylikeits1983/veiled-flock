const isGithubPages = process.env.GITHUB_PAGES === "true";
const repoBasePath = "/veiled-flock";

/** @type {import('next').NextConfig} */
const nextConfig = {
  output: "export",
  trailingSlash: true,
  agentRules: false,
  basePath: isGithubPages ? repoBasePath : undefined,
  assetPrefix: isGithubPages ? `${repoBasePath}/` : undefined,
  env: {
    NEXT_PUBLIC_BASE_PATH: isGithubPages ? repoBasePath : "",
  },
  images: {
    unoptimized: true,
  },
};

export default nextConfig;

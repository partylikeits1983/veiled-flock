"use client";

import { ArrowLeft, ExternalLink, LoaderCircle, X } from "lucide-react";
import { useEffect, useMemo, useState } from "react";
import { BRANCH, REPO_URL, type LeanRef } from "../lib/audit-data";
import { extractByTag, fetchLeanFile, findTagLine } from "../lib/lean-files";

type LeanPanelProps = {
  selected: LeanRef | null;
  historyLength: number;
  onBack: () => void;
  onClose: () => void;
};

type SourceState =
  | { status: "idle"; code: null; line: null; error: null }
  | { status: "loading"; code: null; line: null; error: null }
  | { status: "ready"; code: string; line: number; error: null }
  | { status: "error"; code: null; line: null; error: string };

export default function LeanPanel({ selected, historyLength, onBack, onClose }: LeanPanelProps) {
  const [source, setSource] = useState<SourceState>({
    status: "idle",
    code: null,
    line: null,
    error: null,
  });

  const githubHref = useMemo(() => {
    if (!selected || source.status !== "ready") return null;
    return `${REPO_URL}/blob/${BRANCH}/lean/${selected.file}#L${source.line}`;
  }, [selected, source]);

  useEffect(() => {
    if (!selected) {
      setSource({ status: "idle", code: null, line: null, error: null });
      return;
    }

    let alive = true;
    setSource({ status: "loading", code: null, line: null, error: null });

    fetchLeanFile(selected.file)
      .then((lines) => {
        if (!alive) return;
        const code = extractByTag(lines, selected.tag);
        if (code === null) {
          setSource({
            status: "error",
            code: null,
            line: null,
            error: `Missing audit tag ${selected.tag}`,
          });
          return;
        }
        setSource({
          status: "ready",
          code,
          line: findTagLine(lines, selected.tag),
          error: null,
        });
      })
      .catch((error: unknown) => {
        if (!alive) return;
        setSource({
          status: "error",
          code: null,
          line: null,
          error: error instanceof Error ? error.message : "Failed to load Lean source",
        });
      });

    return () => {
      alive = false;
    };
  }, [selected]);

  return (
    <aside className={`leanPanel ${selected ? "open" : ""}`} aria-label="Lean source">
      <div className="panelHeader">
        <div className="panelTitle">
          <span>Lean Source</span>
          {selected ? <code>{selected.label}</code> : null}
        </div>
        <div className="panelActions">
          <button
            type="button"
            className="iconButton"
            onClick={onBack}
            disabled={historyLength === 0}
            title="Back"
            aria-label="Back"
          >
            <ArrowLeft aria-hidden="true" size={17} />
          </button>
          {githubHref ? (
            <a className="iconButton" href={githubHref} title="GitHub" aria-label="GitHub">
              <ExternalLink aria-hidden="true" size={17} />
            </a>
          ) : null}
          <button type="button" className="iconButton" onClick={onClose} title="Close" aria-label="Close">
            <X aria-hidden="true" size={17} />
          </button>
        </div>
      </div>

      <div className="panelBody">
        {source.status === "loading" ? (
          <div className="panelState">
            <LoaderCircle aria-hidden="true" className="spin" size={18} />
            Loading Lean source
          </div>
        ) : null}
        {source.status === "error" ? <div className="panelError">{source.error}</div> : null}
        {source.status === "ready" ? (
          <pre>
            <code>{source.code}</code>
          </pre>
        ) : null}
      </div>
    </aside>
  );
}

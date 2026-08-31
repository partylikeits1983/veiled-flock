"use client";

import {
  BookOpen,
  ExternalLink,
  FileText,
  GitBranch,
  Landmark,
  Scale,
  ShieldCheck,
} from "lucide-react";
import { useCallback, useMemo, useState } from "react";
import AuditCard from "./components/audit-card";
import LeanPanel from "./components/lean-panel";
import ProofMap from "./components/proof-map";
import { auditSections, resourceLinks, statusRows, type LeanRef } from "./lib/audit-data";

const resourceIcons = {
  spec: FileText,
  architecture: Landmark,
  security: ShieldCheck,
  lean: BookOpen,
};

export default function Home() {
  const [selected, setSelected] = useState<LeanRef | null>(null);
  const [history, setHistory] = useState<LeanRef[]>([]);

  const selectedKey = useMemo(() => (selected ? `${selected.file}:${selected.tag}` : null), [selected]);

  const openLean = useCallback(
    (ref: LeanRef) => {
      const nextKey = `${ref.file}:${ref.tag}`;
      if (selectedKey === nextKey) {
        setSelected(null);
        setHistory([]);
        return;
      }

      if (selected) {
        setHistory((current) => [...current, selected]);
      }
      setSelected(ref);
    },
    [selected, selectedKey],
  );

  const closePanel = useCallback(() => {
    setSelected(null);
    setHistory([]);
  }, []);

  const goBack = useCallback(() => {
    const previous = history[history.length - 1];
    if (!previous) return;
    setSelected(previous);
    setHistory((current) => current.slice(0, -1));
  }, [history]);

  return (
    <div className={`workspace ${selected ? "withPanel" : ""}`}>
      <main className="paper">
        <header className="masthead">
          <div className="identityLine">
            <span className="mark">F+V</span>
            <span>Lean proof audit skeleton</span>
          </div>
          <div className="mastheadGrid">
            <div>
              <h1>FLOCK+VEIL</h1>
              <p className="lead">
                A hosted audit document for the Lean proof artifacts behind the FLOCK+VEIL
                zero-knowledge construction.
              </p>
              <div className="repoLinkRow">
                <a href="https://github.com/partylikeits1983/veiled-flock">
                  <GitBranch aria-hidden="true" size={18} />
                  Repository
                  <ExternalLink aria-hidden="true" size={15} />
                </a>
                <a href="https://veil.succinct.xyz/">
                  <Scale aria-hidden="true" size={18} />
                  Reference Site
                  <ExternalLink aria-hidden="true" size={15} />
                </a>
              </div>
            </div>
            <ProofMap />
          </div>
        </header>

        <section className="statusBand" aria-labelledby="status-title">
          <div>
            <p className="eyebrow">Status</p>
            <h2 id="status-title">Formal Verification Boundary</h2>
          </div>
          <div className="statusRows">
            {statusRows.map((row) => (
              <div className="statusRow" key={row.label}>
                <span>{row.label}</span>
                <p>{row.value}</p>
              </div>
            ))}
          </div>
        </section>

        <nav className="resourceStrip" aria-label="Project resources">
          {resourceLinks.map((resource) => {
            const Icon = resourceIcons[resource.id as keyof typeof resourceIcons];
            return (
              <a href={resource.href} key={resource.id}>
                <Icon aria-hidden="true" size={18} />
                <span>{resource.label}</span>
                <ExternalLink aria-hidden="true" size={14} />
              </a>
            );
          })}
        </nav>

        <nav className="toc" aria-label="Audit sections">
          {auditSections.map((section) => (
            <a href={`#${section.id}`} key={section.id}>
              <span>{section.eyebrow}</span>
              {section.title}
            </a>
          ))}
        </nav>

        {auditSections.map((section) => (
          <section className="auditSection" id={section.id} key={section.id}>
            <p className="eyebrow">{section.eyebrow}</p>
            <h2>{section.title}</h2>
            <p className="sectionIntro">{section.intro}</p>
            <div className="cardGrid">
              {section.cards.map((card) => (
                <AuditCard
                  active={Boolean(card.lean && selectedKey === `${card.lean.file}:${card.lean.tag}`)}
                  card={card}
                  key={card.id}
                  onOpenLean={openLean}
                />
              ))}
            </div>
          </section>
        ))}
      </main>

      <LeanPanel selected={selected} historyLength={history.length} onBack={goBack} onClose={closePanel} />
    </div>
  );
}

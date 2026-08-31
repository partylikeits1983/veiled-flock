"use client";

import { CheckCircle2, CircleDashed, Code2, FileWarning, Sigma } from "lucide-react";
import type { AuditCardData, CardKind, LeanRef } from "../lib/audit-data";

const kindLabel: Record<CardKind, string> = {
  boundary: "Boundary",
  definition: "Definition",
  theorem: "Theorem",
  lemma: "Lemma",
  planned: "Planned",
};

const kindIcon = {
  boundary: FileWarning,
  definition: Sigma,
  theorem: CheckCircle2,
  lemma: Sigma,
  planned: CircleDashed,
};

type AuditCardProps = {
  card: AuditCardData;
  active: boolean;
  onOpenLean: (ref: LeanRef) => void;
};

export default function AuditCard({ card, active, onOpenLean }: AuditCardProps) {
  const Icon = kindIcon[card.kind];

  return (
    <article className={`auditCard auditCard-${card.kind}`}>
      <div className="cardMeta">
        <span className="cardType">
          <Icon aria-hidden="true" size={15} />
          {kindLabel[card.kind]}
        </span>
      </div>
      <h3>{card.title}</h3>
      <p>{card.body}</p>
      {card.detail ? <p className="cardDetail">{card.detail}</p> : null}
      {card.lean ? (
        <button
          type="button"
          className={`leanLink ${active ? "active" : ""}`}
          onClick={() => onOpenLean(card.lean as LeanRef)}
          title={card.lean.label}
          aria-label={card.lean.label}
        >
          <Code2 aria-hidden="true" size={15} />
          <span>{card.lean.label}</span>
        </button>
      ) : null}
    </article>
  );
}

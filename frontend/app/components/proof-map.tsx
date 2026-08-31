import { Braces, Database, GitBranch, ShieldCheck } from "lucide-react";

const layers = [
  {
    label: "Pinned relation",
    detail: "BLAKE3 batch statement",
    icon: Database,
  },
  {
    label: "FLOCK transcript",
    detail: "Affine masked views",
    icon: GitBranch,
  },
  {
    label: "VEIL layer",
    detail: "Shifted verifier constraints",
    icon: ShieldCheck,
  },
  {
    label: "Lean library",
    detail: "Masking and bounds",
    icon: Braces,
  },
];

export default function ProofMap() {
  return (
    <div className="proofMap" aria-label="FLOCK plus VEIL proof map">
      <div className="proofRail" aria-hidden="true" />
      {layers.map((layer, index) => {
        const Icon = layer.icon;
        return (
          <div className="proofLayer" key={layer.label}>
            <span className="layerIndex">{String(index + 1).padStart(2, "0")}</span>
            <span className="layerIcon">
              <Icon aria-hidden="true" size={18} />
            </span>
            <span>
              <strong>{layer.label}</strong>
              <small>{layer.detail}</small>
            </span>
          </div>
        );
      })}
    </div>
  );
}

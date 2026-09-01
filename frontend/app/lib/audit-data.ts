export const REPO_URL = "https://github.com/partylikeits1983/veiled-flock";
export const BRANCH = "main";

export type CardKind = "boundary" | "definition" | "theorem" | "lemma" | "planned";

export type LeanRef = {
  file: string;
  tag: string;
  label: string;
};

export type AuditCardData = {
  id: string;
  kind: CardKind;
  title: string;
  body: string;
  detail?: string;
  lean?: LeanRef;
};

export type AuditSectionData = {
  id: string;
  eyebrow: string;
  title: string;
  intro: string;
  cards: AuditCardData[];
};

export const resourceLinks = [
  {
    id: "spec",
    label: "Specification",
    href: `${REPO_URL}/blob/${BRANCH}/SPEC.md`,
  },
  {
    id: "architecture",
    label: "Architecture",
    href: `${REPO_URL}/blob/${BRANCH}/docs/ARCHITECTURE.md`,
  },
  {
    id: "security",
    label: "Security Scope",
    href: `${REPO_URL}/blob/${BRANCH}/docs/SECURITY.md`,
  },
  {
    id: "lean",
    label: "Lean Proofs",
    href: `${REPO_URL}/blob/${BRANCH}/lean/README.md`,
  },
];

export const statusRows = [
  {
    label: "Current proof layer",
    value: "Generic masking, mixture, bad-set, conditional replacement, and probability lemmas.",
  },
  {
    label: "Current boundary",
    value: "The active Rust protocol and Rust-to-Lean correspondence are not mechanized here yet.",
  },
  {
    label: "Verification path",
    value: "make formal-proof builds Flockzk and audits exported theorem axioms.",
  },
];

export const auditSections: AuditSectionData[] = [
  {
    id: "relation",
    eyebrow: "Protocol Target",
    title: "Pinned FLOCK+VEIL Statement",
    intro:
      "The public statement is an ordered batch of BLAKE3 digests. The witness contains one 64-byte message per digest, padded to the registered circuit shapes before Fiat-Shamir challenge derivation.",
    cards: [
      {
        id: "relation-boundary",
        kind: "boundary",
        title: "Relation and Scope Boundary",
        body:
          "The intended public claim is one ordered digest per 64-byte BLAKE3 preimage, with shape, padding, and transcript binding governed by the normative specification. This skeleton does not claim completed correspondence.",
        detail: "Source: SPEC.md sections 1 and 11; docs/SECURITY.md target properties.",
      },
      {
        id: "protocol-model-planned",
        kind: "planned",
        title: "Production Protocol Model",
        body:
          "Reserved for formal protocol-model cards covering the active succinct VEIL composition and its Rust entry points.",
      },
    ],
  },
  {
    id: "masking",
    eyebrow: "Lean Core",
    title: "Affine Masking",
    intro:
      "The base proof layer shows that affine transcript distributions are witness-independent when witness differences are covered by the mask image.",
    cards: [
      {
        id: "transcript-witness-indep",
        kind: "theorem",
        title: "Transcript Witness Independence",
        body:
          "For witnesses with equal public inputs, every transcript value has the same number of mask assignments under both witnesses.",
        detail: "This is the basic one-time-pad style masking theorem used by later composition arguments.",
        lean: {
          file: "Flockzk/Masking.lean",
          tag: "FlockZk.transcript_witness_indep",
          label: "FlockZk.transcript_witness_indep",
        },
      },
      {
        id: "simulator-exact",
        kind: "theorem",
        title: "Exact Simulator Distribution",
        body:
          "A simulator using a public coset representative produces the same affine transcript distribution as the honest prover.",
        lean: {
          file: "Flockzk/Masking.lean",
          tag: "FlockZk.simulator_exact",
          label: "FlockZk.simulator_exact",
        },
      },
    ],
  },
  {
    id: "triangular",
    eyebrow: "Composition",
    title: "Triangular Masking",
    intro:
      "The triangular theorem models a two-stage masking repair where residual directions are handled in a quotient by an outer mask stage.",
    cards: [
      {
        id: "triangular-witness-indep",
        kind: "theorem",
        title: "Triangular Witness Independence",
        body:
          "Under constant inner image, affine quotient offsets, and residual coverage, the joint transcript distribution is independent of the witness.",
        lean: {
          file: "Flockzk/MaskingTriangular.lean",
          tag: "FlockZk.triangular_witness_indep",
          label: "FlockZk.triangular_witness_indep",
        },
      },
      {
        id: "triangular-simulator-exact",
        kind: "theorem",
        title: "Triangular Simulator",
        body:
          "Running the honest prover on a public representative reproduces the masked transcript distribution without the private witness.",
        lean: {
          file: "Flockzk/MaskingTriangular.lean",
          tag: "FlockZk.triangular_simulator_exact",
          label: "FlockZk.triangular_simulator_exact",
        },
      },
    ],
  },
  {
    id: "bad-set",
    eyebrow: "Statistical Bounds",
    title: "Bad-Set and Replacement Bounds",
    intro:
      "The bad-set layer isolates rank-deficient choices and composes that algebraic loss with a separate boundary term.",
    cards: [
      {
        id: "mixture-bad-set",
        kind: "lemma",
        title: "Mixture Bad-Set Distance",
        body:
          "The normalized distance between two joint transcript distributions is bounded by twice the bad-set mass in L1 form.",
        lean: {
          file: "Flockzk/MaskingMixtureBadSet.lean",
          tag: "FlockZk.mixture_statistical_distance_bad_set",
          label: "FlockZk.mixture_statistical_distance_bad_set",
        },
      },
      {
        id: "conditional-replacement",
        kind: "theorem",
        title: "Conditional Replacement",
        body:
          "Once the algebraic prefix and commitment/hash boundary are bounded independently, their total variation costs add.",
        lean: {
          file: "Flockzk/ConditionalReplacement.lean",
          tag: "FlockZk.conditional_replacement_tv_bound",
          label: "FlockZk.conditional_replacement_tv_bound",
        },
      },
    ],
  },
  {
    id: "probability",
    eyebrow: "Probability Supplier",
    title: "Schwartz-Zippel Budget",
    intro:
      "The symbolic rank argument consumes a generic finite-field polynomial bound supplied by Lean.",
    cards: [
      {
        id: "schwartz-zippel",
        kind: "lemma",
        title: "Degree Budget Bound",
        body:
          "A nonzero polynomial with emitted per-variable degree bounds vanishes on at most the corresponding Schwartz-Zippel budget.",
        lean: {
          file: "Flockzk/SchwartzZippelBound.lean",
          tag: "FlockZk.schwartz_zippel_degree_budget",
          label: "FlockZk.schwartz_zippel_degree_budget",
        },
      },
      {
        id: "ledger-planned",
        kind: "planned",
        title: "Ledger Integration",
        body:
          "Reserved for generated Rust certificate artifacts, pROM ledger links, and correspondence notes.",
      },
    ],
  },
];

# Decision log

## D001 — Integration repository, not an immediate FLOCK fork

Keep the experiment separate and use a pinned local FLOCK dependency. This makes
baseline comparisons straightforward and prevents experimental proof formats from
being mistaken for upstream FLOCK. If invasive verifier refactoring becomes
necessary, maintain a narrow patch queue and record it here.

## D002 — `F128` is the VEIL protocol field

FLOCK's algebraic transcript already uses `F128`. Using it directly avoids a
128-fold exposed-message expansion. The concrete two-adic VEIL implementation is
therefore reference material rather than a reusable backend.

## D003 — First relation is fixed-digest BLAKE3-64 × 256

This matches the requested batch-hash privacy goal and reuses relation-binding
ideas from the old `zk-flock` branch. Hash chains remain a later profile.

## D004 — Secure/UDR before Fast/Johnson-OOD

The first protocol-aligned implementation uses the simpler, conservative profile.
Fast mode is enabled only after its proximity/binding behavior is captured in the
compiler assumptions and simulator.

## D005 — Terminal and ring-switch values are exposed initially

Mask and constrain the final Ligerito residual and ring-switch partial evaluations
through VEIL's intermediate compiler. An extra recursive commitment does not remove
the existence of a terminal residual.

## D006 — Interactive theorem target before Fiat-Shamir

Build and test the statement-only simulator for the public-coin protocol first.
Fiat-Shamir gets a separate proof format, simulator, and security label.


import VeiledFlock.ProductionSamplingScheduleBlindControlFreshness

/-! # Small opaque transport lemmas for dependent control executions -/

namespace VeiledFlock.ProductionSamplingControlTransport

open VeiledFlock.AdaptiveOracleProgramming
open VeiledFlock.ConcreteOracle
open VeiledFlock.ConcreteParameters
open VeiledFlock.ProductionSamplingSchedule
open VeiledFlock.ProductionSamplingScheduleSemantics

theorem iterateFrom_length_bound_transport
    {shape : BatchShape} (step : ℕ → Control shape → OracleBlock → Control shape)
    (start rounds increment : ℕ) (answers : Fin rounds → OracleBlock)
    (actual expected base : Control shape)
    (hactual : actual = expected)
    (hexpected : expected.transcript.length = base.transcript.length)
    (hbound : base.transcript.length + increment ≤
      (iterateFrom step start rounds expected answers).transcript.length) :
    actual.transcript.length + increment ≤
      (iterateFrom step start rounds actual answers).transcript.length := by
  subst actual
  simpa only [hexpected] using hbound

theorem length_bound_transport
    {shape : BatchShape} (before withState startControl endControl : Control shape)
    (increment : ℕ)
    (hwith : withState.transcript.length = before.transcript.length)
    (hstart : startControl.transcript.length = withState.transcript.length)
    (hsegment : startControl.transcript.length + increment ≤
      endControl.transcript.length) :
    before.transcript.length + increment ≤ endControl.transcript.length := by
  omega

end VeiledFlock.ProductionSamplingControlTransport

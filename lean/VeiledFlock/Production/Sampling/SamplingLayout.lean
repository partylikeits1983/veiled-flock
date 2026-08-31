import VeiledFlock.Concrete.ConcreteParameters
import VeiledFlock.Concrete.Grinding

/-!
# Fixed layout for all bounded production sampling queries

Every fail-closed loop reserves its complete public cap.  Coordinates after
an early success are private inactive coordinates; the following stage begins
at a fixed offset.  This makes each local abort event a fixed projection of
one uniform finite answer tape.
-/

namespace VeiledFlock.ProductionSamplingLayout

open VeiledFlock.ChallengeSampling
open VeiledFlock.ConcreteParameters
open VeiledFlock.Grinding

def equalitySkipBlocks : ℕ := 3
def equalityAttemptBlocks : ℕ := 7

def equalityOffset : ℕ := equalitySkipBlocks
def equalityWidth : ℕ := rejectionTrials * equalityAttemptBlocks

def zerocheckOffset : ℕ := equalityOffset + equalityWidth
def zerocheckWidth : ℕ := maxProgrammedPoints

def blindStateOffset : ℕ := zerocheckOffset + zerocheckWidth
def blindStateWidth : ℕ := 1
def blindGrindingOffset : ℕ := blindStateOffset + blindStateWidth
def blindGrindingWidth : ℕ := maxBlindTrials

def blindChallengeOffset : ℕ := blindGrindingOffset + blindGrindingWidth
def multiplicationAlphaOffset : ℕ := blindChallengeOffset + rejectionTrials
def outerChallengeOffset : ℕ := multiplicationAlphaOffset + rejectionTrials
def outerPositionsOffset : ℕ := outerChallengeOffset + rejectionTrials
def linearPositionsOffset : ℕ := outerPositionsOffset + rejectionTrials
def linearRhoOffset : ℕ := linearPositionsOffset + rejectionTrials
def hadamardPositionsOffset : ℕ := linearRhoOffset + rejectionTrials
def hadamardRhoOffset : ℕ := hadamardPositionsOffset + rejectionTrials
def productCoefficientOffset : ℕ := hadamardRhoOffset + rejectionTrials

def ligeritoOffset : ℕ := productCoefficientOffset + rejectionTrials
def ligeritoSiteWidth : ℕ := 1 + maxLigeritoTrials
def ligeritoWidth : ℕ := maxLigeritoSites * ligeritoSiteWidth

/-- Public number of optional answer slots used by the complete equality,
zerocheck, rejection, position, and grinding schedule. -/
def productionSamplingSlots : ℕ := ligeritoOffset + ligeritoWidth

theorem productionSamplingSlots_eq : productionSamplingSlots = 135209 := by
  decide

theorem productionSamplingSlots_le_protocol_cap :
    productionSamplingSlots ≤ maxProtocolOracleQueriesPerProof := by
  decide

/-- Maximum growth of the live Fiat--Shamir transcript after zerocheck.  PoW
failures do not grow the transcript; only a successful nonce is absorbed. -/
def productionTailTranscriptGrowth : ℕ :=
  17 +
    (maxNonzeroChallengeSites + maxNotZeroOrOneChallengeSites + 3) *
      rejectionTrials * 18 +
    maxLigeritoSites * 17

theorem productionTailTranscriptGrowth_eq :
    productionTailTranscriptGrowth = 663841 := by
  decide

/-- Sufficient slack between the actual pre-zerocheck public bound and the
`maxStartLength` parameter for every later Fiat--Shamir query to remain in
the unique finite oracle table. -/
def FullSamplingFits (preZerocheckBound maxStartLength : ℕ) : Prop :=
  preZerocheckBound + productionTailTranscriptGrowth + 10 ≤
    maxStartLength + 8

end VeiledFlock.ProductionSamplingLayout

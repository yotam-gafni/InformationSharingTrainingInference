import Mathlib

/-!
# General signaling-model interfaces

A deliberately finite, distribution-first interface for the model in Section 2 of
*Information-Sharing in Training and Inference*.  The correlation model is defined in a
separate file.  Keeping the two layers separate leaves room for a later derivation of the
correlation model from richer world models and training signals.
-/

namespace TrainSharing

/-- The four information-sharing contracts in the paper. -/
inductive Contract where
  | noSharing
  | trainSharing
  | inferSharing
  | fullSharing
  deriving DecidableEq, Fintype, Repr

/-- Whether a contract reveals the other firm's training signal. -/
def Contract.sharesTraining : Contract → Bool
  | .trainSharing | .fullSharing => true
  | .noSharing | .inferSharing => false

/-- Whether a contract reveals the other firm's inference-time signal. -/
def Contract.sharesInference : Contract → Bool
  | .inferSharing | .fullSharing => true
  | .noSharing | .trainSharing => false

@[simp] theorem Contract.fullSharing_sharesTraining :
    Contract.fullSharing.sharesTraining = true := by rfl

@[simp] theorem Contract.fullSharing_sharesInference :
    Contract.fullSharing.sharesInference = true := by rfl

/-- A finite probability law, represented explicitly by its mass function. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-- A Section 2 world model: a prior on labels and, conditional on a label, a joint law
of the two firms' binary inference signals.  This distributional presentation is equivalent
to the paper's measurable partitions for finite signal spaces, but is easier to extend and use. -/
structure BinaryWorldModel where
  label : FiniteLaw Bool
  signals : Bool → FiniteLaw (Bool × Bool)

/-- The four nonnegative utility parameters from Section 2. -/
structure UtilityParameters where
  reward0 : ℝ
  reward1 : ℝ
  cost0 : ℝ
  cost1 : ℝ
  reward0_nonneg : 0 ≤ reward0
  reward1_nonneg : 0 ≤ reward1
  cost0_nonneg : 0 ≤ cost0
  cost1_nonneg : 0 ≤ cost1

/-- Significant-action utilities impose zero reward and cost on action `false`. -/
def UtilityParameters.IsSignificantAction (u : UtilityParameters) : Prop :=
  u.reward0 = 0 ∧ u.cost0 = 0

/-- Symmetric significant-action utilities additionally have equal reward and cost for
significant action `true`. -/
def UtilityParameters.IsSymmetricSignificantAction (u : UtilityParameters) : Prop :=
  u.IsSignificantAction ∧ u.reward1 = u.cost1

end TrainSharing

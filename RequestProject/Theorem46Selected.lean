import RequestProject.Theorem43Selected

/-!
# Theorem 4.6 under a fixed equilibrium selection

This file gives Theorem 4.6 the same “apples-to-apples” treatment as
`Theorem43Selected.lean`: the IRPO comparison, payoffs, and consumer trade events all refer
to one fixed equilibrium selection.

There is an important asymmetry between Theorems 4.3 and 4.6.  Under no sharing the chosen
strategy is fixed before the correlation world is revealed, so literal unique IRPO rules
out the single inactive profile and immediately gives the half-trade bound.  Under train
sharing the selected strategy may vary with the revealed world.  Literal uniqueness rules
out being inactive in *every* world, but does not by itself imply activity in every world.
The latter statement, and the no-sharing transfer used in part (1), are therefore recorded
explicitly as the two equilibrium-classification consequences proved by the manuscript's
case analysis.
-/

namespace TrainSharing.Theorem46.Selected

open TrainSharing
open TrainSharing.Theorem43
open TrainSharing.Theorem46

/-- One selected equilibrium for each contract when train sharing may condition its action
rules on the revealed correlation world.  The utility vector is ex ante, while `event`
records the selected equilibrium's world-dependent consumer trade event. -/
structure EquilibriumSelection (W : Type) where
  utility : Contract → Firm → ℝ
  event : Contract → W → Bool × Bool → Bool
  trainFirm1 : W → Bool → Bool
  trainFirm2 : W → Bool → Bool
  noFirm1 : Bool → Bool
  noFirm2 : Bool → Bool
  equilibrium_nonnegative : ∀ c i, 0 ≤ utility c i
  train_event : event .trainSharing =
    fun w => TrainSharing.Theorem43.tradeEvent (trainFirm1 w) (trainFirm2 w)
  no_event : event .noSharing =
    fun _ => TrainSharing.Theorem43.tradeEvent noFirm1 noFirm2
  inactive_train_utility :
    WorldwiseTrivialProfile trainFirm1 trainFirm2 →
      utility .trainSharing .firm1 = 0 ∧ utility .trainSharing .firm2 = 0

/-- **Definition 4.5 (inverted equilibrium).**  A world-dependent train-sharing
equilibrium is *inverted* when, for some correlation world, the secondary firm takes the
significant action if and only if it sees the weak inference signal, i.e. its strategy is
`a → 0, b → 1`. -/
def Inverted {W : Type} (trainFirm2 : W → Bool → Bool) : Prop :=
  ∃ w, trainFirm2 w true = false ∧ trainFirm2 w false = true

/-- The negation of `Inverted`, in the pointwise form used by the theorems: whenever the
secondary firm acts after its negative inference signal, it also acts after its positive
one. -/
def NonInverted {W : Type} (trainFirm2 : W → Bool → Bool) : Prop :=
  ∀ w, trainFirm2 w false = true → trainFirm2 w true = true

/-- The two formulations of Definition 4.5 agree. -/
theorem nonInverted_iff_not_inverted {W : Type} (trainFirm2 : W → Bool → Bool) :
    NonInverted trainFirm2 ↔ ¬ Inverted trainFirm2 := by
  constructor
  · rintro h ⟨w, hpos, hneg⟩
    rw [h w hneg] at hpos
    exact Bool.noConfusion hpos
  · intro h w hneg
    by_contra hpos
    exact h ⟨w, by simpa using hpos, hneg⟩

/-- Pareto dominance at the selected equilibria. -/
def ParetoDominates {W : Type} (S : EquilibriumSelection W) (c d : Contract) : Prop :=
  ∀ i, S.utility d i ≤ S.utility c i

/-- Strict Pareto dominance at the selected equilibria. -/
def StrictlyParetoDominates {W : Type} (S : EquilibriumSelection W)
    (c d : Contract) : Prop :=
  ParetoDominates S c d ∧ ¬ ParetoDominates S d c

/-- Selected-equilibrium IRPO, with no sharing as the outside option. -/
def IsIRPO {W : Type} (S : EquilibriumSelection W) (c : Contract) : Prop :=
  (c = .noSharing ∨ ParetoDominates S c .noSharing) ∧
    ∀ d, ¬ StrictlyParetoDominates S d c

/-- Literal, rather than modulo-equivalence, uniqueness at the selected equilibria. -/
def IsUniquelyIRPO {W : Type} (S : EquilibriumSelection W) (c : Contract) : Prop :=
  IsIRPO S c ∧ ∀ d, IsIRPO S d → d = c

private theorem pareto_trans {W : Type} (S : EquilibriumSelection W) (a b c : Contract)
    (hab : ParetoDominates S a b) (hbc : ParetoDominates S b c) :
    ParetoDominates S a c := by
  intro i
  exact le_trans (hbc i) (hab i)

/-- A literally unique selected train-sharing contract cannot have payoff vector `(0,0)`.
This is the train-sharing analogue of
`Theorem43.Selected.unique_noSharing_payoff_not_both_zero`. -/
theorem unique_trainSharing_payoff_not_both_zero {W : Type}
    (S : EquilibriumSelection W) (hunique : IsUniquelyIRPO S .trainSharing) :
    ¬ (S.utility .trainSharing .firm1 = 0 ∧
       S.utility .trainSharing .firm2 = 0) := by
  intro hzero
  have hno_train : ParetoDominates S .noSharing .trainSharing := by
    intro i
    fin_cases i
    · simpa [hzero.1] using S.equilibrium_nonnegative .noSharing .firm1
    · simpa [hzero.2] using S.equilibrium_nonnegative .noSharing .firm2
  have hnoPO : ∀ d, ¬ StrictlyParetoDominates S d .noSharing := by
    intro d hd
    apply hunique.1.2 d
    refine ⟨pareto_trans S d .noSharing .trainSharing hd.1 hno_train, ?_⟩
    intro htrain_d
    exact hd.2 (pareto_trans S .noSharing .trainSharing d hno_train htrain_d)
  have hnoIRPO : IsIRPO S .noSharing := ⟨Or.inl rfl, hnoPO⟩
  have heq := hunique.2 .noSharing hnoIRPO
  exact Contract.noConfusion heq

/-- Literal unique IRPO therefore excludes a train-sharing selection that is inactive in
every correlation world.  Notice that this conclusion is existential: it does not claim
activity separately in every world. -/
theorem unique_trainSharing_forces_some_activity {W : Type}
    (S : EquilibriumSelection W) (hunique : IsUniquelyIRPO S .trainSharing) :
    ¬ WorldwiseTrivialProfile S.trainFirm1 S.trainFirm2 := by
  intro htrivial
  exact unique_trainSharing_payoff_not_both_zero S hunique
    (S.inactive_train_utility htrivial)

/-- The two model-specific conclusions supplied by the manuscript's equilibrium case
analysis.  `noSharingTransfer` is part (1)'s event inclusion.  `trainNontrivial` is the
worldwise activity statement used by the upper-bound paragraph of part (2). -/
structure ManuscriptEquilibriumConsequences {W : Type}
    (S : EquilibriumSelection W) : Prop where
  noSharingTransfer : ∀ w q, S.event .trainSharing w q = true →
    S.event .noSharing w q = true
  trainNontrivial : ∀ w, NontrivialProfile (S.trainFirm1 w) (S.trainFirm2 w)

/-- **Theorem 4.6, apples-to-apples finite-distribution form.**

For a fixed selected equilibrium of every contract, literal unique IRPO excludes the
all-inactive train-sharing selection.  Given the two equilibrium-classification facts in
`ManuscriptEquilibriumConsequences`, the selected no-sharing equilibrium is weakly better
for the normalized opportunity-seeking consumer, and every selected rival contract has
at most twice the train-sharing trade probability.

Unlike the no-sharing result in `Theorem43Selected.lean`, worldwise nontriviality cannot be
recovered merely from ex-ante literal uniqueness: train sharing observes the world and may
use a different strategy there. -/
theorem theorem4_6_fixed_selection {W : Type} [Fintype W]
    (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (S : EquilibriumSelection W)
    (hunique : IsUniquelyIRPO S .trainSharing)
    (hmodel : ManuscriptEquilibriumConsequences S) :
    (¬ WorldwiseTrivialProfile S.trainFirm1 S.trainFirm2) ∧
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (S.event .trainSharing) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (S.event .noSharing) ∧
    ∀ c : Contract,
      correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event c) ≤
        2 * correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event .trainSharing) := by
  refine ⟨unique_trainSharing_forces_some_activity S hunique, ?_, ?_⟩
  · rw [S.train_event, S.no_event]
    exact correlationTradeProbability_transfer prior _ S.trainFirm1 S.trainFirm2
      S.noFirm1 S.noFirm2 (by
        intro w q hq
        have ht : S.event .trainSharing w q = true := by
          rw [S.train_event]
          exact hq
        have hn := hmodel.noSharingTransfer w q ht
        rw [S.no_event] at hn
        exact hn)
  · intro c
    rw [S.train_event]
    have hhalf : (1 / 2 : ℝ) ≤ correlationTradeProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        S.trainFirm1 S.trainFirm2 := by
      apply correlationTradeProbability_half
      · intro w
        exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).1
      · intro w
        exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.1
      · intro w
        exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.2.1
      · intro w
        exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.2.2
      · exact hmodel.trainNontrivial
    have hone := correlationEventProbability_le_one prior
      (fun w => parameterInferenceLaw (parameters w) (feasible w)) (S.event c)
    change correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w)) (S.event c) ≤
      2 * correlationTradeProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        S.trainFirm1 S.trainFirm2
    linarith

end TrainSharing.Theorem46.Selected

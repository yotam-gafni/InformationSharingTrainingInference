import RequestProject.Theorem46

/-!
# Theorem 4.3 under a fixed equilibrium selection

This file formalizes the “apples-to-apples” reading in which every contract is evaluated
at one selected equilibrium.  Literal uniqueness is correspondingly applied to those
selected equilibrium payoff vectors, rather than to an unrelated strategy profile.
-/

namespace TrainSharing.Theorem43.Selected

open TrainSharing.Correlation.Known
open TrainSharing.Theorem43

/-- One selected equilibrium for every contract, retaining exactly the data needed for
Theorem 4.3: both firms' payoffs, the induced trade event, and the no-sharing strategies.
The two semantic fields record standard equilibrium consequences under significant-action
utilities: either firm can guarantee zero by always taking the benign action, and an
inactive no-sharing profile gives both firms payoff zero. -/
structure EquilibriumSelection where
  utility : Contract → Firm → ℝ
  event : Contract → Bool × Bool → Bool
  noFirm1 : Bool → Bool
  noFirm2 : Bool → Bool
  equilibrium_nonnegative : ∀ c i, 0 ≤ utility c i
  no_event : event .noSharing = tradeEvent noFirm1 noFirm2
  inactive_no_utility :
    (∀ x, noFirm1 x = false) → (∀ y, noFirm2 y = false) →
      utility .noSharing .firm1 = 0 ∧ utility .noSharing .firm2 = 0

/-- Pareto comparison of two contracts at their selected equilibria. -/
def ParetoDominates (S : EquilibriumSelection) (c d : Contract) : Prop :=
  ∀ i, S.utility d i ≤ S.utility c i

/-- Selected-equilibrium Pareto dominance is transitive. -/
theorem paretoDominates_trans (S : EquilibriumSelection) (a b c : Contract)
    (hab : ParetoDominates S a b) (hbc : ParetoDominates S b c) :
    ParetoDominates S a c := by
  intro i
  exact le_trans (hbc i) (hab i)

/-- Strict Pareto comparison at the selected equilibria. -/
def StrictlyParetoDominates (S : EquilibriumSelection) (c d : Contract) : Prop :=
  ParetoDominates S c d ∧ ¬ ParetoDominates S d c

/-- IRPO at the selected equilibria, with no sharing as the outside option. -/
def IsIRPO (S : EquilibriumSelection) (c : Contract) : Prop :=
  (c = .noSharing ∨ ParetoDominates S c .noSharing) ∧
    ∀ d, ¬ StrictlyParetoDominates S d c

/-- Literal (not modulo equivalence) unique IRPO for the selected equilibria. -/
def IsUniquelyIRPO (S : EquilibriumSelection) (c : Contract) : Prop :=
  IsIRPO S c ∧ ∀ d, IsIRPO S d → d = c

/-- Under literal selected-equilibrium uniqueness, the selected no-sharing payoff vector
cannot be `(0,0)`: every selected equilibrium gives both firms at least their zero outside
option, so any distinct contract would then be another IRPO representative (or would
strictly dominate no sharing). -/
theorem unique_noSharing_payoff_not_both_zero
    (S : EquilibriumSelection) (hunique : IsUniquelyIRPO S .noSharing) :
    ¬ (S.utility .noSharing .firm1 = 0 ∧ S.utility .noSharing .firm2 = 0) := by
  intro hzero
  have hnoPO := hunique.1.2
  have htrain_no : ParetoDominates S .trainSharing .noSharing := by
    intro i
    fin_cases i
    · simpa [hzero.1] using S.equilibrium_nonnegative .trainSharing .firm1
    · simpa [hzero.2] using S.equilibrium_nonnegative .trainSharing .firm2
  have htrainPO : ∀ d, ¬ StrictlyParetoDominates S d .trainSharing := by
    intro d hd
    apply hnoPO d
    refine ⟨paretoDominates_trans S d .trainSharing .noSharing hd.1 htrain_no, ?_⟩
    intro hno_d
    exact hd.2 (paretoDominates_trans S .trainSharing .noSharing d htrain_no hno_d)
  have htrainIRPO : IsIRPO S .trainSharing :=
    ⟨Or.inr htrain_no, htrainPO⟩
  have heq := hunique.2 .trainSharing htrainIRPO
  exact Contract.noConfusion heq

/-- The selected no-sharing equilibrium is therefore nontrivial.  This is exactly the
step that removes the extra `NontrivialProfile` hypothesis under the user's literal,
selected-equilibrium interpretation. -/
theorem unique_noSharing_forces_nontrivial
    (S : EquilibriumSelection) (hunique : IsUniquelyIRPO S .noSharing) :
    NontrivialProfile S.noFirm1 S.noFirm2 := by
  by_contra htrivial
  apply unique_noSharing_payoff_not_both_zero S hunique
  apply S.inactive_no_utility
  · intro x
    by_contra hx
    have htrue : S.noFirm1 x = true := by
      cases h : S.noFirm1 x <;> simp_all
    exact htrivial (Or.inl ⟨x, htrue⟩)
  · intro y
    by_contra hy
    have htrue : S.noFirm2 y = true := by
      cases h : S.noFirm2 y <;> simp_all
    exact htrivial (Or.inr ⟨y, htrue⟩)

/-- **Theorem 4.3(2), apples-to-apples form.**  For a feasible correlation world and a
fixed equilibrium selection, if no sharing is literally the unique IRPO contract, then
every other selected contract equilibrium has trade probability at most twice that of
the selected no-sharing equilibrium.  There is no separate nontriviality, half-trade, or
event-level assumption. -/
theorem theorem4_3_factor_two_no_extra_strategic_hypotheses
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible)
    (S : EquilibriumSelection) (hunique : IsUniquelyIRPO S .noSharing)
    (c : Contract) :
    preferredProbability (parameterInferenceLaw p hp) (S.event c) ≤
      2 * preferredProbability (parameterInferenceLaw p hp) (S.event .noSharing) := by
  rw [S.no_event]
  exact theorem4_3_factor_two_from_correlation_model p hp S.noFirm1 S.noFirm2
    (unique_noSharing_forces_nontrivial S hunique) (S.event c)

/-- **Theorem 4.3(2), finite-distribution form.**  The same conclusion holds for an
arbitrary finite distribution over feasible correlation worlds.  The no-sharing strategy
is fixed before the correlation is revealed, exactly as required by the no-sharing
contract; the rival selected equilibrium may be evaluated world by world through its
selected event. -/
theorem theorem4_3_factor_two_finite_correlation_distribution
    {W : Type} [Fintype W]
    (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (S : EquilibriumSelection) (hunique : IsUniquelyIRPO S .noSharing)
    (c : Contract) :
    TrainSharing.Theorem46.correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => S.event c) ≤
      2 * TrainSharing.Theorem46.correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => S.event .noSharing) := by
  let law : W → FiniteLaw (Bool × Bool) :=
    fun w => parameterInferenceLaw (parameters w) (feasible w)
  have hhalf : (1 / 2 : ℝ) ≤
      TrainSharing.Theorem46.correlationTradeProbability prior law
        (fun _ => S.noFirm1) (fun _ => S.noFirm2) := by
    apply TrainSharing.Theorem46.correlationTradeProbability_half
    · intro w
      exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).1
    · intro w
      exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.1
    · intro w
      exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.2.1
    · intro w
      exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.2.2
    · intro w
      exact unique_noSharing_forces_nontrivial S hunique
  have hrival := TrainSharing.Theorem46.correlationEventProbability_le_one prior law
    (fun _ => S.event c)
  have hrewrite :
      TrainSharing.Theorem46.correlationEventProbability prior law
          (fun _ => S.event .noSharing) =
        TrainSharing.Theorem46.correlationTradeProbability prior law
          (fun _ => S.noFirm1) (fun _ => S.noFirm2) := by
    unfold TrainSharing.Theorem46.correlationEventProbability
      TrainSharing.Theorem46.correlationTradeProbability
    simp_rw [S.no_event]
  change TrainSharing.Theorem46.correlationEventProbability prior law
      (fun _ => S.event c) ≤
    2 * TrainSharing.Theorem46.correlationEventProbability prior law
      (fun _ => S.event .noSharing)
  rw [hrewrite]
  linarith

end TrainSharing.Theorem43.Selected

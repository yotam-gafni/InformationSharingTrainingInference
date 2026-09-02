import RequestProject.UnknownCorrelation

/-!
# Theorem 3.6, parts (1) and (2)

This file states the economic content of the first two clauses of Theorem 3.6 in the
contract order of `BayesianGame.lean`.  Unlike the earlier generic order lemmas, the
hypotheses below name the comparisons proved in the paper: train/no equivalence and the
failure of full sharing to be individually rational in part (1), and full sharing's
comparison with each of the other three contracts in part (2).

Because contracts are represented as four distinct constructors, the manuscript's “unique
IRPO, up to equivalence” conclusion is represented by uniqueness modulo
`ContractEquivalent`, together with an exact characterization of the no/train-sharing
representatives.
-/

namespace TrainSharing

variable {World Train1 Train2 : Type}
  [Fintype World] [Fintype Train1] [Fintype Train2]

/-- Pareto dominance is transitive whenever its two premises provide the required
model equilibria.  This is proved directly from the quantified interim-utility
definition, rather than assumed as an abstract order law. -/
theorem paretoDominates_trans
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (a b c : Contract)
    (hab : ParetoDominates E u a b) (hbc : ParetoDominates E u b c) :
    ParetoDominates E u a c := by
  intro z hz
  obtain ⟨sa, haNash, ha⟩ := hab z hz
  obtain ⟨sb, hbNash, hb⟩ := hbc z hz
  refine ⟨sa, haNash, ?_⟩
  intro sc hcNash
  have hab' := ha sb hbNash
  have hbc' := hb sc hcNash
  exact ⟨le_trans hbc'.1 hab'.1, le_trans hbc'.2 hab'.2⟩

/-- Pareto optimality transfers across mutually dominating representatives. -/
theorem paretoOptimal_of_equivalent
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (a b : Contract) (heq : ContractEquivalent E u a b)
    (hb : IsParetoOptimal E u b) : IsParetoOptimal E u a := by
  intro d hd
  apply hb d
  exact ⟨paretoDominates_trans E u d a b hd.1 heq.1,
    fun hback => hd.2 (paretoDominates_trans E u a b d heq.1 hback)⟩

/-- Economic comparisons used in Theorem 3.6(1), after imposing `R₁ = C₁`.

* train sharing and no sharing are equivalent (Lemma B.2);
* full sharing strictly dominates infer sharing (Lemma 3.5, away from equality);
* full sharing is not individually rational relative to no sharing;
* the equivalent no/train representatives are Pareto optimal.

Infer sharing is then excluded by the preceding strict dominance, rather than by a
separate assumption.
-/
def Theorem36Part1Conditions
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) : Prop :=
  ContractEquivalent E u .trainSharing .noSharing ∧
  StrictlyParetoDominates E u .fullSharing .inferSharing ∧
  ¬ ParetoDominates E u .fullSharing .noSharing ∧
  IsParetoOptimal E u .noSharing

/-- Actual contract characterization for Theorem 3.6(1): under the paper's economic
comparisons, precisely no sharing and its train-sharing equivalent are IRPO. -/
theorem theorem3_6_part1_irpo_characterization
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part1Conditions E u) (c : Contract) :
    IsIRPO E u c ↔ c = .noSharing ∨ c = .trainSharing := by
  rcases h with ⟨hequiv, hstrict, hfullnot, hnoPO⟩
  have htrainPO : IsParetoOptimal E u .trainSharing := by
    intro d hd
    apply hnoPO d
    exact ⟨paretoDominates_trans E u d .trainSharing .noSharing hd.1 hequiv.1,
      fun hback => hd.2 (paretoDominates_trans E u .trainSharing .noSharing d hequiv.1 hback)⟩
  constructor
  · -- If IsIRPO E u c, then c = noSharing ∨ c = trainSharing
    intro hIRPO
    rcases hIRPO with ⟨hIR, hPO⟩
    have hind : IsIndividuallyRational E u c := hIR
    rcases hind with rfl | hPardom
    · exact Or.inl rfl
    · rcases c with (_ | _ | _ | _)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hPO .fullSharing hstrict)
      · exact absurd hPardom hfullnot
  · -- If c = noSharing ∨ c = trainSharing, then IsIRPO E u c
    intro hc
    rcases hc with rfl | rfl
    · exact ⟨Or.inl rfl, hnoPO⟩
    · exact ⟨Or.inr hequiv.1, htrainPO⟩

/-- Distinct equivalent IRPO representatives rule out *literal* constructor uniqueness.
This complements the manuscript's expressly weaker “unique up to equivalence” wording. -/
theorem distinct_no_and_train_irpo_rule_out_literal_uniqueness
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (htrain : IsIRPO E u .trainSharing) :
    ¬ IsUniquelyIRPO E u .noSharing := by
  intro hunique
  have heq : Contract.trainSharing = Contract.noSharing := hunique.2 .trainSharing htrain
  exact Contract.noConfusion heq

/-- Consequently, the economic comparisons in Theorem 3.6(1) do not imply literal
constructor uniqueness; they support the manuscript's stated uniqueness up to equivalence. -/
theorem theorem3_6_part1_not_literally_unique
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part1Conditions E u) :
    ¬ IsUniquelyIRPO E u .noSharing := by
  apply distinct_no_and_train_irpo_rule_out_literal_uniqueness E u
  exact (theorem3_6_part1_irpo_characterization E u h .trainSharing).2 (Or.inr rfl)

/-- Theorem 3.6(1), with the manuscript's explicit “up to equivalence” qualifier. -/
theorem theorem3_6_part1_unique_up_to_equivalence
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part1Conditions E u) :
    IsUniquelyIRPOUpToEquivalence E u .noSharing := by
  constructor
  · -- IsIRPO E u .noSharing
    constructor
    · -- IsIndividuallyRational E u .noSharing
      left
      rfl
    · -- IsParetoOptimal E u .noSharing
      exact h.2.2.2
  · -- ∀ d, IsIRPO E u d → ContractEquivalent E u d .noSharing
    intro d hd
    rcases hd.1 with rfl | hd_ir
    · -- d = .noSharing
      exact ⟨paretoDominates_trans E u .noSharing .trainSharing .noSharing h.1.2 h.1.1,
        paretoDominates_trans E u .noSharing .trainSharing .noSharing h.1.2 h.1.1⟩
    · -- ParetoDominates E u d .noSharing
      constructor
      · exact hd_ir
      · -- ParetoDominates E u .noSharing d
        by_contra hnot
        have : StrictlyParetoDominates E u d .noSharing := ⟨hd_ir, hnot⟩
        exact h.2.2.2 _ this

/-- Economic comparisons used in Theorem 3.6(2), after imposing `alpha = beta`.
Full sharing dominates each other contract (Lemma 3.5, Lemma B.3, and the symmetric
no-sharing calculation).  The final separation condition says that only no sharing can
possibly be payoff-equivalent to full sharing, matching the dichotomy in the paper. -/
def Theorem36Part2Conditions
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) : Prop :=
  (∀ c, ParetoDominates E u .fullSharing c) ∧
  (∀ c, ParetoDominates E u c .fullSharing → c = .fullSharing ∨ c = .noSharing)

/-- Theorem 3.6(2), first branch: if no sharing does not dominate full sharing, then full
sharing is literally uniquely IRPO. -/
theorem theorem3_6_part2_unique_full
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part2Conditions E u)
    (hstrict : ¬ ParetoDominates E u .noSharing .fullSharing) :
    IsUniquelyIRPO E u .fullSharing := by
  apply universallyDominating_is_uniquelyIRPO E u .fullSharing h.1
  intro d hdom _
  rcases h.2 d hdom with rfl | rfl
  · rfl
  · exact False.elim (hstrict hdom)

/-- Theorem 3.6(2), equality branch: if no sharing also dominates full sharing, the two
contracts are equivalent and both are IRPO. -/
theorem theorem3_6_part2_equivalent_branch
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part2Conditions E u)
    (hback : ParetoDominates E u .noSharing .fullSharing)
    (hnoPO : IsParetoOptimal E u .noSharing) :
    ContractEquivalent E u .fullSharing .noSharing ∧
      IsIRPO E u .fullSharing ∧ IsIRPO E u .noSharing := by
  -- Extract the conditions from h
  have hall : ∀ c, ParetoDominates E u .fullSharing c := h.1
  -- fullSharing Pareto dominates noSharing
  have hfs_nosharing : ParetoDominates E u .fullSharing .noSharing := hall .noSharing
  -- ContractEquivalent: fullSharing ↔ noSharing
  have hequiv : ContractEquivalent E u .fullSharing .noSharing := ⟨hfs_nosharing, hback⟩
  -- IsIRPO E u .fullSharing
  have hirpo_fs : IsIRPO E u .fullSharing := by
    constructor
    -- IsIndividuallyRational E u .fullSharing
    · right
      exact hfs_nosharing
    -- IsParetoOptimal E u .fullSharing
    · intro d hd
      rw [StrictlyParetoDominates] at hd
      exact hd.2 (hall d)
  -- IsIRPO E u .noSharing
  have hirpo_ns : IsIRPO E u .noSharing := ⟨Or.inl rfl, hnoPO⟩
  exact ⟨hequiv, hirpo_fs, hirpo_ns⟩

/-- Complete formal dichotomy of Theorem 3.6(2).  In the equivalence branch the paper's
claim that no sharing is also IRPO uses its Pareto optimality, exposed here rather than
silently folded into an informal equality argument. -/
theorem theorem3_6_part2_dichotomy
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part2Conditions E u)
    (hnoPO_of_equiv : ParetoDominates E u .noSharing .fullSharing →
      IsParetoOptimal E u .noSharing) :
    IsUniquelyIRPO E u .fullSharing ∨
      (ContractEquivalent E u .fullSharing .noSharing ∧
        IsIRPO E u .fullSharing ∧ IsIRPO E u .noSharing) := by
  by_cases hback : ParetoDominates E u .noSharing .fullSharing
  · right
    exact theorem3_6_part2_equivalent_branch E u h hback (hnoPO_of_equiv hback)
  · left
    exact theorem3_6_part2_unique_full E u h hback

/-! ## Theorem 3.6(3): train sharing -/

/-- The four order comparisons isolated by the paper's open-set construction for
Theorem 3.6(3).  Train sharing strictly improves on the default, is Pareto optimal,
full sharing is not individually rational, and infer sharing is strictly dominated by
full sharing.  These are precisely the contract-order facts used after the numerical
parameter inequalities have been checked. -/
def Theorem36Part3Conditions
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) : Prop :=
  StrictlyParetoDominates E u .trainSharing .noSharing ∧
  IsParetoOptimal E u .trainSharing ∧
  ¬ ParetoDominates E u .fullSharing .noSharing ∧
  StrictlyParetoDominates E u .fullSharing .inferSharing

/-- The contract-order conclusion of Theorem 3.6(3): the paper's open-set comparisons
make train sharing the literally unique IRPO constructor. -/
theorem theorem3_6_part3_unique_train
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (h : Theorem36Part3Conditions E u) :
    IsUniquelyIRPO E u .trainSharing := by
  rcases h with ⟨htrainNo, htrainPO, hfullNotIR, hfullInfer⟩
  constructor
  · exact ⟨Or.inr htrainNo.1, htrainPO⟩
  · intro d hd
    rcases d with (_ | _ | _ | _)
    · exact False.elim (hd.2 .trainSharing htrainNo)
    · rfl
    · exact False.elim (hd.2 .fullSharing hfullInfer)
    · rcases hd.1 with hEq | hdom
      · contradiction
      · exact False.elim (hfullNotIR hdom)

end TrainSharing

import RequestProject.GeneralSignaling

/-!
# The correlation model

Initial formalization of Section 3.  A binary pair is reconstructed from its two Bernoulli
marginals and the mass of `(true,true)`.  The latter is determined by Pearson correlation
when the variances are nonzero.  This proves the algebraic core of Lemma 3.1 and records
feasibility conditions separately from the reconstruction formula.
-/

namespace TrainSharing.Correlation

/-- Parameters of the paper's correlation model. -/
structure Parameters where
  alpha : ℝ
  beta : ℝ
  theta : ℝ
  alpha_mem : alpha ∈ Set.Ioo (0 : ℝ) 1
  beta_mem : beta ∈ Set.Ioo (0 : ℝ) 1

/-- The square-root factor in the denominator of the Pearson correlation. -/
noncomputable def Parameters.scale (p : Parameters) : ℝ :=
  Real.sqrt (p.alpha * (1 - p.alpha) * p.beta * (1 - p.beta))

/-- The joint positive-positive mass recovered from correlation and marginals. -/
noncomputable def Parameters.jointTT (p : Parameters) : ℝ :=
  p.alpha * p.beta + p.theta * p.scale

/-- The complete `2 × 2` table recovered from the two marginals and `jointTT`. -/
noncomputable def Parameters.jointMass (p : Parameters) : Bool × Bool → ℝ
  | (true, true) => p.jointTT
  | (true, false) => p.alpha - p.jointTT
  | (false, true) => p.beta - p.jointTT
  | (false, false) => 1 - p.alpha - p.beta + p.jointTT

/-- Fréchet bounds characterize when the reconstructed table has nonnegative entries. -/
def Parameters.Feasible (p : Parameters) : Prop :=
  max 0 (p.alpha + p.beta - 1) ≤ p.jointTT ∧
    p.jointTT ≤ min p.alpha p.beta

lemma Parameters.scale_pos (p : Parameters) : 0 < p.scale := by
  unfold Parameters.scale
  apply Real.sqrt_pos.mpr
  have ha : p.alpha > 0 := p.alpha_mem.1
  have ha' : 1 - p.alpha > 0 := sub_pos.mpr p.alpha_mem.2
  have hb : p.beta > 0 := p.beta_mem.1
  have hb' : 1 - p.beta > 0 := sub_pos.mpr p.beta_mem.2
  exact mul_pos (mul_pos (mul_pos ha ha') hb) hb' 

lemma Parameters.jointMass_nonneg (p : Parameters) (hp : p.Feasible) :
    ∀ s, 0 ≤ p.jointMass s := by
  intro s
  rcases s with ⟨s1, s2⟩
  fin_cases s1 <;> fin_cases s2 <;> simp [Parameters.jointMass]
  · exact le_trans (le_max_left _ _) hp.1
  · exact le_trans hp.2 (min_le_left _ _)
  · exact le_trans hp.2 (min_le_right _ _)
  · linarith [hp.1, le_max_right 0 (p.alpha + p.beta - 1)]

/-- The reconstructed table has total mass one. -/
lemma Parameters.jointMass_total (p : Parameters) :
    ∑ s : Bool × Bool, p.jointMass s = 1 := by
  rw [show (Finset.univ : Finset (Bool × Bool)) =
    {(true, true), (true, false), (false, true), (false, false)} by decide]
  simp [Parameters.jointMass]

/-- The first marginal of the reconstructed table is `alpha`. -/
lemma Parameters.first_true_marginal (p : Parameters) :
    ∑ y : Bool, p.jointMass (true, y) = p.alpha := by
  simp [jointMass, jointTT]

/-- The second marginal of the reconstructed table is `beta`. -/
lemma Parameters.second_true_marginal (p : Parameters) :
    ∑ x : Bool, p.jointMass (x, true) = p.beta := by
  simp [Parameters.jointMass]

/-- Algebraic recovery of the prescribed Pearson correlation. -/
lemma Parameters.correlation_recovered (p : Parameters) :
    (p.jointMass (true, true) - p.alpha * p.beta) / p.scale = p.theta := by
  simp [jointMass, jointTT]
  exact mul_div_cancel_right₀ _ (ne_of_gt (scale_pos p))

/-- A feasible parameter tuple defines a genuine finite probability law. -/
noncomputable def Parameters.signalLaw (p : Parameters) (hp : p.Feasible) :
    FiniteLaw (Bool × Bool) where
  mass := p.jointMass
  nonneg := p.jointMass_nonneg hp
  total := p.jointMass_total

/-- Accuracy symmetry from Eq. (7): under label `true`, `true` signals have marginals
`alpha,beta`; under label `false`, the positive signals are their complements. -/
noncomputable def Parameters.world (p : Parameters) (hp : p.Feasible) : BinaryWorldModel where
  label := {
    mass := fun _ => (1 : ℝ) / 2
    nonneg := by intro; norm_num
    total := by norm_num [Finset.sum_eq_add_sum_diff_singleton] }
  signals := fun t => if t then p.signalLaw hp else {
    mass := fun s => p.jointMass (!s.1, !s.2)
    nonneg := by intro s; exact p.jointMass_nonneg hp (!s.1, !s.2)
    total := by
      rw [show (Finset.univ : Finset (Bool × Bool)) =
        {(true, true), (true, false), (false, true), (false, false)} by decide]
      simp [Parameters.jointMass]
      ring }

/-- Any `2 × 2` mass function is uniquely determined by its total mass, two true
marginals, and its true-true cell.  This is the finite-table core of Lemma 3.1. -/
theorem joint_table_unique
    (m n : Bool × Bool → ℝ)
    (hmTotal : ∑ s, m s = 1) (hnTotal : ∑ s, n s = 1)
    (hmFirst : ∑ y, m (true, y) = ∑ y, n (true, y))
    (hmSecond : ∑ x, m (x, true) = ∑ x, n (x, true))
    (hTT : m (true, true) = n (true, true)) :
    m = n := by
  ext ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> simp_all
  have hm_expand : m (true, true) + m (true, false) + m (false, true) + m (false, false) = 1 := by
    rw [← hmTotal]
    rw [show (Finset.univ : Finset (Bool × Bool)) = {(true, true), (true, false), (false, true), (false, false)} by decide]
    simp
    ring
  have hn_expand : n (true, true) + n (true, false) + n (false, true) + n (false, false) = 1 := by
    rw [← hnTotal]
    rw [show (Finset.univ : Finset (Bool × Bool)) = {(true, true), (true, false), (false, true), (false, false)} by decide]
    simp
    ring
  linarith

/-- **Lemma 3.1, one-label form.** Equal nondegenerate Bernoulli marginals and equal
Pearson correlation determine the entire joint signal distribution. -/
theorem correlation_determines_joint
    (p : Parameters) (m : Bool × Bool → ℝ)
    (hmTotal : ∑ s, m s = 1)
    (hmFirst : ∑ y, m (true, y) = p.alpha)
    (hmSecond : ∑ x, m (x, true) = p.beta)
    (hCorr : (m (true, true) - p.alpha * p.beta) / p.scale = p.theta) :
    m = p.jointMass := by
  apply joint_table_unique m (p.jointMass) hmTotal (Parameters.jointMass_total p)
  · rw [hmFirst, Parameters.first_true_marginal p]
  · rw [hmSecond, Parameters.second_true_marginal p]
  · have h1 := Parameters.correlation_recovered p
    have h2 : p.scale ≠ 0 := ne_of_gt (Parameters.scale_pos p)
    field_simp [h2] at hCorr h1
    linarith

end TrainSharing.Correlation

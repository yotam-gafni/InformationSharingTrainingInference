import RequestProject.Theorem46Selected

/-!
# The manuscript's upper-bound argument for Theorem 4.6, from the correlation model

`Theorem46Selected.lean` derived the factor-two bound of Theorem 4.6(2) from two
model-level premises collected in `ManuscriptEquilibriumConsequences`.  This file removes
the second of those premises, `trainNontrivial`, by carrying out the argument written
under “Upper Bound” in the proof of Theorem 4.6 inside the significant-action correlation
model of Section 3.

The argument in the manuscript runs as follows.  Because Firm `i`'s interim payoff from
acting *alone* depends only on its own accuracy — not on the correlation — the profile in
which no firm ever takes the significant action is an equilibrium either in every
correlation world or in none of them.  If it were an equilibrium, then (this is the
content of `no_active_strict_equilibrium`) no strict equilibrium of any world could have
a firm take a significant action, so the selected train-sharing equilibrium would be
inactive in every world and train sharing would have payoff vector `(0,0)`; literal
unique IRPO of train sharing excludes that.  Hence acting alone is strictly profitable
for one of the firms, and therefore *no* train-sharing equilibrium, under *any*
correlation, can be completely inactive.  Since `alpha, beta ≥ 1/2`, each single signal
already has unconditional probability `1/2`, which yields the factor-two bound.

Everything here is proved for the weighted (asymmetric reward/cost) version of the model
in `KnownCorrelationAsymmetric.lean`, i.e. for arbitrary `R₁ ≥ 0` and `C₁ ≥ 0`.
-/

namespace TrainSharing.Theorem46.Upper

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected

/-! ## Interim gains in terms of the four signal-pair scores -/

/-- Firm 1's interim gain is the market-share weighted sum of the two significant-action
scores in the row of its own signal. -/
theorem weightedFirm1Gain_eq (alpha beta rho reward cost : ℝ) (s2 : Bool → Bool)
    (x : Bool) :
    weightedFirm1Gain alpha beta rho reward cost s2 x =
      (weightedSharedScore alpha beta rho reward cost x true * shareFactor (s2 true) +
        weightedSharedScore alpha beta rho reward cost x false * shareFactor (s2 false)) / 2 := by
  fin_cases x <;>
    simp [weightedFirm1Gain, weightedSharedScore, conditionalMass] <;> ring

/-- Firm 2's interim gain is the market-share weighted sum of the two significant-action
scores in the column of its own signal. -/
theorem weightedFirm2Gain_eq (alpha beta rho reward cost : ℝ) (s1 : Bool → Bool)
    (y : Bool) :
    weightedFirm2Gain alpha beta rho reward cost s1 y =
      (weightedSharedScore alpha beta rho reward cost true y * shareFactor (s1 true) +
        weightedSharedScore alpha beta rho reward cost false y * shareFactor (s1 false)) / 2 := by
  fin_cases y <;>
    simp [weightedFirm2Gain, weightedSharedScore, conditionalMass] <;> ring

/-! ### The six correlation-free identities satisfied by the scores

Each row sum, each column sum, the sum of the two off-diagonal scores, and the sum of the
two diagonal scores are all free of the correlation cell `rho`, except that the last two
depend on it only through the factor `reward - cost`. -/

theorem score_row_true (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost true true +
      weightedSharedScore alpha beta rho reward cost true false =
      reward * alpha - cost * (1 - alpha) := by
  simp [weightedSharedScore, conditionalMass]; ring

theorem score_row_false (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost false true +
      weightedSharedScore alpha beta rho reward cost false false =
      reward * (1 - alpha) - cost * alpha := by
  simp [weightedSharedScore, conditionalMass]; ring

theorem score_col_true (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost true true +
      weightedSharedScore alpha beta rho reward cost false true =
      reward * beta - cost * (1 - beta) := by
  simp [weightedSharedScore, conditionalMass]; ring

theorem score_col_false (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost true false +
      weightedSharedScore alpha beta rho reward cost false false =
      reward * (1 - beta) - cost * beta := by
  simp [weightedSharedScore, conditionalMass]; ring

theorem score_offdiag (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost true false +
      weightedSharedScore alpha beta rho reward cost false true =
      (reward - cost) * (alpha + beta - 2 * rho) := by
  simp [weightedSharedScore, conditionalMass]; ring

theorem score_diag (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost true true +
      weightedSharedScore alpha beta rho reward cost false false =
      (reward - cost) * (1 - alpha - beta + 2 * rho) := by
  simp [weightedSharedScore, conditionalMass]; ring

/-- Acting alone on the positive signal: Firm 1's solo gain is correlation free. -/
theorem soloGain1 (alpha beta rho reward cost : ℝ) :
    weightedFirm1Gain alpha beta rho reward cost inactive true =
      (reward * alpha - cost * (1 - alpha)) / 2 := by
  rw [weightedFirm1Gain_eq]
  simp only [inactive, shareFactor, if_neg (by decide : ¬ (false = true))]
  rw [show (weightedSharedScore alpha beta rho reward cost true true * 1 +
      weightedSharedScore alpha beta rho reward cost true false * 1) =
      weightedSharedScore alpha beta rho reward cost true true +
      weightedSharedScore alpha beta rho reward cost true false by ring,
    score_row_true]

/-- Acting alone on the negative signal. -/
theorem soloGain1_false (alpha beta rho reward cost : ℝ) :
    weightedFirm1Gain alpha beta rho reward cost inactive false =
      (reward * (1 - alpha) - cost * alpha) / 2 := by
  rw [weightedFirm1Gain_eq]
  simp only [inactive, shareFactor, if_neg (by decide : ¬ (false = true))]
  rw [show (weightedSharedScore alpha beta rho reward cost false true * 1 +
      weightedSharedScore alpha beta rho reward cost false false * 1) =
      weightedSharedScore alpha beta rho reward cost false true +
      weightedSharedScore alpha beta rho reward cost false false by ring,
    score_row_false]

/-- Acting alone on the positive signal: Firm 2's solo gain is correlation free. -/
theorem soloGain2 (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost inactive true =
      (reward * beta - cost * (1 - beta)) / 2 := by
  rw [weightedFirm2Gain_eq]
  simp only [inactive, shareFactor, if_neg (by decide : ¬ (false = true))]
  rw [show (weightedSharedScore alpha beta rho reward cost true true * 1 +
      weightedSharedScore alpha beta rho reward cost false true * 1) =
      weightedSharedScore alpha beta rho reward cost true true +
      weightedSharedScore alpha beta rho reward cost false true by ring,
    score_col_true]

/-- Acting alone on the negative signal, for Firm 2. -/
theorem soloGain2_false (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost inactive false =
      (reward * (1 - beta) - cost * beta) / 2 := by
  rw [weightedFirm2Gain_eq]
  simp only [inactive, shareFactor, if_neg (by decide : ¬ (false = true))]
  rw [show (weightedSharedScore alpha beta rho reward cost true false * 1 +
      weightedSharedScore alpha beta rho reward cost false false * 1) =
      weightedSharedScore alpha beta rho reward cost true false +
      weightedSharedScore alpha beta rho reward cost false false by ring,
    score_col_false]

/-! ### Monotonicity of a firm's behaviour in its own signal

The manuscript's proofs repeatedly use the claim that “if the weaker signal leads to a
significant action, then so should the stronger”.  Against a rival that follows its own
signal, the exact gap between the two interim gains is recorded below.  With symmetric
reward and cost it is nonnegative, so the claim holds; with asymmetric reward and cost the
gap can be negative, because acting after the *positive* signal is precisely acting where
the rival also acts and takes half the market.  `Example47.lean` uses
that failure. -/

theorem weightedFirm2Gain_follow_difference (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost follow true -
      weightedFirm2Gain alpha beta rho reward cost follow false =
      (-(reward - cost) * rho + reward * (alpha + 4 * beta - 2) / 2 -
        cost * (alpha - 2 * beta + 1) / 2) / 2 := by
  simp [weightedFirm2Gain_eq, weightedSharedScore, conditionalMass, follow, shareFactor]
  ring

theorem weightedFirm1Gain_follow_difference (alpha beta rho reward cost : ℝ) :
    weightedFirm1Gain alpha beta rho reward cost follow true -
      weightedFirm1Gain alpha beta rho reward cost follow false =
      (-(reward - cost) * rho + reward * (beta + 4 * alpha - 2) / 2 -
        cost * (beta - 2 * alpha + 1) / 2) / 2 := by
  simp [weightedFirm1Gain_eq, weightedSharedScore, conditionalMass, follow, shareFactor]
  ring

/-- With symmetric reward and mistake cost the manuscript's monotonicity claim is correct
for the secondary firm. -/
theorem weightedFirm2Gain_follow_monotone (alpha beta rho r : ℝ)
    (hbeta : 1 / 2 ≤ beta) (hr : 0 ≤ r) :
    weightedFirm2Gain alpha beta rho r r follow false ≤
      weightedFirm2Gain alpha beta rho r r follow true := by
  have h : weightedFirm2Gain alpha beta rho r r follow true -
      weightedFirm2Gain alpha beta rho r r follow false = r * (6 * beta - 3) / 4 := by
    simp [weightedFirm2Gain_eq, weightedSharedScore, conditionalMass, follow, shareFactor]
    ring
  nlinarith [h]

/-! ## Strict equilibria -/

/-- Signal-by-signal *strict* equilibrium for the weighted significant-action model:
each prescribed action is the unique interim best response. -/
def IsStrictWeightedNash (alpha beta rho reward cost : ℝ) (s1 s2 : Bool → Bool) : Prop :=
  (∀ x, if s1 x then 0 < weightedFirm1Gain alpha beta rho reward cost s2 x
                  else weightedFirm1Gain alpha beta rho reward cost s2 x < 0) ∧
  (∀ y, if s2 y then 0 < weightedFirm2Gain alpha beta rho reward cost s1 y
                  else weightedFirm2Gain alpha beta rho reward cost s1 y < 0)

/-- A strict equilibrium is in particular an equilibrium. -/
theorem IsStrictWeightedNash.toNash {alpha beta rho reward cost : ℝ} {s1 s2 : Bool → Bool}
    (h : IsStrictWeightedNash alpha beta rho reward cost s1 s2) :
    IsWeightedNoSharingNash alpha beta rho reward cost s1 s2 := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · have hx := h.1 x
    split_ifs at hx ⊢ <;> linarith
  · have hy := h.2 y
    split_ifs at hy ⊢ <;> linarith

/-! ## The core sign argument

The following purely arithmetical lemma is the heart of the matter.  Write `Wxy` for the
four significant-action scores.  Suppose the four sums that describe *acting alone* are
nonpositive (`A1`–`A4`), and the two correlation-dependent sums are nonpositive as well
(`A5`, `A6`; these follow from `reward ≤ cost`, which itself follows from `A1`).  Then no
firm can strictly want to act, whatever the market-sharing pattern.  All fifteen active
patterns are refuted by linear arithmetic alone. -/
theorem no_active_strict_equilibrium_core
    (Wtt Wtf Wft Wff : ℝ)
    (A1 : Wtt + Wtf ≤ 0) (A2 : Wft + Wff ≤ 0) (A3 : Wtt + Wft ≤ 0)
    (A4 : Wtf + Wff ≤ 0) (A5 : Wtf + Wft ≤ 0) (A6 : Wtt + Wff ≤ 0)
    (t1 f1 t2 f2 : Bool)
    (h1t : t1 = true → 0 < Wtt * shareFactor t2 + Wtf * shareFactor f2)
    (h1f : f1 = true → 0 < Wft * shareFactor t2 + Wff * shareFactor f2)
    (h2t : t2 = true → 0 < Wtt * shareFactor t1 + Wft * shareFactor f1)
    (h2f : f2 = true → 0 < Wtf * shareFactor t1 + Wff * shareFactor f1)
    (hactive : t1 = true ∨ f1 = true ∨ t2 = true ∨ f2 = true) : False := by
  fin_cases t1 <;> fin_cases f1 <;> fin_cases t2 <;> fin_cases f2 <;> simp [shareFactor] at * <;> linarith

/-- If acting alone on the positive signal is unprofitable for the more accurate firm,
the mistake cost dominates the reward. -/
theorem reward_le_cost_of_solo_nonpos (alpha reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (h : reward * alpha - cost * (1 - alpha) ≤ 0) : reward ≤ cost := by
  nlinarith [sq_nonneg alpha, sq_nonneg reward, sq_nonneg cost]

/-- **The manuscript's key equilibrium fact.**  In the significant-action correlation
model with `alpha, beta ≥ 1/2`, if some firm takes the significant action at a strict
equilibrium, then acting alone on the positive signal is strictly profitable for one of
the two firms.  Equivalently (contrapositive): if acting alone is unprofitable for both
firms, then every strict equilibrium — under *every* correlation — is completely
inactive. -/
theorem solo_gain_pos_of_active
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hactive : NontrivialProfile s1 s2) :
    0 < weightedFirm1Gain alpha beta rho reward cost inactive true ∨
      0 < weightedFirm2Gain alpha beta rho reward cost inactive true := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [soloGain1] at h1
  rw [soloGain2] at h2
  have hrow : reward * alpha - cost * (1 - alpha) ≤ 0 := by linarith
  have hcol : reward * beta - cost * (1 - beta) ≤ 0 := by linarith
  have hRC : reward ≤ cost :=
    reward_le_cost_of_solo_nonpos alpha reward cost halpha hreward hcost hrow
  refine no_active_strict_equilibrium_core
    (weightedSharedScore alpha beta rho reward cost true true)
    (weightedSharedScore alpha beta rho reward cost true false)
    (weightedSharedScore alpha beta rho reward cost false true)
    (weightedSharedScore alpha beta rho reward cost false false)
    ?_ ?_ ?_ ?_ ?_ ?_ (s1 true) (s1 false) (s2 true) (s2 false) ?_ ?_ ?_ ?_ ?_
  · rw [score_row_true]; exact hrow
  · rw [score_row_false]; nlinarith
  · rw [score_col_true]; exact hcol
  · rw [score_col_false]; nlinarith
  · rw [score_offdiag]; nlinarith
  · rw [score_diag]; nlinarith
  · intro hx
    have hg := hnash.1 true
    rw [hx] at hg
    simp only [if_true] at hg
    rw [weightedFirm1Gain_eq] at hg
    linarith
  · intro hx
    have hg := hnash.1 false
    rw [hx] at hg
    simp only [if_true] at hg
    rw [weightedFirm1Gain_eq] at hg
    linarith
  · intro hy
    have hg := hnash.2 true
    rw [hy] at hg
    simp only [if_true] at hg
    rw [weightedFirm2Gain_eq] at hg
    linarith
  · intro hy
    have hg := hnash.2 false
    rw [hy] at hg
    simp only [if_true] at hg
    rw [weightedFirm2Gain_eq] at hg
    linarith
  · rcases hactive with ⟨x, hx⟩ | ⟨y, hy⟩
    · cases x with
      | true => exact Or.inl hx
      | false => exact Or.inr (Or.inl hx)
    · cases y with
      | true => exact Or.inr (Or.inr (Or.inl hy))
      | false => exact Or.inr (Or.inr (Or.inr hy))

/-- Contrapositive packaging: if neither firm profits from acting alone on its positive
signal, every strict equilibrium is completely inactive. -/
theorem strict_equilibrium_trivial_of_solo_nonpos
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (hsolo1 : weightedFirm1Gain alpha beta rho reward cost inactive true ≤ 0)
    (hsolo2 : weightedFirm2Gain alpha beta rho reward cost inactive true ≤ 0)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2) :
    TrivialProfile s1 s2 := by
  rw [trivialProfile_iff_not_nontrivial]
  intro hactive
  rcases solo_gain_pos_of_active alpha beta rho reward cost halpha hbeta hreward hcost
    hrho0 hrhoa hrhob hrho1 s1 s2 hnash hactive with h | h
  · exact absurd h (not_lt.mpr hsolo1)
  · exact absurd h (not_lt.mpr hsolo2)

/-! ## Worldwise activity of the selected train-sharing equilibrium -/

/-- The solo gains do not depend on the revealed correlation world, so if the selected
train-sharing equilibrium is inactive in one world it must be inactive in all of them.
Combined with literal unique IRPO of train sharing, this is the manuscript's conclusion
that “no train-sharing equilibrium can be such that no significant action is taken”. -/
theorem worldwise_nontrivial_of_not_worldwiseTrivial {W : Type}
    (alpha beta reward cost : ℝ) (rho : W → ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ rho w) (hrhoa : ∀ w, rho w ≤ alpha) (hrhob : ∀ w, rho w ≤ beta)
    (hrho1 : ∀ w, 0 ≤ 1 - alpha - beta + rho w)
    (t1 t2 : W → Bool → Bool)
    (hnash : ∀ w, IsStrictWeightedNash alpha beta (rho w) reward cost (t1 w) (t2 w))
    (hsome : ¬ WorldwiseTrivialProfile t1 t2) :
    ∀ w, NontrivialProfile (t1 w) (t2 w) := by
  -- Some world `w₀` is active, so acting alone is strictly profitable for a firm.
  have hexists : ∃ w, NontrivialProfile (t1 w) (t2 w) := by
    by_contra hcon
    push_neg at hcon
    exact hsome fun w => (trivialProfile_iff_not_nontrivial (t1 w) (t2 w)).mpr (hcon w)
  obtain ⟨w0, hw0⟩ := hexists
  have hsolo := solo_gain_pos_of_active alpha beta (rho w0) reward cost halpha hbeta
    hreward hcost (hrho0 w0) (hrhoa w0) (hrhob w0) (hrho1 w0) _ _ (hnash w0) hw0
  intro w
  by_contra hcon
  have htriv : TrivialProfile (t1 w) (t2 w) :=
    (trivialProfile_iff_not_nontrivial (t1 w) (t2 w)).mpr hcon
  have h1 : weightedFirm1Gain alpha beta (rho w) reward cost inactive true ≤ 0 := by
    have := (hnash w).1 true
    rw [htriv.1 true] at this
    have heq : t2 w = inactive := funext fun y => htriv.2 y
    rw [heq] at this
    simpa using le_of_lt this
  have h2 : weightedFirm2Gain alpha beta (rho w) reward cost inactive true ≤ 0 := by
    have := (hnash w).2 true
    rw [htriv.2 true] at this
    have heq : t1 w = inactive := funext fun x => htriv.1 x
    rw [heq] at this
    simpa using le_of_lt this
  -- Solo gains are correlation free, so the two worlds must agree.
  rw [soloGain1] at h1 hsolo
  rw [soloGain2] at h2 hsolo
  rcases hsolo with h | h
  · exact absurd h (not_lt.mpr h1)
  · exact absurd h (not_lt.mpr h2)

/-- The manuscript's first paragraph, without its restriction to four action patterns.
If the all-inactive profile is an equilibrium of the no-sharing game — equivalently, if
neither firm profits from acting alone on its positive signal — then the selected
train-sharing equilibrium is inactive in *every* correlation world. -/
theorem worldwiseTrivial_of_solo_nonpos {W : Type}
    (alpha beta reward cost : ℝ) (rho : W → ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ rho w) (hrhoa : ∀ w, rho w ≤ alpha) (hrhob : ∀ w, rho w ≤ beta)
    (hrho1 : ∀ w, 0 ≤ 1 - alpha - beta + rho w)
    (hsolo1 : ∀ w, weightedFirm1Gain alpha beta (rho w) reward cost inactive true ≤ 0)
    (hsolo2 : ∀ w, weightedFirm2Gain alpha beta (rho w) reward cost inactive true ≤ 0)
    (t1 t2 : W → Bool → Bool)
    (hnash : ∀ w, IsStrictWeightedNash alpha beta (rho w) reward cost (t1 w) (t2 w)) :
    WorldwiseTrivialProfile t1 t2 := fun w =>
  strict_equilibrium_trivial_of_solo_nonpos alpha beta (rho w) reward cost halpha hbeta
    hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (hrho1 w) (hsolo1 w) (hsolo2 w) _ _ (hnash w)

/-! ## Theorem 4.6(2) with no separate activity premise -/

/-- **Theorem 4.6(2), factor two, from the model.**

For a fixed selected equilibrium of every contract, assume only that

* train sharing is literally uniquely IRPO (the manuscript's hypothesis), and
* in every revealed correlation world the selected train-sharing profile is a strict
  equilibrium of that world's significant-action game, with the standing model
  restrictions `alpha, beta ≥ 1/2` and nonnegative reward and mistake cost.

Then every selected contract equilibrium has trade probability at most twice that of
train sharing.  The activity premise `ManuscriptEquilibriumConsequences.trainNontrivial`
used in `Theorem46Selected.lean` is *derived* here rather than assumed. -/
theorem theorem4_6_factor_two_from_model {W : Type} [Fintype W]
    (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (S : EquilibriumSelection W)
    (hunique : TrainSharing.Theorem46.Selected.IsUniquelyIRPO S Contract.trainSharing)
    (alpha beta reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta)
    (hnash : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (S.trainFirm1 w) (S.trainFirm2 w)) :
    ∀ c : Contract,
      correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event c) ≤
        2 * correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event .trainSharing) := by
  have hnontrivial : ∀ w, NontrivialProfile (S.trainFirm1 w) (S.trainFirm2 w) := by
    refine worldwise_nontrivial_of_not_worldwiseTrivial alpha beta reward cost
      (fun w => (parameters w).jointTT) halpha hbeta hreward hcost ?_ ?_ ?_ ?_
      _ _ hnash (unique_trainSharing_forces_some_activity S hunique)
    · intro w
      have := (feasible w).1
      exact le_trans (le_max_left _ _) this
    · intro w
      have := (feasible w).2
      have h := le_trans this (min_le_left _ _)
      rw [halphaw w] at h
      exact h
    · intro w
      have := (feasible w).2
      have h := le_trans this (min_le_right _ _)
      rw [hbetaw w] at h
      exact h
    · intro w
      have h1 := (feasible w).1
      have h2 := le_max_right (0 : ℝ) ((parameters w).alpha + (parameters w).beta - 1)
      have := le_trans h2 h1
      rw [halphaw w, hbetaw w] at this
      linarith
  intro c
  rw [S.train_event]
  have hhalf : (1 / 2 : ℝ) ≤ correlationTradeProbability prior
      (fun w => parameterInferenceLaw (parameters w) (feasible w))
      S.trainFirm1 S.trainFirm2 := by
    apply correlationTradeProbability_half
    · intro w; exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).1
    · intro w; exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.1
    · intro w; exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.2.1
    · intro w; exact (parameterInferenceLaw_marginals (parameters w) (feasible w)).2.2.2
    · exact hnontrivial
  have hone := correlationEventProbability_le_one prior
    (fun w => parameterInferenceLaw (parameters w) (feasible w)) (S.event c)
  change correlationEventProbability prior
      (fun w => parameterInferenceLaw (parameters w) (feasible w)) (S.event c) ≤
    2 * correlationTradeProbability prior
      (fun w => parameterInferenceLaw (parameters w) (feasible w))
      S.trainFirm1 S.trainFirm2
  linarith

/-! ## Generic equilibrium-classification lemmas

The facts below hold at every significant-action correlation game and are used by the
equilibrium classifications and by the explicit rational instances. -/

theorem shareFactor_pos (b : Bool) : 0 < shareFactor b := by
  cases b <;> norm_num [shareFactor]

/-- If both scores in the row of Firm 1's positive signal are positive and both scores in
the row of its negative signal are negative, Firm 1 follows its signal at every
equilibrium, whatever Firm 2 does. -/
theorem firm1_eq_follow (alpha beta rho reward cost : ℝ) (s1 s2 : Bool → Bool)
    (hAt : 0 < weightedSharedScore alpha beta rho reward cost true true)
    (hAf : 0 < weightedSharedScore alpha beta rho reward cost true false)
    (hBt : weightedSharedScore alpha beta rho reward cost false true < 0)
    (hBf : weightedSharedScore alpha beta rho reward cost false false < 0)
    (hnash : IsWeightedNoSharingNash alpha beta rho reward cost s1 s2) :
    s1 = follow := by
  have hposA : 0 < weightedFirm1Gain alpha beta rho reward cost s2 true := by
    rw [weightedFirm1Gain_eq]
    have h1 := mul_pos hAt (shareFactor_pos (s2 true))
    have h2 := mul_pos hAf (shareFactor_pos (s2 false))
    linarith
  have hnegB : weightedFirm1Gain alpha beta rho reward cost s2 false < 0 := by
    rw [weightedFirm1Gain_eq]
    have h1 := mul_neg_of_neg_of_pos hBt (shareFactor_pos (s2 true))
    have h2 := mul_neg_of_neg_of_pos hBf (shareFactor_pos (s2 false))
    linarith
  have h1 := hnash.1 true
  have h2 := hnash.1 false
  funext x
  cases x with
  | true =>
    by_contra hcon
    have hfalse : s1 true = false := by
      cases hx : s1 true with
      | false => rfl
      | true => exact absurd (by simp [follow, hx]) hcon
    rw [hfalse] at h1
    simp at h1
    linarith
  | false =>
    by_contra hcon
    have htrue : s1 false = true := by
      cases hx : s1 false with
      | true => rfl
      | false => exact absurd (by simp [follow, hx]) hcon
    rw [htrue] at h2
    simp only [if_true] at h2
    linarith

/-- Given that Firm 1 follows its signal, a strictly positive interim score sum forces
Firm 2 to act. -/
theorem firm2_act_of_pos (alpha beta rho reward cost : ℝ) (s1 s2 : Bool → Bool) (y : Bool)
    (hs1 : s1 = follow)
    (h : 0 < weightedSharedScore alpha beta rho reward cost true y / 2 +
      weightedSharedScore alpha beta rho reward cost false y)
    (hnash : IsWeightedNoSharingNash alpha beta rho reward cost s1 s2) :
    s2 y = true := by
  have hgain : 0 < weightedFirm2Gain alpha beta rho reward cost s1 y := by
    rw [weightedFirm2Gain_eq, hs1]
    simp only [follow, id_eq, shareFactor, if_true, if_neg (by decide : ¬ (false = true))]
    linarith
  have hy := hnash.2 y
  cases hcase : s2 y with
  | true => rfl
  | false =>
    rw [hcase] at hy
    simp at hy
    linarith

/-- Given that Firm 1 follows its signal, a strictly negative interim score sum forces
Firm 2 to stay out. -/
theorem firm2_out_of_neg (alpha beta rho reward cost : ℝ) (s1 s2 : Bool → Bool) (y : Bool)
    (hs1 : s1 = follow)
    (h : weightedSharedScore alpha beta rho reward cost true y / 2 +
      weightedSharedScore alpha beta rho reward cost false y < 0)
    (hnash : IsWeightedNoSharingNash alpha beta rho reward cost s1 s2) :
    s2 y = false := by
  have hgain : weightedFirm2Gain alpha beta rho reward cost s1 y < 0 := by
    rw [weightedFirm2Gain_eq, hs1]
    simp only [follow, id_eq, shareFactor, if_true, if_neg (by decide : ¬ (false = true))]
    linarith
  have hy := hnash.2 y
  cases hcase : s2 y with
  | false => rfl
  | true =>
    rw [hcase] at hy
    simp only [if_true] at hy
    linarith

/-- Firm 2's *inverted* strategy: take the significant action exactly on the *negative*
inference signal.  This is the pattern excluded by Definition 4.5. -/
def antiFollow : Bool → Bool := fun y => !y

/-- Under full sharing (and, with a single mixture law, under inference sharing) both
firms observe the realized signal pair, and taking the significant action there is
strictly profitable exactly when the pair's score is positive — whatever the rival does,
since sharing the market only halves the sign-preserving payoff.  The equilibrium is
therefore for both firms to act exactly on the positive cells, each collecting a quarter
of the score. -/
theorem fullSharing_action_dominant (score : ℝ) (rival : Bool) :
    (0 < score → 0 < score / 2 * shareFactor rival) ∧
    (score < 0 → score / 2 * shareFactor rival < 0) := by
  have hpos := shareFactor_pos rival
  constructor <;> intro h
  · positivity
  · exact mul_neg_of_neg_of_pos (by linarith) hpos

/-- Each firm's full-information equilibrium payoff. -/
noncomputable def fullInfoPayoff (alpha beta rho reward cost : ℝ) : ℝ :=
  ∑ q : Bool × Bool, max (weightedSharedScore alpha beta rho reward cost q.1 q.2) 0 / 4


end TrainSharing.Theorem46.Upper

import RequestProject.Theorem46Parts

/-!
# Theorem 4.6(1) under the non-inversion assumption

`Theorem46Parts.part1_transfer_of_monotone_worlds` proves conclusion (1) of Theorem 4.6
under the condition

> in **no** correlation world does the secondary firm take the significant action after its
> own negative inference signal,

i.e. under `∀ w, t₂ w b = 0`.  The manuscript assumes less: only that the train-sharing
equilibrium is not *inverted* (Definition 4.5), i.e. that no world has the pattern
`a → 0, b → 1`.  By the classification of the strict equilibria
(`strict_equilibrium_classification`) there are exactly three world patterns in which the
secondary firm acts after `b`:

* `A → 1, b → 1` (that is, `a → 0, b → 1`) — the **inverted** pattern, excluded by
  Definition 4.5;
* `A → 1, a → 1, b → 1`;
* `A → 1, B → 1, a → 1, b → 1` (everybody always acts).

This file assumes away only the first, and disposes of the other two:

* **the all-acting world** (`Section 1`).  The four incentive constraints of the
  everywhere-active profile are the four *correlation-free* row and column sums, so if that
  profile is a strict equilibrium in one correlation world it is a strict equilibrium of the
  no-sharing game at the prior mixture as well, where it trades with probability one.  The
  consumer therefore weakly prefers *that* no-sharing equilibrium: conclusion (1) survives in
  its existential reading.

* **the `A → 1, a → 1, b → 1` world** (`Section 2`).  Here nothing has to be assumed.  If
  that profile is a strict equilibrium in one world then, at the same primitives, the only
  other strict-equilibrium patterns are `A → 1, a → 1` and `A → 1, b → 1`; the latter is
  excluded by non-inversion, so every world is either `A → 1, a → 1` or
  `A → 1, a → 1, b → 1`, and the no-sharing equilibrium at the prior mixture is one of
  those two.  A payoff computation then shows that Firm 1 strictly loses from an
  `A → 1, a → 1, b → 1` world — its ex-ante payoff drops by `W(A,b)/4 > 0` — so Pareto
  dominance of train sharing forces every such world to carry prior probability zero, and
  the trade probabilities agree.

The results are `theorem4_6_part1_nonInverted` (the selected reading, which additionally
needs that no world is all-acting — see `Theorem46Part1AllActing.lean`),
`theorem4_6_part1_existence_nonInverted` (the manuscript's existential reading, with
nothing assumed about all-acting worlds), and `theorem4_6_part1_or_inverted`, which states
the same fact as a dichotomy against Definition 4.5.  Example 4.7 shows that non-inversion
cannot be dropped.
-/

namespace TrainSharing.Theorem46.Part1

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected
open TrainSharing.Theorem46.Upper
open TrainSharing.Theorem46.Classification
open TrainSharing.Theorem46.Transfer

/-- Take the significant action after either inference signal. -/
def alwaysAct : Bool → Bool := fun _ => true

@[simp] theorem alwaysAct_apply (x : Bool) : alwaysAct x = true := rfl

/-! ## 0.  Interim gains and ex-ante payoffs of the two exceptional patterns -/

/-- Against an always-acting rival, Firm 1's interim gain after `A` is a quarter of its
positive row sum — a correlation-free quantity. -/
theorem gain1_alwaysAct_true (alpha beta rho reward cost : ℝ) :
    weightedFirm1Gain alpha beta rho reward cost alwaysAct true =
      (reward * alpha - cost * (1 - alpha)) / 4 := by
  simp [weightedFirm1Gain, conditionalMass, alwaysAct, shareFactor]; ring

/-- Against an always-acting rival, Firm 1's interim gain after `B` is a quarter of its
negative row sum. -/
theorem gain1_alwaysAct_false (alpha beta rho reward cost : ℝ) :
    weightedFirm1Gain alpha beta rho reward cost alwaysAct false =
      (reward * (1 - alpha) - cost * alpha) / 4 := by
  simp [weightedFirm1Gain, conditionalMass, alwaysAct, shareFactor]; ring

/-- Against an always-acting rival, Firm 2's interim gain after `a` is a quarter of its
positive column sum. -/
theorem gain2_alwaysAct_true (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost alwaysAct true =
      (reward * beta - cost * (1 - beta)) / 4 := by
  simp [weightedFirm2Gain, conditionalMass, alwaysAct, shareFactor]; ring

/-- Against an always-acting rival, Firm 2's interim gain after `b` is a quarter of its
negative column sum. -/
theorem gain2_alwaysAct_false (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost alwaysAct false =
      (reward * (1 - beta) - cost * beta) / 4 := by
  simp [weightedFirm2Gain, conditionalMass, alwaysAct, shareFactor]; ring

/-- Firm 2's interim gain after `a` against a signal-following rival. -/
theorem gain2_follow_true (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost follow true =
      (reward * beta - cost * (1 - beta)) / 2 -
        weightedSharedScore alpha beta rho reward cost true true / 4 := by
  simp [weightedFirm2Gain, weightedSharedScore, conditionalMass, follow, shareFactor]; ring

/-- Firm 2's interim gain after `b` against a signal-following rival. -/
theorem gain2_follow_false (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost follow false =
      ((reward * (1 - beta) - cost * beta) - (reward * alpha - cost * (1 - alpha)) / 2 +
        weightedSharedScore alpha beta rho reward cost true true / 2) / 2 := by
  simp [weightedFirm2Gain, weightedSharedScore, conditionalMass, follow, shareFactor]; ring

/-- Firm 1's interim gain after `A` against a signal-following rival. -/
theorem gain1_follow_true (alpha beta rho reward cost : ℝ) :
    weightedFirm1Gain alpha beta rho reward cost follow true =
      ((reward * alpha - cost * (1 - alpha)) -
        weightedSharedScore alpha beta rho reward cost true true / 2) / 2 := by
  simp [weightedFirm1Gain, weightedSharedScore, conditionalMass, follow, shareFactor]; ring

/-- Firm 1's ex-ante payoff at the `A → 1, a → 1, b → 1` profile: it acts exactly after `A`
and always shares the market, so it collects a quarter of its positive row sum. -/
theorem payoff1_follow_alwaysAct (alpha beta rho reward cost : ℝ) :
    weightedNoSharingPayoff1 alpha beta rho reward cost follow alwaysAct =
      (reward * alpha - cost * (1 - alpha)) / 4 := by
  simp [weightedNoSharingPayoff1, conditionalMass, follow, alwaysAct, shareFactor]; ring

/-! ## 1.  The all-acting world -/

/-- **The all-acting profile is correlation free.**  Its four incentive constraints are the
four row and column sums, which do not depend on the correlation cell.  Hence if everybody
always acting is a strict equilibrium in one correlation world, it is a strict equilibrium
in every correlation world — in particular in the no-sharing game played at the prior
mixture. -/
theorem alwaysAct_strict_of_strict (alpha beta rho rho' reward cost : ℝ)
    (h : IsStrictWeightedNash alpha beta rho reward cost alwaysAct alwaysAct) :
    IsStrictWeightedNash alpha beta rho' reward cost alwaysAct alwaysAct := by
  obtain ⟨h1, h2⟩ := h
  have hA := h1 true
  have hB := h1 false
  have ha := h2 true
  have hb := h2 false
  simp only [alwaysAct_apply, if_true] at hA hB ha hb
  rw [gain1_alwaysAct_true] at hA
  rw [gain1_alwaysAct_false] at hB
  rw [gain2_alwaysAct_true] at ha
  rw [gain2_alwaysAct_false] at hb
  refine ⟨fun x => ?_, fun y => ?_⟩
  · cases x <;> simp only [alwaysAct_apply, if_true]
    · rw [gain1_alwaysAct_false]; exact hB
    · rw [gain1_alwaysAct_true]; exact hA
  · cases y <;> simp only [alwaysAct_apply, if_true]
    · rw [gain2_alwaysAct_false]; exact hb
    · rw [gain2_alwaysAct_true]; exact ha

/-- The all-acting profile always trades. -/
theorem tradeEvent_alwaysAct (q : Bool × Bool) :
    TrainSharing.Theorem43.tradeEvent alwaysAct alwaysAct q = true := by
  simp [TrainSharing.Theorem43.tradeEvent, alwaysAct]

/-! ## 2.  The `A → 1, a → 1, b → 1` world

Write `S₁ = R₁α - C₁(1-α)` and `S₁' = R₁(1-α) - C₁α` for Firm 1's two row sums and
`S₂ = R₁β - C₁(1-β)`, `S₂' = R₁(1-β) - C₁β` for Firm 2's two column sums — the four
correlation-free quantities that measure acting alone.  At an `A → 1, a → 1, b → 1` strict
equilibrium

* `S₁ > 0` and `S₁' < 0` (Firm 1's two constraints against an always-acting rival are
  `S₁/4 > 0` and `S₁'/4 < 0`),
* `W(A,a) < 2S₂` and `S₁ - 2S₂' < W(A,a)` (Firm 2's two constraints against a following
  rival),

and these already force `C₁ < R₁` and `W(A,b) > 0`. -/
theorem followAlways_facts (alpha beta rho reward cost : ℝ)
    (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (h : IsStrictWeightedNash alpha beta rho reward cost follow alwaysAct) :
    0 < reward * alpha - cost * (1 - alpha) ∧
    reward * (1 - alpha) - cost * alpha < 0 ∧
    weightedSharedScore alpha beta rho reward cost true true <
      2 * (reward * beta - cost * (1 - beta)) ∧
    (reward * alpha - cost * (1 - alpha)) - 2 * (reward * (1 - beta) - cost * beta) <
      weightedSharedScore alpha beta rho reward cost true true ∧
    cost < reward ∧
    0 < weightedSharedScore alpha beta rho reward cost true false := by
  have hA := h.1 true
  have hB := h.1 false
  have ha := h.2 true
  have hb := h.2 false
  simp only [follow, id_eq, if_true, Bool.false_eq_true, if_false] at hA hB
  simp only [alwaysAct_apply, if_true] at ha hb
  rw [gain1_alwaysAct_true] at hA
  rw [gain1_alwaysAct_false] at hB
  rw [gain2_follow_true] at ha
  rw [gain2_follow_false] at hb
  have hrowT : 0 < reward * alpha - cost * (1 - alpha) := by linarith
  have hrowF : reward * (1 - alpha) - cost * alpha < 0 := by linarith
  have hcolT : weightedSharedScore alpha beta rho reward cost true true <
      2 * (reward * beta - cost * (1 - beta)) := by linarith
  have hcolF : (reward * alpha - cost * (1 - alpha)) -
      2 * (reward * (1 - beta) - cost * beta) <
      weightedSharedScore alpha beta rho reward cost true true := by linarith
  have hRC : cost < reward := by
    have hsum : (reward * beta - cost * (1 - beta)) + (reward * (1 - beta) - cost * beta) =
        reward - cost := by ring
    linarith
  refine ⟨hrowT, hrowF, hcolT, hcolF, hRC, ?_⟩
  -- `W(A,b) = (R-C)(α-ρ) + C(α-β) ≥ 0`, and it cannot vanish at such an equilibrium
  have hexp : weightedSharedScore alpha beta rho reward cost true false =
      reward * (alpha - rho) - cost * (beta - rho) := by
    simp [weightedSharedScore, conditionalMass]
  have hexpba : weightedSharedScore alpha beta rho reward cost false true =
      reward * (beta - rho) - cost * (alpha - rho) := by
    simp [weightedSharedScore, conditionalMass]
  have hexpbb : weightedSharedScore alpha beta rho reward cost false false =
      reward * (1 - alpha - beta + rho) - cost * rho := by
    simp [weightedSharedScore, conditionalMass]
  have hexpaa : weightedSharedScore alpha beta rho reward cost true true =
      reward * rho - cost * (1 - alpha - beta + rho) := by
    simp [weightedSharedScore, conditionalMass]
  -- the two constraints, in score form
  have h1 : weightedSharedScore alpha beta rho reward cost false true +
      weightedSharedScore alpha beta rho reward cost false false < 0 := by
    rw [score_row_false]; linarith
  have h2 : 0 < weightedSharedScore alpha beta rho reward cost true false +
      2 * weightedSharedScore alpha beta rho reward cost false false := by
    rw [hexp, hexpbb]
    rw [hexpaa] at hcolF
    linarith
  rw [hexpba, hexpbb] at h1
  rw [hexp, hexpbb] at h2
  rw [hexp]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ reward - cost) (by linarith : (0:ℝ) ≤ alpha - rho),
    mul_nonneg (by linarith : (0:ℝ) ≤ reward - cost) (by linarith : (0:ℝ) ≤ beta - rho)]

/-! ### Reading off the four interim inequalities of a strict equilibrium -/

theorem gain1_pos_of_act {alpha beta rho reward cost : ℝ} {s1 s2 : Bool → Bool} {x : Bool}
    (h : IsStrictWeightedNash alpha beta rho reward cost s1 s2) (hx : s1 x = true) :
    0 < weightedFirm1Gain alpha beta rho reward cost s2 x := by
  have hg := h.1 x; rw [hx] at hg; simpa using hg

theorem gain1_neg_of_abstain {alpha beta rho reward cost : ℝ} {s1 s2 : Bool → Bool} {x : Bool}
    (h : IsStrictWeightedNash alpha beta rho reward cost s1 s2) (hx : s1 x = false) :
    weightedFirm1Gain alpha beta rho reward cost s2 x < 0 := by
  have hg := h.1 x; rw [hx] at hg; simpa using hg

theorem gain2_pos_of_act {alpha beta rho reward cost : ℝ} {s1 s2 : Bool → Bool} {y : Bool}
    (h : IsStrictWeightedNash alpha beta rho reward cost s1 s2) (hy : s2 y = true) :
    0 < weightedFirm2Gain alpha beta rho reward cost s1 y := by
  have hg := h.2 y; rw [hy] at hg; simpa using hg

theorem gain2_neg_of_abstain {alpha beta rho reward cost : ℝ} {s1 s2 : Bool → Bool} {y : Bool}
    (h : IsStrictWeightedNash alpha beta rho reward cost s1 s2) (hy : s2 y = false) :
    weightedFirm2Gain alpha beta rho reward cost s1 y < 0 := by
  have hg := h.2 y; rw [hy] at hg; simpa using hg

/-- The diagonal score, written out. -/
theorem score_tt_eq (alpha beta rho reward cost : ℝ) :
    weightedSharedScore alpha beta rho reward cost true true =
      reward * rho - cost * (1 - alpha - beta + rho) := by
  simp [weightedSharedScore, conditionalMass]

/-- Whenever the primary firm follows its signal and the secondary firm acts after `a`,
the diagonal score is below twice the positive column sum. -/
theorem score_tt_lt_two_colTrue (alpha beta rho reward cost : ℝ) (s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost follow s2)
    (ha : s2 true = true) :
    weightedSharedScore alpha beta rho reward cost true true <
      2 * (reward * beta - cost * (1 - beta)) := by
  have hg := gain2_pos_of_act hnash ha
  rw [gain2_follow_true] at hg
  linarith

/-- **Only three patterns survive at the primitives of a `A → 1, a → 1, b → 1` world.**

Suppose two of the correlation-free facts extracted in `followAlways_facts` hold — the
negative row sum is negative, and the window `S₁ - 2S₂' < 2S₂` left by the secondary
firm's two constraints is nonempty (the two together already force `C₁ < R₁` and
`S₁ > 0`).  Then, at *any* feasible correlation cell, a strict equilibrium is one of
`A → 1, a → 1`, `A → 1, b → 1` or `A → 1, a → 1, b → 1`: the inactive, single-firm and
all-acting patterns are all excluded. -/
theorem classification_of_followAlways_facts
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrowF : reward * (1 - alpha) - cost * alpha < 0)
    (hwindow : (reward * alpha - cost * (1 - alpha)) -
      2 * (reward * (1 - beta) - cost * beta) < 2 * (reward * beta - cost * (1 - beta)))
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2) :
    (s1 = follow ∧ s2 = follow) ∨ (s1 = follow ∧ s2 = antiFollow) ∨
      (s1 = follow ∧ s2 = alwaysAct) := by
  rcases strict_equilibrium_classification alpha beta rho reward cost halpha hbeta horder
      hreward hcost hrho0 hrhoa hrhob s1 s2 hnash with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- nobody acts: Firm 1 would want to act alone after `A`
    exfalso
    have hg := gain1_neg_of_abstain hnash (show s1 true = false by rw [h1]; rfl)
    rw [h2, soloGain1] at hg
    linarith
  · -- `A → 1, a → 0`: the secondary firm's two constraints contradict the window
    exfalso
    have hga := gain2_neg_of_abstain hnash (show s2 true = false by rw [h2]; rfl)
    have hgb := gain2_neg_of_abstain hnash (show s2 false = false by rw [h2]; rfl)
    rw [h1, gain2_follow_true] at hga
    rw [h1, gain2_follow_false] at hgb
    linarith
  · -- `A → 0, a → 1`: Firm 1 abstaining after `A` forces the positive row sum negative
    exfalso
    have hg := gain1_neg_of_abstain hnash (show s1 true = false by rw [h1]; rfl)
    rw [h2, gain1_follow_true, score_tt_eq] at hg
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ reward - cost) (by linarith : (0:ℝ) ≤ beta - rho),
      mul_nonneg hreward (by linarith : (0:ℝ) ≤ alpha - beta)]
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · -- everybody always acts: Firm 1 would not act after `B`
    exfalso
    have h2' : s2 = alwaysAct := h2
    have hg := gain1_pos_of_act hnash (show s1 false = true by rw [h1])
    rw [h2', gain1_alwaysAct_false] at hg
    linarith

/-! ### The diagonal score is affine, hence commutes with the prior mixture -/

/-- `W(A,a)` is an affine function of the correlation cell, so its value at the prior
mixture is the prior average of its values across the worlds. -/
theorem score_tt_mixture {W : Type} [Fintype W] (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta rhoBar reward cost : ℝ)
    (hbar : rhoBar = ∑ w, prior.mass w * rho w) :
    weightedSharedScore alpha beta rhoBar reward cost true true =
      ∑ w, prior.mass w * weightedSharedScore alpha beta (rho w) reward cost true true := by
  simp only [score_tt_eq]
  have h : ∑ w, prior.mass w * (reward * rho w - cost * (1 - alpha - beta + rho w)) =
      (reward - cost) * (∑ w, prior.mass w * rho w) -
        (cost * (1 - alpha - beta)) * (∑ w, prior.mass w) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [h, prior.total, hbar]
  ring

/-- Firm 1's ex-ante payoff in the `A → 1, a → 1` pattern is affine in the correlation
cell, so it too commutes with the prior mixture. -/
theorem payoff1_follow_follow_mixture {W : Type} [Fintype W] (prior : FiniteLaw W)
    (rho : W → ℝ) (alpha beta rhoBar reward cost : ℝ)
    (hbar : rhoBar = ∑ w, prior.mass w * rho w) :
    ∑ w, prior.mass w *
        weightedNoSharingPayoff1 alpha beta (rho w) reward cost follow follow =
      weightedNoSharingPayoff1 alpha beta rhoBar reward cost follow follow := by
  simp only [payoff1_follow_follow]
  rw [score_tt_mixture prior rho alpha beta rhoBar reward cost hbar]
  calc ∑ w, prior.mass w * ((reward * alpha - cost * (1 - alpha)) / 2 -
          weightedSharedScore alpha beta (rho w) reward cost true true / 4)
      = ∑ w, ((reward * alpha - cost * (1 - alpha)) / 2 * prior.mass w -
          prior.mass w * weightedSharedScore alpha beta (rho w) reward cost true true / 4) :=
        Finset.sum_congr rfl fun w _ => by ring
    _ = (reward * alpha - cost * (1 - alpha)) / 2 * (∑ w, prior.mass w) -
          (∑ w, prior.mass w * weightedSharedScore alpha beta (rho w) reward cost true true) / 4 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    _ = _ := by rw [prior.total]; ring

/-! ### The `A → 1, a → 1, b → 1` worlds carry no prior probability -/

/-- **Firm 1 strictly loses from an `A → 1, a → 1, b → 1` world.**

If every world is either `A → 1, a → 1` or `A → 1, a → 1, b → 1`, if the no-sharing
equilibrium at the prior mixture is `A → 1, a → 1`, and if train sharing does not lower
Firm 1's ex-ante payoff, then every `A → 1, a → 1, b → 1` world carries prior probability
zero.  Indeed Firm 1's payoff in such a world is smaller than in the `A → 1, a → 1`
pattern by exactly `W(A,b)/4 > 0`, while the `A → 1, a → 1` payoff is affine in the
correlation cell and therefore averages to its value at the mixture. -/
theorem followAlways_worlds_null {W : Type} [Fintype W] (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta rhoBar reward cost : ℝ)
    (hbar : rhoBar = ∑ w, prior.mass w * rho w)
    (t1 t2 : W → Bool → Bool)
    (hpat : ∀ w, (t1 w = follow ∧ t2 w = follow) ∨ (t1 w = follow ∧ t2 w = alwaysAct))
    (hWab : ∀ w, t2 w = alwaysAct →
      0 < weightedSharedScore alpha beta (rho w) reward cost true false)
    (hdom1 : weightedNoSharingPayoff1 alpha beta rhoBar reward cost follow follow ≤
      ∑ w, prior.mass w * weightedNoSharingPayoff1 alpha beta (rho w) reward cost
        (t1 w) (t2 w)) :
    ∀ w, t2 w = alwaysAct → prior.mass w = 0 := by
  -- the gap is `W(A,b)/4` in a `A → 1, a → 1, b → 1` world and zero otherwise
  have hgap : ∀ w, weightedNoSharingPayoff1 alpha beta (rho w) reward cost follow follow -
      weightedNoSharingPayoff1 alpha beta (rho w) reward cost (t1 w) (t2 w) =
      if t2 w = alwaysAct then
        weightedSharedScore alpha beta (rho w) reward cost true false / 4 else 0 := by
    intro w
    rcases hpat w with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hne : ¬ (t2 w = alwaysAct) := by
        rw [h2]; intro hcon; exact absurd (congrFun hcon false) (by decide)
      rw [if_neg hne, h1, h2]; ring
    · rw [if_pos h2, h1, h2, payoff1_follow_follow, payoff1_follow_alwaysAct]
      have := score_row_true alpha beta (rho w) reward cost
      linarith
  have hnonneg : ∀ w, 0 ≤ prior.mass w *
      (weightedNoSharingPayoff1 alpha beta (rho w) reward cost follow follow -
        weightedNoSharingPayoff1 alpha beta (rho w) reward cost (t1 w) (t2 w)) := by
    intro w
    refine mul_nonneg (prior.nonneg w) ?_
    rw [hgap w]
    split_ifs with h
    · linarith [hWab w h]
    · exact le_refl 0
  have hsum : ∑ w, prior.mass w *
      (weightedNoSharingPayoff1 alpha beta (rho w) reward cost follow follow -
        weightedNoSharingPayoff1 alpha beta (rho w) reward cost (t1 w) (t2 w)) ≤ 0 := by
    have hsplit : ∑ w, prior.mass w *
        (weightedNoSharingPayoff1 alpha beta (rho w) reward cost follow follow -
          weightedNoSharingPayoff1 alpha beta (rho w) reward cost (t1 w) (t2 w)) =
        (∑ w, prior.mass w *
          weightedNoSharingPayoff1 alpha beta (rho w) reward cost follow follow) -
        ∑ w, prior.mass w *
          weightedNoSharingPayoff1 alpha beta (rho w) reward cost (t1 w) (t2 w) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hsplit, payoff1_follow_follow_mixture prior rho alpha beta rhoBar reward cost hbar]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun w (_ : w ∈ Finset.univ) => hnonneg w)).mp
    (le_antisymm hsum (Finset.sum_nonneg fun w _ => hnonneg w))
  intro w hw
  have h := hzero w (Finset.mem_univ w)
  rw [hgap w, if_pos hw] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (by linarith [hWab w hw])

/-! ### The transfer theorem for a `A → 1, a → 1, b → 1` world -/

/-- **Theorem 4.6(1) when some world is `A → 1, a → 1, b → 1`.**

Standing assumptions of Section 3; the no-sharing game is played at the prior mixture
`rhoBar`; the selected no-sharing profile and every selected world profile are strict
equilibria; train sharing does not lower Firm 1's ex-ante payoff; the secondary firm never
acts *only* after its negative inference signal (non-inversion); and in one world
the selected profile is `A → 1, a → 1, b → 1`.

Then the normalized opportunity-seeking consumer weakly prefers the no-sharing
equilibrium.  Nothing is assumed about the no-sharing pattern, and the conclusion is the
*selected*-equilibrium form of conclusion (1). -/
theorem tradeProbability_transfer_of_followAlways_world
    {W : Type} [Fintype W] (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (alpha beta rhoBar reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ (parameters w).jointTT)
    (hrhoa : ∀ w, (parameters w).jointTT ≤ alpha)
    (hrhob : ∀ w, (parameters w).jointTT ≤ beta)
    (hbar0 : 0 ≤ rhoBar) (hbara : rhoBar ≤ alpha) (hbarb : rhoBar ≤ beta)
    (hbar : rhoBar = ∑ w, prior.mass w * (parameters w).jointTT)
    (n1 n2 : Bool → Bool) (t1 t2 : W → Bool → Bool)
    (hno : IsStrictWeightedNash alpha beta rhoBar reward cost n1 n2)
    (htrain : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (t1 w) (t2 w))
    (hnonInverted : NonInverted t2)
    (w0 : W) (h01 : t1 w0 = follow) (h02 : t2 w0 = alwaysAct)
    (hdom1 : weightedNoSharingPayoff1 alpha beta rhoBar reward cost n1 n2 ≤
      ∑ w, prior.mass w * weightedNoSharingPayoff1 alpha beta ((parameters w).jointTT)
        reward cost (t1 w) (t2 w)) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
  -- the correlation-free consequences of the exceptional world
  have h0 : IsStrictWeightedNash alpha beta ((parameters w0).jointTT) reward cost
      follow alwaysAct := by
    have h := htrain w0; rwa [h01, h02] at h
  obtain ⟨hrowT, hrowF, hcolT0, hcolF0, hRC, hWab0⟩ :=
    followAlways_facts alpha beta ((parameters w0).jointTT) reward cost (hrhoa w0) (hrhob w0) h0
  have hwindow : (reward * alpha - cost * (1 - alpha)) -
      2 * (reward * (1 - beta) - cost * beta) < 2 * (reward * beta - cost * (1 - beta)) := by
    linarith
  -- every world is `A → 1, a → 1` or `A → 1, a → 1, b → 1`
  have hpat : ∀ w, (t1 w = follow ∧ t2 w = follow) ∨ (t1 w = follow ∧ t2 w = alwaysAct) := by
    intro w
    rcases classification_of_followAlways_facts alpha beta ((parameters w).jointTT) reward
        cost halpha hbeta horder hreward hcost (hrho0 w) (hrhoa w) (hrhob w) hrowF hwindow
        (t1 w) (t2 w) (htrain w) with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨ha, hb⟩
    · exfalso
      have hact := hnonInverted w (by rw [hb]; rfl)
      rw [hb] at hact
      exact absurd hact (by decide)
    · exact Or.inr ⟨ha, hb⟩
  -- the exceptional worlds all have a positive `W(A,b)`
  have hWab : ∀ w, t2 w = alwaysAct →
      0 < weightedSharedScore alpha beta ((parameters w).jointTT) reward cost true false := by
    intro w hw
    have hfw : t1 w = follow := by
      rcases hpat w with ⟨ha, _⟩ | ⟨ha, _⟩ <;> exact ha
    have hn : IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
        follow alwaysAct := by
      have h := htrain w; rwa [hfw, hw] at h
    exact (followAlways_facts alpha beta ((parameters w).jointTT) reward cost (hrhoa w)
      (hrhob w) hn).2.2.2.2.2
  -- every world has its diagonal score below twice the positive column sum
  have hlt : ∀ w, weightedSharedScore alpha beta ((parameters w).jointTT) reward cost
      true true ≤ 2 * (reward * beta - cost * (1 - beta)) := by
    intro w
    rcases hpat w with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      exact le_of_lt (score_tt_lt_two_colTrue alpha beta ((parameters w).jointTT) reward cost
        (t2 w) (by rw [← ha]; exact htrain w) (by rw [hb]; rfl))
  rcases classification_of_followAlways_facts alpha beta rhoBar reward cost halpha hbeta
      horder hreward hcost hbar0 hbara hbarb hrowF hwindow n1 n2 hno with
      ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
  · -- the no-sharing equilibrium is `A → 1, a → 1`: the exceptional worlds are null
    rw [hn1, hn2] at hdom1
    have hnull := followAlways_worlds_null prior (fun w => (parameters w).jointTT) alpha beta
      rhoBar reward cost hbar t1 t2 hpat hWab hdom1
    simp only [correlationEventProbability]
    refine le_of_eq (Finset.sum_congr rfl fun w _ => ?_)
    by_cases hm : prior.mass w = 0
    · rw [hm]; ring
    · rcases hpat w with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb, hn1, hn2]
      · exact absurd (hnull w hb) hm
  · -- the no-sharing equilibrium cannot be `A → 1, b → 1`
    exfalso
    have hmixle : weightedSharedScore alpha beta rhoBar reward cost true true ≤
        2 * (reward * beta - cost * (1 - beta)) := by
      rw [score_tt_mixture prior (fun w => (parameters w).jointTT) alpha beta rhoBar reward
        cost hbar]
      calc ∑ w, prior.mass w *
            weightedSharedScore alpha beta ((parameters w).jointTT) reward cost true true
          ≤ ∑ w, prior.mass w * (2 * (reward * beta - cost * (1 - beta))) :=
            Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hlt w) (prior.nonneg w)
        _ = 2 * (reward * beta - cost * (1 - beta)) := by
            rw [← Finset.sum_mul, prior.total]; ring
    have hg := gain2_neg_of_abstain hno (show n2 true = false by rw [hn2]; rfl)
    rw [hn1, gain2_follow_true] at hg
    linarith
  · -- the no-sharing equilibrium is `A → 1, a → 1, b → 1`: it always trades
    refine correlationTradeProbability_transfer prior _ t1 t2 n1 n2 fun w q _ => ?_
    simp [TrainSharing.Theorem43.tradeEvent, hn2]

/-! ## 3.  Reading the pattern off the secondary firm's behaviour -/

/-- If the secondary firm acts after **both** of its signals, and the primary firm does not
act after `B`, the pattern is `A → 1, a → 1, b → 1`. -/
theorem followAlways_of_acts_after_b
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (ha : s2 true = true) (hb : s2 false = true) (h1 : s1 false = false) :
    s1 = follow ∧ s2 = alwaysAct := by
  rcases strict_equilibrium_classification alpha beta rho reward cost halpha hbeta horder
      hreward hcost hrho0 hrhoa hrhob s1 s2 hnash with
      ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
  · rw [ha2] at hb; exact absurd hb (by decide)
  · rw [ha2] at hb; exact absurd hb (by decide)
  · rw [ha2] at hb; exact absurd hb (by decide)
  · rw [ha2] at hb; exact absurd hb (by decide)
  · rw [ha2] at ha; exact absurd ha (by decide)
  · exact ⟨ha1, ha2⟩
  · rw [ha1] at h1; exact absurd h1 (by decide)

/-- If the primary firm acts after its **negative** signal, everybody always acts. -/
theorem alwaysAct_of_acts_after_B
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (h1 : s1 false = true) :
    s1 = alwaysAct ∧ s2 = alwaysAct := by
  rcases strict_equilibrium_classification alpha beta rho reward cost halpha hbeta horder
      hreward hcost hrho0 hrhoa hrhob s1 s2 hnash with
      ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
  · rw [ha1] at h1; exact absurd h1 (by decide)
  · rw [ha1] at h1; exact absurd h1 (by decide)
  · rw [ha1] at h1; exact absurd h1 (by decide)
  · rw [ha1] at h1; exact absurd h1 (by decide)
  · rw [ha1] at h1; exact absurd h1 (by decide)
  · rw [ha1] at h1; exact absurd h1 (by decide)
  · exact ⟨ha1, ha2⟩

/-- An event that always occurs has probability one. -/
theorem preferredProbability_of_always {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (event : Ω → Bool) (h : ∀ q, event q = true) : preferredProbability law event = 1 := by
  simp only [preferredProbability, h, if_true, mul_one]
  exact law.total

/-- The all-acting profile trades with ex-ante probability one. -/
theorem correlationEventProbability_alwaysAct {W : Type} [Fintype W] (prior : FiniteLaw W)
    (law : W → FiniteLaw (Bool × Bool)) :
    correlationEventProbability prior law
      (fun _ => TrainSharing.Theorem43.tradeEvent alwaysAct alwaysAct) = 1 := by
  simp only [correlationEventProbability,
    preferredProbability_of_always _ _ tradeEvent_alwaysAct, mul_one]
  exact prior.total

/-! ## 4.  Theorem 4.6(1) under non-inversion -/

section

variable {W : Type} [Fintype W]
variable (prior : FiniteLaw W)
variable (parameters : W → TrainSharing.Correlation.Parameters)
variable (feasible : ∀ w, (parameters w).Feasible)
variable (S : EquilibriumSelection W)
variable (alpha beta rhoBar reward cost : ℝ)

omit [Fintype W] in
/-- Feasibility of each world's correlation cell, in the four-inequality form. -/
theorem worldCellBounds
    (feasible : ∀ w, (parameters w).Feasible)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta) :
    (∀ w, 0 ≤ (parameters w).jointTT) ∧ (∀ w, (parameters w).jointTT ≤ alpha) ∧
      (∀ w, (parameters w).jointTT ≤ beta) ∧
      (∀ w, 0 ≤ 1 - alpha - beta + (parameters w).jointTT) := by
  refine ⟨fun w => le_trans (le_max_left _ _) (feasible w).1, fun w => ?_, fun w => ?_,
    fun w => ?_⟩
  · have h := le_trans (feasible w).2 (min_le_left _ _)
    rw [halphaw w] at h
    exact h
  · have h := le_trans (feasible w).2 (min_le_right _ _)
    rw [hbetaw w] at h
    exact h
  · have h := le_trans (le_max_right (0 : ℝ)
      ((parameters w).alpha + (parameters w).beta - 1)) (feasible w).1
    rw [halphaw w, hbetaw w] at h
    linarith

/-- **Theorem 4.6(1), non-inverted equilibrium, no all-acting world.**

The hypotheses are those of `Theorem46Parts.part1_transfer_of_monotone_worlds` except that

> in no correlation world does the secondary firm take the significant action after its own
> negative inference signal

is replaced by the strictly weaker pair

* the train-sharing equilibrium is not inverted (Definition 4.5): the secondary firm never
  acts after `b` *without* also acting after `a`, i.e. the world pattern `A → 1, b → 1`
  never occurs — this is the assumption of Theorem 4.6, and Example 4.7 shows it cannot be
  dropped — and
* no world is all-acting: the primary firm never acts after `B`.

In particular the pattern `A → 1, a → 1, b → 1` is *allowed*: it is handled by
`tradeProbability_transfer_of_followAlways_world`, at the cost of no extra assumption.
The conclusion is the selected-equilibrium form of Theorem 4.6(1). -/
theorem theorem4_6_part1_nonInverted
    (hunique : TrainSharing.Theorem46.Selected.IsUniquelyIRPO S Contract.trainSharing)
    (hmodel : Parts.ModelPayoffs S prior parameters alpha beta rhoBar reward cost)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta)
    (hnoNash : IsStrictWeightedNash alpha beta rhoBar reward cost S.noFirm1 S.noFirm2)
    (htrainNash : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (S.trainFirm1 w) (S.trainFirm2 w))
    (hnonInverted : NonInverted S.trainFirm2)
    (hnotAll : ∀ w, S.trainFirm1 w false = false) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (S.event .trainSharing) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (S.event .noSharing) := by
  obtain ⟨hrho0, hrhoa, hrhob, hrho1⟩ :=
    worldCellBounds parameters alpha beta feasible halphaw hbetaw
  obtain ⟨hbar0, hbara, hbarb, hbar1⟩ :=
    mixture_feasible prior (fun w => (parameters w).jointTT) alpha beta rhoBar hrho0 hrhoa
      hrhob hrho1 hmodel.mixture
  by_cases hmono : ∀ w, S.trainFirm2 w false = false
  · exact Parts.part1_transfer_of_monotone_worlds prior parameters feasible S alpha beta rhoBar
      reward cost hunique hmodel halpha hbeta horder hreward hcost halphaw hbetaw hnoNash
      htrainNash hmono
  · push_neg at hmono
    obtain ⟨w0, hw0⟩ := hmono
    have hw0' : S.trainFirm2 w0 false = true := by
      cases h : S.trainFirm2 w0 false
      · exact absurd h hw0
      · rfl
    obtain ⟨h01, h02⟩ := followAlways_of_acts_after_b alpha beta ((parameters w0).jointTT)
      reward cost halpha hbeta horder hreward hcost (hrho0 w0) (hrhoa w0) (hrhob w0)
      (S.trainFirm1 w0) (S.trainFirm2 w0) (htrainNash w0) (hnonInverted w0 hw0') hw0' (hnotAll w0)
    -- literal unique IRPO gives Pareto dominance over no sharing
    have hpareto : TrainSharing.Theorem46.Selected.ParetoDominates S Contract.trainSharing
        Contract.noSharing := by
      rcases hunique.1.1 with h | h
      · exact absurd h (by decide)
      · exact h
    have hdom1 := hpareto Firm.firm1
    rw [hmodel.noSharing1, hmodel.train1] at hdom1
    rw [S.train_event, S.no_event]
    exact tradeProbability_transfer_of_followAlways_world prior parameters feasible alpha
      beta rhoBar reward cost halpha hbeta horder hreward hcost hrho0 hrhoa hrhob hbar0
      hbara hbarb hmodel.mixture S.noFirm1 S.noFirm2 S.trainFirm1 S.trainFirm2 hnoNash
      htrainNash hnonInverted w0 h01 h02 hdom1

/-- **Theorem 4.6(1), existential form.**

With the train-sharing equilibrium not inverted, and with *nothing at all*
assumed about the all-acting worlds, there is a strict equilibrium of the no-sharing game
at the prior mixture that the consumer weakly prefers to train sharing.

If no world is all-acting the witness is the selected no-sharing equilibrium, by
`theorem4_6_part1_nonInverted`.  If some world is all-acting then — because the four
incentive constraints of the all-acting profile are the correlation-free row and column
sums — the all-acting profile is a strict equilibrium of the no-sharing game as well, and
it trades with probability one. -/
theorem theorem4_6_part1_existence_nonInverted
    (hunique : TrainSharing.Theorem46.Selected.IsUniquelyIRPO S Contract.trainSharing)
    (hmodel : Parts.ModelPayoffs S prior parameters alpha beta rhoBar reward cost)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta)
    (hnoNash : IsStrictWeightedNash alpha beta rhoBar reward cost S.noFirm1 S.noFirm2)
    (htrainNash : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (S.trainFirm1 w) (S.trainFirm2 w))
    (hnonInverted : NonInverted S.trainFirm2) :
    ∃ n1 n2 : Bool → Bool,
      IsStrictWeightedNash alpha beta rhoBar reward cost n1 n2 ∧
      correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event .trainSharing) ≤
        correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
  obtain ⟨hrho0, hrhoa, hrhob, hrho1⟩ :=
    worldCellBounds parameters alpha beta feasible halphaw hbetaw
  by_cases hall : ∀ w, S.trainFirm1 w false = false
  · refine ⟨S.noFirm1, S.noFirm2, hnoNash, ?_⟩
    have h := theorem4_6_part1_nonInverted prior parameters feasible S alpha beta
      rhoBar reward cost hunique hmodel halpha hbeta horder hreward hcost halphaw hbetaw
      hnoNash htrainNash hnonInverted hall
    rwa [S.no_event] at h
  · push_neg at hall
    obtain ⟨w0, hw0⟩ := hall
    have hw0' : S.trainFirm1 w0 false = true := by
      cases h : S.trainFirm1 w0 false
      · exact absurd h hw0
      · rfl
    obtain ⟨h01, h02⟩ := alwaysAct_of_acts_after_B alpha beta ((parameters w0).jointTT)
      reward cost halpha hbeta horder hreward hcost (hrho0 w0) (hrhoa w0) (hrhob w0)
      (S.trainFirm1 w0) (S.trainFirm2 w0) (htrainNash w0) hw0'
    refine ⟨alwaysAct, alwaysAct, ?_, ?_⟩
    · refine alwaysAct_strict_of_strict alpha beta ((parameters w0).jointTT) rhoBar reward
        cost ?_
      have h := htrainNash w0; rwa [h01, h02] at h
    · rw [correlationEventProbability_alwaysAct]
      exact correlationEventProbability_le_one prior _ _

/-- **Theorem 4.6(1) as a dichotomy against Definition 4.5.**

Dropping the non-inversion hypothesis from `theorem4_6_part1_existence_nonInverted`, what
remains is that *either* conclusion (1) holds in its existential reading, *or* the
train-sharing equilibrium is inverted in the sense of Definition 4.5.  Example 4.7 realises
the second alternative, so neither disjunct can be dropped. -/
theorem theorem4_6_part1_or_inverted
    (hunique : TrainSharing.Theorem46.Selected.IsUniquelyIRPO S Contract.trainSharing)
    (hmodel : Parts.ModelPayoffs S prior parameters alpha beta rhoBar reward cost)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta)
    (hnoNash : IsStrictWeightedNash alpha beta rhoBar reward cost S.noFirm1 S.noFirm2)
    (htrainNash : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (S.trainFirm1 w) (S.trainFirm2 w)) :
    (∃ n1 n2 : Bool → Bool,
      IsStrictWeightedNash alpha beta rhoBar reward cost n1 n2 ∧
      correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event .trainSharing) ≤
        correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2)) ∨
      Inverted S.trainFirm2 := by
  by_cases h : NonInverted S.trainFirm2
  · exact Or.inl (theorem4_6_part1_existence_nonInverted prior parameters feasible S alpha
      beta rhoBar reward cost hunique hmodel halpha hbeta horder hreward hcost halphaw
      hbetaw hnoNash htrainNash h)
  · refine Or.inr ?_
    by_contra hinv
    exact h ((nonInverted_iff_not_inverted _).mpr hinv)

end

end TrainSharing.Theorem46.Part1

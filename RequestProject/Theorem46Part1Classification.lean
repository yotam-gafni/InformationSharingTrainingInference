import RequestProject.Theorem46UpperBound

/-!
# Strict-equilibrium classification and the trade-event transfer

The proof of Theorem 4.6(1) in the manuscript rests on a transfer:

> every train-sharing trade event is contained in the trade event of the no-sharing
> equilibrium.

This file establishes that transfer inside the significant-action correlation model of
Section 3, for `alpha ≥ beta ≥ 1/2` and `R₁, C₁ ≥ 0`, and classifies the strict
equilibria that can occur.  Its main results are used by
`Theorem46Part1Transfer.lean` and, through it, by the proof of Theorem 4.6(1) under the
manuscript's non-inversion assumption.

* `tradeEvent_transfer_of_monotone_patterns` proves the transfer under two conditions on the
  *equilibrium patterns*:
  * `PositiveSignalsAgree`: under no sharing the two firms agree about acting after their
    positive signals — either both of `A → 1` and `a → 1` hold, or neither does;
  * `NoNegativeSignalAction`: in the revealed world no firm takes the significant action
    after its own *negative* signal (`B → 0` and `b → 0`).  This is exactly the
    monotonicity that the manuscript's proof takes for granted, and it is what an
    inverted equilibrium (Definition 4.5) violates.

  The first condition is removed in `Theorem46Part1Transfer.lean`, and the second is
  weakened there to non-inversion.

* `strict_equilibrium_classification` lists the seven equilibrium patterns that can occur
  at all.

Two structural lemmas of independent interest are proved on the way, both under the
standing assumptions only:

* `firm1_inactive_after_B_of_inactive_after_A`: the *primary* firm is always monotone in
  its own signal — no strict equilibrium has Firm 1 acting after `B` but not after `A`.
  (The corresponding statement for Firm 2 is false: that failure is precisely an inverted
  equilibrium, realized by Example 4.7.)
* `trivial_of_positives_inactive`: if at a strict equilibrium neither firm acts after its
  positive signal, the equilibrium is completely inactive.
-/

namespace TrainSharing.Theorem46.Classification

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected
open TrainSharing.Theorem46.Upper

/-! ## The two equilibrium-pattern conditions -/

/-- The two firms agree about acting after their positive signals: `A → 1` holds if and
only if `a → 1` does. -/
def PositiveSignalsAgree (s1 s2 : Bool → Bool) : Prop := s1 true = s2 true

/-- No firm takes the significant action after its own negative signal: `B → 0` and
`b → 0`. -/
def NoNegativeSignalAction (s1 s2 : Bool → Bool) : Prop :=
  s1 false = false ∧ s2 false = false

/-! ## Monotonicity of the primary firm

Firm 2 can act after its negative signal only (this is the inverted pattern), but Firm 1
never can: if the more accurate firm stays out after `A`, it stays out after `B` as
well. -/

/-- If the reward dominates the mistake cost, both significant-action scores in Firm 1's
positive row are nonnegative: `W(A,a) = (R₁-C₁)ρ + C₁(α+β-1)` and
`W(A,b) = (R₁-C₁)(α-ρ) + C₁(α-β)`. -/
theorem score_row_true_nonneg (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hcost : 0 ≤ cost) (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha)
    (hRC : cost ≤ reward) :
    0 ≤ weightedSharedScore alpha beta rho reward cost true true ∧
      0 ≤ weightedSharedScore alpha beta rho reward cost true false := by
  constructor <;> simp only [weightedSharedScore, conditionalMass] <;> norm_num <;>
    nlinarith [mul_nonneg hcost (by linarith : (0:ℝ) ≤ alpha + beta - 1),
      mul_nonneg (by linarith : (0:ℝ) ≤ reward - cost) hrho0,
      mul_nonneg (by linarith : (0:ℝ) ≤ reward - cost) (by linarith : (0:ℝ) ≤ alpha - rho),
      mul_nonneg hcost (by linarith : (0:ℝ) ≤ alpha - beta)]

/-- If the mistake cost dominates the reward, both significant-action scores in Firm 1's
negative row are nonpositive: `W(B,a) = (R₁-C₁)(β-ρ) - C₁(α-β)` and
`W(B,b) = R₁(1-α-β) + (R₁-C₁)ρ`. -/
theorem score_row_false_nonpos (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost) (hrho0 : 0 ≤ rho) (hrhob : rho ≤ beta)
    (hRC : reward ≤ cost) :
    weightedSharedScore alpha beta rho reward cost false true ≤ 0 ∧
      weightedSharedScore alpha beta rho reward cost false false ≤ 0 := by
  constructor <;> simp only [weightedSharedScore, conditionalMass] <;> norm_num <;>
    nlinarith [mul_nonneg hcost (by linarith : (0:ℝ) ≤ alpha - beta),
      mul_nonneg (by linarith : (0:ℝ) ≤ cost - reward) hrho0,
      mul_nonneg (by linarith : (0:ℝ) ≤ cost - reward) (by linarith : (0:ℝ) ≤ beta - rho),
      mul_nonneg hreward (by linarith : (0:ℝ) ≤ alpha + beta - 1)]

/-- **Firm 1 is monotone in its own signal.**  At a strict equilibrium of the weighted
significant-action model with `alpha ≥ beta ≥ 1/2` and nonnegative reward and mistake
cost, if Firm 1 does not act after its positive signal then it does not act after its
negative signal either.

The reason is that Firm 1's positive row of scores is nonnegative whenever
`R₁ ≥ C₁`, and its negative row is nonpositive whenever `R₁ ≤ C₁`: in the first case
Firm 1 wants to act after `A` against *any* behaviour of Firm 2, in the second it never
wants to act after `B`.  The analogous statement for Firm 2 is false — that failure is
the inverted pattern of Definition 4.5, realised by Example 4.7. -/
theorem firm1_inactive_after_B_of_inactive_after_A
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hA : s1 true = false) : s1 false = false := by
  by_contra hB
  have hBtrue : s1 false = true := by
    cases h : s1 false
    · exact absurd h hB
    · rfl
  -- Firm 1 strictly prefers to stay out after `A` and to act after `B`.
  have hgA : weightedFirm1Gain alpha beta rho reward cost s2 true < 0 := by
    have h := hnash.1 true
    rw [hA] at h
    simpa using h
  have hgB : 0 < weightedFirm1Gain alpha beta rho reward cost s2 false := by
    have h := hnash.1 false
    rw [hBtrue] at h
    simpa using h
  rw [weightedFirm1Gain_eq] at hgA
  rw [weightedFirm1Gain_eq] at hgB
  have hsa := shareFactor_pos (s2 true)
  have hsb := shareFactor_pos (s2 false)
  rcases le_total cost reward with hRC | hRC
  · obtain ⟨h1, h2⟩ := score_row_true_nonneg alpha beta rho reward cost halpha hbeta
      horder hcost hrho0 hrhoa hRC
    nlinarith [mul_nonneg h1 (le_of_lt hsa), mul_nonneg h2 (le_of_lt hsb)]
  · obtain ⟨h1, h2⟩ := score_row_false_nonpos alpha beta rho reward cost halpha hbeta
      horder hreward hcost hrho0 hrhob hRC
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hsa),
      mul_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hsb)]

/-- If Firm 1 is completely inactive and Firm 2 stays out after its positive signal, then
Firm 2 stays out after its negative signal too: with an inactive rival both interim gains
are the correlation-free solo gains, and the negative one is the smaller. -/
theorem firm2_inactive_after_b_of_inactive_after_a
    (alpha beta rho reward cost : ℝ)
    (hbeta : 1 / 2 ≤ beta) (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (h1 : s1 = inactive) (ha : s2 true = false) : s2 false = false := by
  by_contra hb
  have hbtrue : s2 false = true := by
    cases h : s2 false
    · exact absurd h hb
    · rfl
  have hga : weightedFirm2Gain alpha beta rho reward cost inactive true < 0 := by
    have h := hnash.2 true
    rw [ha, h1] at h
    simpa using h
  have hgb : 0 < weightedFirm2Gain alpha beta rho reward cost inactive false := by
    have h := hnash.2 false
    rw [hbtrue, h1] at h
    simpa using h
  rw [soloGain2] at hga
  rw [soloGain2_false] at hgb
  -- the solo gain after the negative signal is the smaller of the two
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ reward + cost)
    (by linarith : (0:ℝ) ≤ 2 * beta - 1)]

/-- **If neither firm acts after its positive signal, nobody acts at all.** -/
theorem trivial_of_positives_inactive
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hA : s1 true = false) (ha : s2 true = false) :
    TrivialProfile s1 s2 := by
  have hB : s1 false = false :=
    firm1_inactive_after_B_of_inactive_after_A alpha beta rho reward cost halpha hbeta
      horder hreward hcost hrho0 hrhoa hrhob s1 s2 hnash hA
  have h1 : s1 = inactive := by
    funext x; cases x
    · exact hB
    · exact hA
  have hb : s2 false = false :=
    firm2_inactive_after_b_of_inactive_after_a alpha beta rho reward cost hbeta hreward
      hcost s1 s2 hnash h1 ha
  refine ⟨fun x => ?_, fun y => ?_⟩
  · cases x
    · exact hB
    · exact hA
  · cases y
    · exact hb
    · exact ha

/-- The solo gains read off an inactive strict equilibrium: if neither firm acts, then
acting alone after the positive signal is unprofitable for both firms.  Both quantities
are correlation free. -/
theorem solo_gains_nonpos_of_trivial
    (alpha beta rho reward cost : ℝ)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (htriv : TrivialProfile s1 s2) :
    weightedFirm1Gain alpha beta rho reward cost inactive true ≤ 0 ∧
      weightedFirm2Gain alpha beta rho reward cost inactive true ≤ 0 := by
  have h2 : s2 = inactive := funext fun y => htriv.2 y
  have h1 : s1 = inactive := funext fun x => htriv.1 x
  constructor
  · have := hnash.1 true
    rw [htriv.1 true] at this
    rw [h2] at this
    simpa using le_of_lt this
  · have := hnash.2 true
    rw [htriv.2 true] at this
    rw [h1] at this
    simpa using le_of_lt this

/-! ## The complete list of strict equilibrium patterns

The manuscript's proof of Theorem 4.6(1) enumerates the possible no-sharing equilibria as
"nobody acts", "`A → 1, a → 0`", "`A → 1, a → 1`", and "everything else has trade
probability one".  The classification below shows that the list is incomplete: exactly
seven patterns can occur, and two of the seven — the secondary firm acting alone
(`A → 0, a → 1`) and the non-monotone `A → 1, b → 1` — are neither in the manuscript's
list nor of trade probability one. -/

/-- Two binary action rules agree once they agree at both signals. -/
theorem strategy_ext {s t : Bool → Bool}
    (ht : s true = t true) (hf : s false = t false) : s = t := by
  funext y
  cases y
  · exact hf
  · exact ht

/-- If Firm 1 is inactive, Firm 2 cannot act after both signals: acting after `a` alone is
already profitable then, which contradicts Firm 1's staying out after `A`. -/
theorem no_inactive_firm1_with_fully_active_firm2
    (alpha beta rho reward cost : ℝ) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (h1 : s1 = inactive) (ha : s2 true = true) (hb : s2 false = true) : False := by
  have hgA : weightedFirm1Gain alpha beta rho reward cost s2 true < 0 := by
    have h := hnash.1 true
    rw [h1] at h
    simpa [inactive] using h
  have hga : 0 < weightedFirm2Gain alpha beta rho reward cost inactive true := by
    have h := hnash.2 true
    rw [ha, h1] at h
    simpa using h
  rw [weightedFirm1Gain_eq, ha, hb] at hgA
  rw [soloGain2] at hga
  have hrow := score_row_true alpha beta rho reward cost
  simp only [shareFactor, if_true] at hgA
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ reward + cost)
    (by linarith : (0:ℝ) ≤ alpha - beta)]

/-- If Firm 1 always acts, Firm 2 must act after its positive signal. -/
theorem firm2_acts_after_a_of_firm1_always_acts
    (alpha beta rho reward cost : ℝ)
    (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (h1 : s1 = fun _ => true) : s2 true = true := by
  by_contra hcon
  have ha : s2 true = false := by
    cases h : s2 true
    · rfl
    · exact absurd h hcon
  -- Firm 2's two interim gains against an always-acting rival are the halved column sums
  have hga : weightedFirm2Gain alpha beta rho reward cost s1 true < 0 := by
    have h := hnash.2 true
    rw [ha] at h
    simpa using h
  rw [weightedFirm2Gain_eq, h1] at hga
  simp only [shareFactor, if_true] at hga
  have hcol := score_col_true alpha beta rho reward cost
  cases hb : s2 false with
  | false =>
      -- Firm 2 is inactive, so Firm 1's gain after `B` is the correlation-free solo gain
      have hgB : 0 < weightedFirm1Gain alpha beta rho reward cost s2 false := by
        have h := hnash.1 false
        rw [h1] at h
        simpa using h
      have hs2 : s2 = inactive := by
        funext y; cases y
        · exact hb
        · exact ha
      rw [hs2, soloGain1_false] at hgB
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ reward + cost)
        (by linarith : (0:ℝ) ≤ alpha + beta - 1)]
  | true =>
      have hgb : 0 < weightedFirm2Gain alpha beta rho reward cost s1 false := by
        have h := hnash.2 false
        rw [hb] at h
        simpa using h
      rw [weightedFirm2Gain_eq, h1] at hgb
      simp only [shareFactor, if_true] at hgb
      have hcol' := score_col_false alpha beta rho reward cost
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ reward + cost)
        (by linarith : (0:ℝ) ≤ 2 * beta - 1)]

/-- If Firm 1 always acts, Firm 2 must act after its negative signal too: the profile in
which Firm 1 always acts and Firm 2 follows its signal is never a strict equilibrium. -/
theorem firm2_acts_after_b_of_firm1_always_acts
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward)
    (hrho0 : 0 ≤ rho) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (h1 : s1 = fun _ => true) (ha : s2 true = true) : s2 false = true := by
  by_contra hcon
  have hb : s2 false = false := by
    cases h : s2 false
    · rfl
    · exact absurd h hcon
  have hgB : 0 < weightedFirm1Gain alpha beta rho reward cost s2 false := by
    have h := hnash.1 false
    rw [h1] at h
    simpa using h
  have hgb : weightedFirm2Gain alpha beta rho reward cost s1 false < 0 := by
    have h := hnash.2 false
    rw [hb] at h
    simpa using h
  rw [weightedFirm1Gain_eq, ha, hb] at hgB
  rw [weightedFirm2Gain_eq, h1] at hgb
  simp only [shareFactor, if_true] at hgB hgb
  simp only [weightedSharedScore, conditionalMass] at hgB hgb
  norm_num at hgB hgb
  nlinarith [mul_nonneg hreward (mul_nonneg (by linarith : (0:ℝ) ≤ alpha - beta)
      (by linarith : (0:ℝ) ≤ 1 + beta)),
    mul_nonneg hreward (mul_nonneg (by linarith : (0:ℝ) ≤ beta - rho)
      (by linarith : (0:ℝ) ≤ 2 * beta - 1)),
    mul_nonneg hreward hrho0]

/-- **Classification of the strict equilibria of the significant-action game.**

Under the standing assumptions `alpha ≥ beta ≥ 1/2`, `R₁, C₁ ≥ 0` and a feasible
correlation cell, a strict equilibrium must be one of the following seven patterns; the
other nine binary profiles are excluded:

| pattern | manuscript notation |
|---|---|
| `inactive, inactive` | nobody acts |
| `follow, inactive` | `A → 1, a → 0` |
| `inactive, follow` | `A → 0, a → 1` |
| `follow, follow` | `A → 1, a → 1` |
| `follow, antiFollow` | `A → 1, b → 1` |
| `follow, always` | `A → 1, a → 1, b → 1` |
| `always, always` | `A → 1, B → 1, a → 1, b → 1` |

In particular Firm 1 is always monotone in its own signal, and it never acts after `B`
unless it also acts after `A` *and* Firm 2 acts after both of its signals. -/
theorem strict_equilibrium_classification
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2) :
    (s1 = inactive ∧ s2 = inactive) ∨
    (s1 = follow ∧ s2 = inactive) ∨
    (s1 = inactive ∧ s2 = follow) ∨
    (s1 = follow ∧ s2 = follow) ∨
    (s1 = follow ∧ s2 = antiFollow) ∨
    (s1 = follow ∧ s2 = fun _ => true) ∨
    (s1 = (fun _ => true) ∧ s2 = fun _ => true) := by
  cases hA : s1 true with
  | false =>
      have hB : s1 false = false :=
        firm1_inactive_after_B_of_inactive_after_A alpha beta rho reward cost halpha hbeta
          horder hreward hcost hrho0 hrhoa hrhob s1 s2 hnash hA
      have h1 : s1 = inactive := strategy_ext hA hB
      cases ha : s2 true with
      | false =>
          have hb : s2 false = false :=
            firm2_inactive_after_b_of_inactive_after_a alpha beta rho reward cost hbeta
              hreward hcost s1 s2 hnash h1 ha
          exact Or.inl ⟨h1, strategy_ext ha hb⟩
      | true =>
          cases hb : s2 false with
          | false => exact Or.inr (Or.inr (Or.inl ⟨h1, strategy_ext ha hb⟩))
          | true =>
              exact absurd hb (fun hb' => no_inactive_firm1_with_fully_active_firm2 alpha
                beta rho reward cost horder hreward hcost s1 s2 hnash h1 ha hb')
  | true =>
      cases hB : s1 false with
      | false =>
          have h1 : s1 = follow := strategy_ext hA hB
          cases ha : s2 true with
          | false =>
              cases hb : s2 false with
              | false => exact Or.inr (Or.inl ⟨h1, strategy_ext ha hb⟩)
              | true =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, strategy_ext ha hb⟩))))
          | true =>
              cases hb : s2 false with
              | false => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, strategy_ext ha hb⟩)))
              | true =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl ⟨h1, strategy_ext ha hb⟩)))))
      | true =>
          have h1 : s1 = fun _ => true := strategy_ext hA hB
          have ha : s2 true = true :=
            firm2_acts_after_a_of_firm1_always_acts alpha beta rho reward cost hbeta horder
              hreward hcost s1 s2 hnash h1
          have hb : s2 false = true :=
            firm2_acts_after_b_of_firm1_always_acts alpha beta rho reward cost halpha hbeta
              horder hreward hrho0 hrhob s1 s2 hnash h1 ha
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨h1, strategy_ext ha hb⟩)))))

/-! ## The trade-event transfer -/

/-- **The trade-event transfer.**

Let the no-sharing profile `(n1, n2)` be a strict equilibrium of the game with
correlation cell `rhoBar`, and let `(t1, t2)` be a strict equilibrium of a revealed world
with correlation cell `rho`; both games share the accuracies `alpha ≥ beta ≥ 1/2` and the
utility parameters `reward, cost ≥ 0`.  Assume

* under no sharing the two firms agree about acting after their positive signals, and
* in the revealed world no firm acts after its own negative signal.

Then every trade event of the revealed world's equilibrium is also a trade event of the
no-sharing equilibrium — which is the event inclusion that Theorem 4.6(1) needs.

`Theorem46Part1Transfer.lean` removes the first condition and weakens the second to the
manuscript's non-inversion assumption. -/
theorem tradeEvent_transfer_of_monotone_patterns
    (alpha beta rhoBar rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hbar0 : 0 ≤ rhoBar) (hbara : rhoBar ≤ alpha) (hbarb : rhoBar ≤ beta)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (n1 n2 t1 t2 : Bool → Bool)
    (hno : IsStrictWeightedNash alpha beta rhoBar reward cost n1 n2)
    (htrain : IsStrictWeightedNash alpha beta rho reward cost t1 t2)
    (hagree : PositiveSignalsAgree n1 n2)
    (hmono : NoNegativeSignalAction t1 t2)
    (q : Bool × Bool) (hq : TrainSharing.Theorem43.tradeEvent t1 t2 q = true) :
    TrainSharing.Theorem43.tradeEvent n1 n2 q = true := by
  obtain ⟨hmono1, hmono2⟩ := hmono
  cases hn1 : n1 true with
  | true =>
      have hn2 : n2 true = true := by rw [← hagree]; exact hn1
      -- Firm 1 acts after `A` and Firm 2 acts after `a`, so the no-sharing trade event
      -- already contains both `{A}` and `{a}`, which is where the world's equilibrium
      -- can trade at all.
      obtain ⟨x, y⟩ := q
      simp only [TrainSharing.Theorem43.tradeEvent] at hq ⊢
      cases x with
      | true => simp [hn1]
      | false =>
          cases y with
          | true => simp [hn2]
          | false =>
              exfalso
              simp [hmono1, hmono2] at hq
  | false =>
      have hn2 : n2 true = false := by rw [← hagree]; exact hn1
      -- Neither firm acts after its positive signal, so no sharing is inactive; its solo
      -- gains are correlation free, hence the world's equilibrium is inactive too.
      have htriv : TrivialProfile n1 n2 :=
        trivial_of_positives_inactive alpha beta rhoBar reward cost halpha hbeta horder
          hreward hcost hbar0 hbara hbarb n1 n2 hno hn1 hn2
      obtain ⟨hsolo1, hsolo2⟩ :=
        solo_gains_nonpos_of_trivial alpha beta rhoBar reward cost n1 n2 hno htriv
      rw [soloGain1] at hsolo1
      rw [soloGain2] at hsolo2
      have htriv' : TrivialProfile t1 t2 := by
        refine strict_equilibrium_trivial_of_solo_nonpos alpha beta rho reward cost halpha
          hbeta hreward hcost hrho0 hrhoa hrhob hrho1 ?_ ?_ t1 t2 htrain
        · rw [soloGain1]; exact hsolo1
        · rw [soloGain2]; exact hsolo2
      exfalso
      obtain ⟨x, y⟩ := q
      simp only [TrainSharing.Theorem43.tradeEvent, htriv'.1 x, htriv'.2 y] at hq
      exact Bool.false_ne_true hq

/-! ## Ex-ante payoffs

Two payoff identities used by the transfer arguments of `Theorem46Part1Transfer.lean`. -/

/-- A firm's ex-ante payoff is the sum of its interim gains at the signals where it
acts. -/
theorem weightedNoSharingPayoff1_eq (alpha beta rho reward cost : ℝ) (s1 s2 : Bool → Bool) :
    weightedNoSharingPayoff1 alpha beta rho reward cost s1 s2 =
      (if s1 true then weightedFirm1Gain alpha beta rho reward cost s2 true else 0) +
      (if s1 false then weightedFirm1Gain alpha beta rho reward cost s2 false else 0) := by
  cases h1 : s1 true <;> cases h2 : s1 false <;>
    simp [weightedNoSharingPayoff1, weightedFirm1Gain, h1, h2] <;> ring

/-- Firm 1's payoff at the no-sharing equilibrium `A → 1, a → 0` is its correlation-free
solo gain. -/
theorem payoff1_follow_inactive (alpha beta rho reward cost : ℝ) :
    weightedNoSharingPayoff1 alpha beta rho reward cost follow inactive =
      (reward * alpha - cost * (1 - alpha)) / 2 := by
  rw [weightedNoSharingPayoff1_eq]
  simp only [follow, id_eq, if_true, if_false, Bool.false_eq_true, add_zero]
  exact soloGain1 alpha beta rho reward cost

end TrainSharing.Theorem46.Classification

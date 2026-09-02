import RequestProject.BayesianGame

/-!
# Appendix A: reduction to congestion games

This file formalizes Definition A.1 and gives the reductions asserted by Theorems 2.1
and 3.4.  A resource records a complete finite realization and the action selected on
that realization.  A pure strategy selects exactly one of the two action-resources at
every realization, subject to the information restriction imposed by its contract.
Thus two firms use the same resource exactly when they take the same action there.
-/

namespace TrainSharing

/-- Definition A.1: a finite congestion game.  Each player's admissible strategies are
finite sets of resources, and the payoff from a selected resource depends only on the
number of players selecting it. -/
structure CongestionGame (Player Resource : Type*) [Fintype Player] [Fintype Resource] where
  strategies : Player → Set (Finset Resource)
  resourceUtility : Resource → ℕ → ℝ

namespace CongestionGame

variable {Player Resource : Type*} [Fintype Player] [DecidableEq Player]
  [Fintype Resource] [DecidableEq Resource]

/-- The congestion induced at a resource by a strategy profile. -/
def congestion (s : Player → Finset Resource) (r : Resource) : ℕ :=
  (Finset.univ.filter fun i => r ∈ s i).card

/-- A player's utility in Definition A.1: the sum of the resource utilities over all
resources selected by that player. -/
def playerUtility (G : CongestionGame Player Resource)
    (s : Player → Finset Resource) (i : Player) : ℝ :=
  ∑ r ∈ s i, G.resourceUtility r (congestion s r)

/-- A profile is admissible when every component belongs to that player's strategy set. -/
def IsAdmissible (G : CongestionGame Player Resource)
    (s : Player → Finset Resource) : Prop :=
  ∀ i, s i ∈ G.strategies i

end CongestionGame

/-- Resources used in the Appendix-A reduction: one for every complete realization and
one of the two possible actions. -/
structure BayesianResource (World Train1 Train2 : Type) where
  world : World
  training : Train1 × Train2
  inference : InferenceOutcome
  action : Bool
  deriving DecidableEq, Fintype

variable {World Train1 Train2 : Type}
  [Fintype World] [DecidableEq World]
  [Fintype Train1] [DecidableEq Train1]
  [Fintype Train2] [DecidableEq Train2]

/-- The resource set selected by a pure strategy under contract `c`. -/
def pureStrategyResources (i : Firm) (c : Contract)
    (s : PureStrategy Train1 Train2 i c) :
    Finset (BayesianResource World Train1 Train2) :=
  Finset.univ.filter fun r => s (observe i c r.training r.inference) = r.action

/-- Resource profile corresponding to a pure Bayesian strategy profile. -/
def pureProfileResources (c : Contract) (s : PureProfile Train1 Train2 c) :
    Firm → Finset (BayesianResource World Train1 Train2)
  | .firm1 => pureStrategyResources .firm1 c s.firm1
  | .firm2 => pureStrategyResources .firm2 c s.firm2

/-- The two-player congestion game associated with a finite Bayesian environment and a
contract.  Congestion one means that the rival selected the opposite action-resource;
congestion two means that both selected the same action-resource. -/
noncomputable def bayesianCongestionGame
    (E : BayesianEnvironment World Train1 Train2) (p : UtilityParameters)
    (c : Contract) : CongestionGame Firm (BayesianResource World Train1 Train2) where
  strategies i := {S | ∃ s : PureStrategy Train1 Train2 i c,
    S = pureStrategyResources i c s}
  resourceUtility r k :=
    E.completeMass r.world r.training r.inference *
      p.exPost r.action r.inference.1 (if k = 2 then r.action else !r.action)

omit [DecidableEq World] [DecidableEq Train1] [DecidableEq Train2] in
/-- Every pure Bayesian profile maps to an admissible congestion-game profile. -/
theorem pureProfileResources_admissible
    (E : BayesianEnvironment World Train1 Train2) (p : UtilityParameters)
    (c : Contract) (s : PureProfile Train1 Train2 c) :
    (bayesianCongestionGame E p c).IsAdmissible (pureProfileResources c s) := by
  intro i
  simp [pureProfileResources, bayesianCongestionGame]
  cases i with
  | firm1 => exact ⟨s.firm1, rfl⟩
  | firm2 => exact ⟨s.firm2, rfl⟩

set_option maxHeartbeats 1000000 in
/-- Core Appendix-A utility identity.  The pure Bayesian expected utility of either firm
is exactly its Definition-A.1 congestion-game utility after the resource reduction. -/
theorem expectedUtility_eq_congestionUtility
    (E : BayesianEnvironment World Train1 Train2) (p : UtilityParameters)
    (c : Contract) (s : PureProfile Train1 Train2 c) (i : Firm) :
    expectedUtility E p.family c s.toMixed i =
      (bayesianCongestionGame E p c).playerUtility (pureProfileResources c s) i := by
  unfold expectedUtility
  simp only [PureProfile.toMixed]
  unfold MixedProfile.actionMass PureStrategy.toMixed
  simp only []
  -- Simplify sums over Bool: the inner Bool sums collapse to single terms
  -- because the mass is 1 for the selected action and 0 otherwise.
  have lemma_bool_sum : ∀ (w : World) (z : Train1 × Train2) (o : InferenceOutcome),
      ∑ a1 : Bool, ∑ a2 : Bool,
        ((E.completeMass w z o * if a1 = s.firm1 (observe .firm1 c z o) then (1 : ℝ) else 0) *
          if a2 = s.firm2 (observe .firm2 c z o) then (1 : ℝ) else 0) *
          (if i = .firm1 then p.family .firm1 a1 o.1 a2 else p.family .firm2 a2 o.1 a1) =
      E.completeMass w z o * (if i = .firm1 then p.family .firm1 (s.firm1 (observe .firm1 c z o)) o.1 (s.firm2 (observe .firm2 c z o)) else p.family .firm2 (s.firm2 (observe .firm2 c z o)) o.1 (s.firm1 (observe .firm1 c z o))) := by
    intro w z o
    fin_cases i <;> simp [Finset.sum_ite_eq']
  -- Now unfold playerUtility and show the sums match
  unfold CongestionGame.playerUtility
  have step1 : (∑ w : World, ∑ z : Train1 × Train2, ∑ o : InferenceOutcome, ∑ a1 : Bool, ∑ a2 : Bool,
      ((E.completeMass w z o * if a1 = s.firm1 (observe .firm1 c z o) then (1 : ℝ) else 0) * if a2 = s.firm2 (observe .firm2 c z o) then (1 : ℝ) else 0) *
        (if i = .firm1 then p.family .firm1 a1 o.1 a2 else p.family .firm2 a2 o.1 a1)) =
      ∑ w : World, ∑ z : Train1 × Train2, ∑ o : InferenceOutcome,
        E.completeMass w z o * (if i = .firm1 then p.family .firm1 (s.firm1 (observe .firm1 c z o)) o.1 (s.firm2 (observe .firm2 c z o)) else p.family .firm2 (s.firm2 (observe .firm2 c z o)) o.1 (s.firm1 (observe .firm1 c z o))) := by
    simp_rw [lemma_bool_sum]
  convert step1
  · fin_cases i <;> simp
  next =>
    fin_cases i <;> simp
    · -- Firm 1 goal
      rw [pureProfileResources, pureStrategyResources, bayesianCongestionGame]
      simp only [CongestionGame.congestion, Finset.sum_filter]
      -- Key lemma: for resource with act = s.firm1(obs), if card=2 then act else !act = s.firm2(obs)
      have h_card : ∀ (w : World) (z : Train1 × Train2) (o : InferenceOutcome) (act : Bool),
          s.firm1 (observe .firm1 c z o) = act →
          (((Finset.univ : Finset Firm).filter (fun i => BayesianResource.mk w z o act ∈ pureProfileResources c s i)).card = 2 ↔ s.firm2 (observe .firm2 c z o) = act) := by
        intro w z o act hact
        have h_filter : (Finset.univ : Finset Firm).filter (fun j => BayesianResource.mk w z o act ∈ pureProfileResources c s j) =
            (if s.firm1 (observe .firm1 c z o) = act then {Firm.firm1} else ∅) ∪
            (if s.firm2 (observe .firm2 c z o) = act then {Firm.firm2} else ∅) := by
          ext j
          simp only [pureProfileResources, pureStrategyResources]
          rw [hact]
          rcases act with true | false <;> rcases b : s.firm2 (observe .firm2 c z o) with true | false <;> cases j <;> simp [b] <;> assumption
        rw [h_filter, hact]
        simp; split_ifs <;> simp <;> assumption
      -- Use h_card to simplify the conditional
      have h_simp : ∀ a : BayesianResource World Train1 Train2,
          s.firm1 (observe .firm1 c a.training a.inference) = a.action →
          ((if ((Finset.univ : Finset Firm).filter (fun i => a ∈ pureProfileResources c s i)).card = 2 then a.action else !a.action) = s.firm2 (observe .firm2 c a.training a.inference)) := by
        intro a ha
        have heq : (Finset.univ : Finset Firm).filter (fun i => a ∈ pureProfileResources c s i) =
            (Finset.univ : Finset Firm).filter (fun i => BayesianResource.mk a.world a.training a.inference a.action ∈ pureProfileResources c s i) := by rfl
        have := h_card a.world a.training a.inference a.action ha
        rw [heq] at *
        split_ifs with h
        · exact (this.mp h).symm
        · have := mt this.mpr h
          cases b : s.firm2 (observe .firm2 c a.training a.inference) <;> simp_all
      have h_term : ∀ a : BayesianResource World Train1 Train2,
          (if s.firm1 (observe .firm1 c a.training a.inference) = a.action then
            E.completeMass a.world a.training a.inference *
              p.exPost a.action a.inference.1
                (if ({i : Firm | a ∈ pureProfileResources c s i} : Finset Firm).card = 2 then a.action else !a.action)
          else 0) =
          if s.firm1 (observe .firm1 c a.training a.inference) = a.action then
            E.completeMass a.world a.training a.inference *
              p.exPost a.action a.inference.1 (s.firm2 (observe .firm2 c a.training a.inference))
          else 0 := by
        intro a
        by_cases h : s.firm1 (observe .firm1 c a.training a.inference) = a.action
        · simp [h, h_simp a h]
        · simp [h]
      simp_rw [h_term]
      -- Convert if-then-else sum to filtered sum
      have hfilter : (∑ r : BayesianResource World Train1 Train2, 
            if s.firm1 (observe .firm1 c r.training r.inference) = r.action then
              E.completeMass r.world r.training r.inference * 
                p.exPost r.action r.inference.1 (s.firm2 (observe .firm2 c r.training r.inference))
            else 0) = 
          ∑ r ∈ Finset.filter (fun r : BayesianResource World Train1 Train2 => 
            s.firm1 (observe .firm1 c r.training r.inference) = r.action) Finset.univ,
            E.completeMass r.world r.training r.inference * 
              p.exPost r.action r.inference.1 (s.firm2 (observe .firm2 c r.training r.inference)) := by
        rw [Finset.sum_filter]
      rw [hfilter]
      -- Convert ∑ r with ... to ∑ r ∈ Finset.filter ...
      have goal_equiv : (∑ r : BayesianResource World Train1 Train2 with s.firm1 (observe .firm1 c r.training r.inference) = r.action,
          E.completeMass r.world r.training r.inference *
            p.exPost r.action r.inference.1 (s.firm2 (observe .firm2 c r.training r.inference))) =
        ∑ r ∈ Finset.filter (fun r : BayesianResource World Train1 Train2 => 
          s.firm1 (observe .firm1 c r.training r.inference) = r.action) Finset.univ,
          E.completeMass r.world r.training r.inference *
            p.exPost r.action r.inference.1 (s.firm2 (observe .firm2 c r.training r.inference)) := by
        rfl
      rw [goal_equiv]
      -- Define bijection: product type → filtered resources
      let f : (World × (Train1 × Train2) × InferenceOutcome) → BayesianResource World Train1 Train2 :=
        fun p => ⟨p.1, p.2.1, p.2.2, s.firm1 (observe .firm1 c p.2.1 p.2.2)⟩
      have hf_filter_eq : Finset.filter (fun r : BayesianResource World Train1 Train2 => 
          s.firm1 (observe .firm1 c r.training r.inference) = r.action) Finset.univ = Finset.univ.image f := by
        apply Finset.ext
        intro r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hr
          refine ⟨(r.world, r.training, r.inference), ?_⟩
          simp only [f]
          cases r; simp_all
        · intro ⟨p, hp⟩
          simp only [f] at hp
          rw [← hp]
      have hf_inj : Function.Injective f := by
        intro p q hpq
        have heq : (⟨p.1, p.2.1, p.2.2, s.firm1 (observe .firm1 c p.2.1 p.2.2)⟩ : BayesianResource _ _ _) = 
                   ⟨q.1, q.2.1, q.2.2, s.firm1 (observe .firm1 c q.2.1 q.2.2)⟩ := hpq
        simp [BayesianResource.mk.injEq] at heq
        rcases heq with ⟨h1, h2, h3, _⟩
        exact Prod.ext h1 (Prod.ext h2 h3)
      rw [hf_filter_eq, Finset.sum_image hf_inj.injOn]
      simp only [f]
      conv_lhs => rw [← Finset.univ_product_univ]
      conv_lhs => rw [Finset.sum_product (Finset.univ : Finset World) (Finset.univ : Finset ((Train1 × Train2) × InferenceOutcome))]
      conv_lhs => { arg 2; ext x; rw [← Finset.univ_product_univ] }
      conv_lhs => { arg 2; ext x; rw [Finset.sum_product (Finset.univ : Finset (Train1 × Train2)) (Finset.univ : Finset InferenceOutcome)] }
      rfl
    · -- Firm 2 goal
      rw [pureProfileResources, pureStrategyResources, bayesianCongestionGame]
      simp only [CongestionGame.congestion, Finset.sum_filter]
      have h_card : ∀ (w : World) (z : Train1 × Train2) (o : InferenceOutcome) (act : Bool),
          s.firm2 (observe .firm2 c z o) = act →
          (((Finset.univ : Finset Firm).filter (fun i => BayesianResource.mk w z o act ∈ pureProfileResources c s i)).card = 2 ↔ s.firm1 (observe .firm1 c z o) = act) := by
        intro w z o act hact
        have h_filter : (Finset.univ : Finset Firm).filter (fun j => BayesianResource.mk w z o act ∈ pureProfileResources c s j) =
            (if s.firm1 (observe .firm1 c z o) = act then {Firm.firm1} else ∅) ∪
            (if s.firm2 (observe .firm2 c z o) = act then {Firm.firm2} else ∅) := by
          ext j
          simp only [pureProfileResources, pureStrategyResources]
          rw [hact]
          rcases act with true | false <;> rcases b : s.firm1 (observe .firm1 c z o) with true | false <;> cases j <;> simp [b] <;> assumption
        rw [h_filter, hact]
        simp; split_ifs <;> simp <;> assumption
      have h_simp : ∀ a : BayesianResource World Train1 Train2,
          s.firm2 (observe .firm2 c a.training a.inference) = a.action →
          ((if ((Finset.univ : Finset Firm).filter (fun i => a ∈ pureProfileResources c s i)).card = 2 then a.action else !a.action) = s.firm1 (observe .firm1 c a.training a.inference)) := by
        intro a ha
        have heq : (Finset.univ : Finset Firm).filter (fun i => a ∈ pureProfileResources c s i) =
            (Finset.univ : Finset Firm).filter (fun i => BayesianResource.mk a.world a.training a.inference a.action ∈ pureProfileResources c s i) := by rfl
        have := h_card a.world a.training a.inference a.action ha
        rw [heq] at *
        split_ifs with h
        · exact (this.mp h).symm
        · have := mt this.mpr h
          cases b : s.firm1 (observe .firm1 c a.training a.inference) <;> simp_all
      have h_term : ∀ a : BayesianResource World Train1 Train2,
          (if s.firm2 (observe .firm2 c a.training a.inference) = a.action then
            E.completeMass a.world a.training a.inference *
              p.exPost a.action a.inference.1
                (if ({i : Firm | a ∈ pureProfileResources c s i} : Finset Firm).card = 2 then a.action else !a.action)
          else 0) =
          if s.firm2 (observe .firm2 c a.training a.inference) = a.action then
            E.completeMass a.world a.training a.inference *
              p.exPost a.action a.inference.1 (s.firm1 (observe .firm1 c a.training a.inference))
          else 0 := by
        intro a
        by_cases h : s.firm2 (observe .firm2 c a.training a.inference) = a.action
        · simp [h, h_simp a h]
        · simp [h]
      simp_rw [h_term]
      have hfilter : (∑ r : BayesianResource World Train1 Train2, 
            if s.firm2 (observe .firm2 c r.training r.inference) = r.action then
              E.completeMass r.world r.training r.inference * 
                p.exPost r.action r.inference.1 (s.firm1 (observe .firm1 c r.training r.inference))
            else 0) = 
          ∑ r ∈ Finset.filter (fun r : BayesianResource World Train1 Train2 => 
            s.firm2 (observe .firm2 c r.training r.inference) = r.action) Finset.univ,
            E.completeMass r.world r.training r.inference * 
              p.exPost r.action r.inference.1 (s.firm1 (observe .firm1 c r.training r.inference)) := by
        rw [Finset.sum_filter]
      rw [hfilter]
      have goal_equiv : (∑ r : BayesianResource World Train1 Train2 with s.firm2 (observe .firm2 c r.training r.inference) = r.action,
          E.completeMass r.world r.training r.inference *
            p.exPost r.action r.inference.1 (s.firm1 (observe .firm1 c r.training r.inference))) =
        ∑ r ∈ Finset.filter (fun r : BayesianResource World Train1 Train2 => 
          s.firm2 (observe .firm2 c r.training r.inference) = r.action) Finset.univ,
          E.completeMass r.world r.training r.inference *
            p.exPost r.action r.inference.1 (s.firm1 (observe .firm1 c r.training r.inference)) := by
        rfl
      rw [goal_equiv]
      let f : (World × (Train1 × Train2) × InferenceOutcome) → BayesianResource World Train1 Train2 :=
        fun p => ⟨p.1, p.2.1, p.2.2, s.firm2 (observe .firm2 c p.2.1 p.2.2)⟩
      have hf_filter_eq : Finset.filter (fun r : BayesianResource World Train1 Train2 => 
          s.firm2 (observe .firm2 c r.training r.inference) = r.action) Finset.univ = Finset.univ.image f := by
        apply Finset.ext
        intro r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hr
          refine ⟨(r.world, r.training, r.inference), ?_⟩
          simp only [f]
          cases r; simp_all
        · intro ⟨p, hp⟩
          simp only [f] at hp
          rw [← hp]
      have hf_inj : Function.Injective f := by
        intro p q hpq
        have heq : (⟨p.1, p.2.1, p.2.2, s.firm2 (observe .firm2 c p.2.1 p.2.2)⟩ : BayesianResource _ _ _) = 
                   ⟨q.1, q.2.1, q.2.2, s.firm2 (observe .firm2 c q.2.1 q.2.2)⟩ := hpq
        simp [BayesianResource.mk.injEq] at heq
        rcases heq with ⟨h1, h2, h3, _⟩
        exact Prod.ext h1 (Prod.ext h2 h3)
      rw [hf_filter_eq, Finset.sum_image hf_inj.injOn]
      simp only [f]
      conv_lhs => rw [← Finset.univ_product_univ]
      conv_lhs => rw [Finset.sum_product (Finset.univ : Finset World) (Finset.univ : Finset ((Train1 × Train2) × InferenceOutcome))]
      conv_lhs => { arg 2; ext x; rw [← Finset.univ_product_univ] }
      conv_lhs => { arg 2; ext x; rw [Finset.sum_product (Finset.univ : Finset (Train1 × Train2)) (Finset.univ : Finset InferenceOutcome)] }
      rfl

/-- A contract has the Appendix-A congestion reduction when every pure profile maps to
an admissible congestion profile and the map preserves both firms' utilities. -/
def HasCongestionReduction
    (E : BayesianEnvironment World Train1 Train2) (p : UtilityParameters)
    (c : Contract) : Prop :=
  ∀ s : PureProfile Train1 Train2 c,
    (bayesianCongestionGame E p c).IsAdmissible (pureProfileResources c s) ∧
      ∀ i, expectedUtility E p.family c s.toMixed i =
        (bayesianCongestionGame E p c).playerUtility (pureProfileResources c s) i

/-- Theorem 2.1: every one of the four contracts reduces to Definition A.1 for arbitrary
utility parameters and every finite world model. -/
theorem theorem2_1_congestion_reduction
    (E : BayesianEnvironment World Train1 Train2) (p : UtilityParameters) :
    ∀ c : Contract, HasCongestionReduction E p c := by
  intro c s
  exact ⟨pureProfileResources_admissible E p c s,
    expectedUtility_eq_congestionUtility E p c s⟩

/-- Theorem 3.4: in particular, the same four reductions hold in the significant-action
correlation-model setting (indeed, the reduction needs no extra correlation assumptions). -/
theorem theorem3_4_congestion_reduction
    (E : BayesianEnvironment World Train1 Train2) (p : UtilityParameters)
    (_hsig : p.IsSignificantAction) :
    ∀ c : Contract, HasCongestionReduction E p c := by
  exact theorem2_1_congestion_reduction E p

/-- Theorem 2.1, explicitly specialized to no sharing. -/
theorem theorem2_1_noSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) : HasCongestionReduction E p .noSharing := by
  exact theorem2_1_congestion_reduction E p .noSharing
/-- Theorem 2.1, explicitly specialized to train sharing. -/
theorem theorem2_1_trainSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) : HasCongestionReduction E p .trainSharing := by
  exact theorem2_1_congestion_reduction E p .trainSharing
/-- Theorem 2.1, explicitly specialized to inference sharing. -/
theorem theorem2_1_inferSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) : HasCongestionReduction E p .inferSharing := by
  exact theorem2_1_congestion_reduction E p .inferSharing
/-- Theorem 2.1, explicitly specialized to full sharing. -/
theorem theorem2_1_fullSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) : HasCongestionReduction E p .fullSharing := by
  exact theorem2_1_congestion_reduction E p .fullSharing

/-- Theorem 3.4, explicitly specialized to no sharing. -/
theorem theorem3_4_noSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) (h : p.IsSignificantAction) :
    HasCongestionReduction E p .noSharing := by
  exact theorem3_4_congestion_reduction E p h .noSharing
/-- Theorem 3.4, explicitly specialized to train sharing. -/
theorem theorem3_4_trainSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) (h : p.IsSignificantAction) :
    HasCongestionReduction E p .trainSharing := by
  exact theorem3_4_congestion_reduction E p h .trainSharing
/-- Theorem 3.4, explicitly specialized to inference sharing. -/
theorem theorem3_4_inferSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) (h : p.IsSignificantAction) :
    HasCongestionReduction E p .inferSharing := by
  exact theorem3_4_congestion_reduction E p h .inferSharing
/-- Theorem 3.4, explicitly specialized to full sharing. -/
theorem theorem3_4_fullSharing (E : BayesianEnvironment World Train1 Train2)
    (p : UtilityParameters) (h : p.IsSignificantAction) :
    HasCongestionReduction E p .fullSharing := by
  exact theorem3_4_congestion_reduction E p h .fullSharing

end TrainSharing

module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SACommSES
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeVectorExists

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IsKRelationCompactWordAction
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def sC (V : Submodule ℂ M) (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => if p.2 = b then Finsupp.lsingle (p.1, a) else 0

theorem sC_single (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sC V a b (Finsupp.single p v) = if p.2 = b then Finsupp.single (p.1, a) v else 0 := by
  simp only [sC, Finsupp.lsum_single]; split_ifs <;> rfl

def compactWordAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  sA ε E V hV a b - sC V a b

theorem compactWordAction_single (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    compactWordAction ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) := by
  rw [compactWordAction, LinearMap.sub_apply, sC_single, sub_eq_iff_eq_add]
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

theorem sC_mul (a b c d : Fin n) : sC V a b * sC V c d = if b = c then sC V a d else 0 := by
  refine Finsupp.lhom_ext fun p v => ?_
  rw [Module.End.mul_apply, sC_single]
  by_cases h1 : p.2 = d <;> by_cases h2 : b = c <;> simp [h1, h2, sC_single, eq_comm]

theorem compactWordAction_commute (hV : IsKStableSub ε E V) (a b c d : Fin n) :
    compactWordAction ε E V hV a b * sC V c d = sC V c d * compactWordAction ε E V hV a b := by
  refine Finsupp.lhom_ext fun p v => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.End.mul_apply, Module.End.mul_apply, sC_single, compactWordAction_single, map_add (f := _), map_sum]
  by_cases h1 : p.2 = d <;> by_cases h : ε a = ε b <;>
    simp only [h1, h, if_true, if_false, dif_pos, dif_neg, not_false_eq_true, compactWordAction_single, map_smul,
      sC_single, map_zero, smul_zero, sum_const_zero, add_zero]

theorem isKRelation_compactWordAction (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (compactWordAction ε E V hV) := by
  intro a b c d hab hcd
  have h1 := sA_isKRel ε E V hV hE a b c d hab hcd
  have e : ∀ x y, sA ε E V hV x y = compactWordAction ε E V hV x y + sC V x y := fun x y => by simp [compactWordAction]
  rw [e a b, e c d, e a d, e c b] at h1
  simp only [add_mul, mul_add, sC_mul, compactWordAction_commute] at h1
  have h2 : compactWordAction ε E V hV a b * compactWordAction ε E V hV c d - compactWordAction ε E V hV c d * compactWordAction ε E V hV a b =
      ((if b = c then compactWordAction ε E V hV a d + sC V a d else 0) -
        if d = a then compactWordAction ε E V hV c b + sC V c b else 0) -
      ((if b = c then sC V a d else 0) - if d = a then sC V c b else 0) := by
    rw [← h1]; abel
  rw [h2]
  split_ifs <;> abel

theorem sT_sC (a b : Fin n) (x : KS (n := n) V) :
    sT E V (sC V a b x) = Pi.single a (sT E V x b) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y h h' => simp only [map_add (f := _), h, h', Pi.add_apply, Pi.single_add]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sC_single, sT_single]
    by_cases h : c = b
    · subst h; simp [sT_single]
    · simp [h, Ne.symm h]

theorem sθ_sC (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n)
    (x : KS (n := n) V) : sθ V EM φ ℓ (sC V a b x) = Pi.single a (sθ V EM φ ℓ x b) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y h h' => simp only [map_add (f := _), h, h', Pi.add_apply, Pi.single_add]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sC_single, sθ_single]
    by_cases h : c = b
    · subst h; simp [sθ_single]
    · simp [h, Ne.symm h]

theorem tensV_eq (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (Pi.single a (f b) : Fin n → M) c := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem contraction_compactWordAction (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b)
    (x : KS (n := n) V) (c : Fin n) : sT E V (compactWordAction ε E V hV a b x) c = E a b (sT E V x c) := by
  rw [compactWordAction, LinearMap.sub_apply, map_sub, sT_sA ε E V hV hE a b hab, sT_sC, Pi.sub_apply, tensV_eq,
    add_sub_cancel_right]

theorem exists_stable (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM)
    (ℓ : V →ₗ[ℂ] ℂ) (W0 : Submodule ℂ (KS (n := n) V)) (hW0 : IsKStableSub ε (compactWordAction ε E V hV) W0)
    (hθ : ∀ x ∈ W0, sθ V EM φ ℓ x = 0) :
    ∃ W : Submodule ℂ (KS (n := n) V), W0 ≤ W ∧ IsKStableSub ε (sA ε E V hV) W ∧
      ∀ x ∈ W, sθ V EM φ ℓ x = 0 := by
  let G : Set (KS (n := n) V) := {x | x ∈ W0 ∨ ∃ c d, ∃ y ∈ W0, x = sC V c d y}
  refine ⟨Submodule.span ℂ G, fun x hx => Submodule.subset_span (Or.inl hx), fun a b hab x hx => ?_,
    fun x hx => ?_⟩
  · refine (Submodule.span_le (p := (Submodule.span ℂ G).comap (sA ε E V hV a b))).mpr ?_ hx
    have e : ∀ y, sA ε E V hV a b y = compactWordAction ε E V hV a b y + sC V a b y := fun y => by simp [compactWordAction]
    rintro y (hy | ⟨c, d, y, hy, rfl⟩)
    · show sA ε E V hV a b y ∈ Submodule.span ℂ G
      rw [e]
      exact add_mem (Submodule.subset_span (Or.inl (hW0 a b hab y hy)))
        (Submodule.subset_span (Or.inr ⟨a, b, y, hy, rfl⟩))
    · show sA ε E V hV a b (sC V c d y) ∈ Submodule.span ℂ G
      rw [e, ← Module.End.mul_apply, compactWordAction_commute, ← Module.End.mul_apply (sC V a b), sC_mul]
      refine add_mem (Submodule.subset_span (Or.inr ⟨c, d, _, hW0 a b hab y hy, rfl⟩)) ?_
      split_ifs
      · exact Submodule.subset_span (Or.inr ⟨a, d, y, hy, rfl⟩)
      · exact Submodule.zero_mem _
  · refine (Submodule.span_le (p := LinearMap.ker (sθ V EM φ ℓ))).mpr ?_ hx
    rintro y (hy | ⟨c, d, y, hy, rfl⟩)
    · exact hθ y hy
    · show sθ V EM φ ℓ (sC V c d y) = 0
      rw [sθ_sC, hθ y hy]; simp

theorem verma_weight (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM) (ν : Fin n → ℝ)
    (hlow : ∀ a b, b < a → EM a b φ = 0) (hwt : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ)
    (hgen : genSub EM (Submodule.span ℂ {φ}) = ⊤) {μ : Fin n → ℝ} {x : MM} (hx0 : x ≠ 0)
    (hx : ∀ a, EM a a x = ((μ a : ℝ) : ℂ) • x) : InRootCone (μ - ν) := by
  by_contra hμ
  refine hx0 (vc_eq_zero_of_mem_span EM (fun β => InRootCone (β - ν)) hμ hx ?_)
  have h1 := vc_genSub_le_mon EM hEM φ ⊥ (fun a b y hy => by simp_all)
    (fun a b h => by simp [hlow a b h]) (fun a => ⟨_, hwt a⟩)
  rw [hgen, sup_bot_eq] at h1
  refine Submodule.span_mono ?_ (h1 Submodule.mem_top)
  intro w hw
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
  obtain ⟨β, h2, h3, -⟩ := vcMon_weight EM hEM hwt k w hk
  exact ⟨β, h3, h2⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone
end
end

noncomputable section

open Finset
open scoped InnerProductSpace ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem klw_cons_nil (a b : Fin n) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    adLW a b (p :: w) [] = 0 := by
  simp only [adLW, Finsupp.add_apply]
  rw [Finsupp.mapDomain_of_notMem_range, Finsupp.mapDomain_of_notMem_range, add_zero] <;> simp

theorem klw_cons_cons (a b : Fin n) (p q : Fin n × Fin n) (w w' : List (Fin n × Fin n)) :
    adLW a b (p :: w) (q :: w') =
      (if w' = w then adL a b p q else 0) + (if q = p then adLW a b w w' else 0) := by
  simp only [adLW, Finsupp.add_apply]
  congr 1
  · split_ifs with h
    · subst h
      exact Finsupp.mapDomain_apply_of_injective (f := fun x => x :: w') (fun x y hxy => (List.cons.inj hxy).1) _ _
    · rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      exact h (List.cons.inj hx).2.symm
  · split_ifs with h
    · subst h
      exact Finsupp.mapDomain_apply_of_injective (f := fun x => q :: x) List.cons_injective _ _
    · rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      exact h (List.cons.inj hx).1.symm

theorem kl_adL_apply (a b : Fin n) (p q : Fin n × Fin n) :
    adL a b p q = (if b = p.1 ∧ q = (a, p.2) then 1 else 0) - (if p.2 = a ∧ q = (p.1, b) then 1 else 0) := by
  simp only [adL, Finsupp.sub_apply]
  congr 1
  · by_cases h : b = p.1
    · simp [h, Finsupp.single_apply, eq_comm]
    · simp [h]
  · by_cases h : p.2 = a
    · simp [h, Finsupp.single_apply, eq_comm]
    · simp [h]

theorem kl_adL_symm (a b : Fin n) (p q : Fin n × Fin n) :
    starRingEnd ℂ (adL a b p q) = adL b a q p := by
  rw [kl_adL_apply, kl_adL_apply]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [map_sub, apply_ite (starRingEnd ℂ), map_one, map_zero, Prod.mk.injEq]
  congr 1
  · by_cases h : b = p1 ∧ q1 = a ∧ q2 = p2
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl, rfl⟩; exact h ⟨rfl, rfl, rfl⟩
  · by_cases h : p2 = a ∧ q1 = p1 ∧ q2 = b
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl, rfl⟩; exact h ⟨rfl, rfl, rfl⟩

theorem klw_symm (a b : Fin n) (w w' : List (Fin n × Fin n)) :
    starRingEnd ℂ (adLW a b w w') = adLW b a w' w := by
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil => simp [adLW]
    | cons q w' => rw [klw_cons_nil]; simp [adLW]
  | cons p w ih =>
    cases w' with
    | nil => rw [klw_cons_nil]; simp [adLW]
    | cons q w' =>
      rw [klw_cons_cons, klw_cons_cons, map_add (f := _), apply_ite (starRingEnd ℂ), apply_ite (starRingEnd ℂ)]
      simp only [map_zero, kl_adL_symm, ih]
      by_cases h1 : w' = w
      · subst h1
        by_cases h2 : q = p
        · subst h2; simp
        · simp [h2, Ne.symm h2]
      · by_cases h2 : q = p
        · subst h2; simp [h1, Ne.symm h1]
        · simp [h1, Ne.symm h1, h2, Ne.symm h2]

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def ipK (V : Submodule ℂ M) : KS (n := n) V →ₗ⋆[ℂ] KS (n := n) V →ₗ[ℂ] ℂ where
  toFun x := x.sum fun p v => (innerₛₗ ℂ v) ∘ₗ Finsupp.lapply p
  map_add' x y := Finsupp.sum_add_index' (fun p => by simp) (fun p v v' => by
    rw [map_add (f := _), LinearMap.add_comp])
  map_smul' c x := by
    rw [Finsupp.sum_smul_index' (fun p => by simp), Finsupp.smul_sum]
    exact Finsupp.sum_congr fun p _ => by rw [map_smulₛₗ, LinearMap.smul_comp]

theorem ipK_single (p : List (Fin n × Fin n) × Fin n) (v : V) (y : KS (n := n) V) :
    ipK V (Finsupp.single p v) y = ⟪v, y p⟫_ℂ := by
  show ((Finsupp.single p v).sum fun p v => (innerₛₗ ℂ v) ∘ₗ Finsupp.lapply p) y = _
  rw [Finsupp.sum_single_index (by simp)]; rfl

theorem ipK_apply (x y : KS (n := n) V) : ipK V x y = ∑ p ∈ x.support, ⟪x p, y p⟫_ℂ := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum, LinearMap.sum_apply]
  simp only [ipK_single]

theorem ipK_symm (x y : KS (n := n) V) : conj (ipK V y x) = ipK V x y := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | single p v =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
    | single q u =>
      rw [ipK_single, ipK_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : p = q
      · simp [h]
      · simp [h, Ne.symm h]

theorem compactWordAction_single_apply (hV : IsKStableSub ε E V) {a b : Fin n} (hab : ε a = ε b)
    (p q : List (Fin n × Fin n) × Fin n) (v : V) :
    compactWordAction ε E V hV a b (Finsupp.single p v) q = (if p.2 = q.2 then adLW a b p.1 q.1 • v else 0) +
      (if p = q then (⟨E a b v, hV a b hab v v.2⟩ : V) else 0) := by
  classical
  rw [compactWordAction_single, dite_eq_left hab, Finsupp.add_apply, Finsupp.single_apply, Finsupp.finsetSum_apply]
  congr 1
  simp only [Finsupp.smul_apply, Finsupp.single_apply, Prod.ext_iff]
  by_cases h : p.2 = q.2
  · simp only [h, and_true, if_true]
    rw [sum_eq_single q.1 (fun w _ hw => by simp [hw]) (fun hq => by
      simp [Finsupp.notMem_support_iff.mp hq])]
    simp
  · simp [h]

theorem inner_compactWordAction_adjoint (hV : IsKStableSub ε E V) (hU : IsKUnitary ε E) {a b : Fin n} (hab : ε a = ε b)
    (x y : KS (n := n) V) : ipK V (compactWordAction ε E V hV a b x) y = ipK V x (compactWordAction ε E V hV b a y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | single p v =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), h, h']
    | single q u =>
      rw [← ipK_symm, ipK_single, ipK_single, compactWordAction_single_apply hV hab, compactWordAction_single_apply hV hab.symm,
        inner_conj_symm, inner_add_left, inner_add_right]
      congr 1
      · by_cases h : p.2 = q.2
        · rw [if_pos h, if_pos h.symm, inner_smul_left, inner_smul_right, klw_symm]
        · rw [if_neg h, if_neg (Ne.symm h), inner_zero_left, inner_zero_right]
      · by_cases h : p = q
        · rw [if_pos h, if_pos h.symm]; exact hU a b hab v u
        · rw [if_neg h, if_neg (Ne.symm h), inner_zero_left, inner_zero_right]

theorem lift0 (hV : IsKStableSub ε E V) [FiniteDimensional ℂ V] (hE : IsGlRep E) (hU : IsKUnitary ε E)
    {μ : Fin n → ℝ} {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) (hμ : ∀ c, IsKHWVec ε E μ (f c)) :
    ∃ u, IsKHWVec ε (compactWordAction ε E V hV) μ u ∧ sT E V u = f := by
  obtain ⟨x, rfl⟩ := sT_surj E V f hf
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have hfd : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have hS : IsKStableSub ε (compactWordAction ε E V hV) (Finsupp.supported V ℂ S) := by
    intro a b hab y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [compactWordAction_single]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_
    · show w'.length ≤ R
      rw [TRA.adLW_length a b _ _ hw']; exact hpS
    · rw [dite_eq_left hab]
      exact Finsupp.single_mem_supported ℂ _ hpS
  let cr : InnerProductSpace.Core ℂ (KS (n := n) V) :=
    { inner := fun x y => ipK V x y
      conj_inner_symm := fun x y => ipK_symm x y
      re_inner_nonneg := fun x => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [ipK_apply, map_sum]; exact sum_nonneg fun p _ => inner_self_nonneg
      add_left := fun x y z => by rw [map_add (f := _), LinearMap.add_apply]
      smul_left := fun x y r => by rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      definite := fun x hx => by
        have h1 := congrArg RCLike.re hx
        set_option synthInstance.maxHeartbeats 100000 in
          rw [ipK_apply, map_sum, map_zero,
          sum_eq_zero_iff_of_nonneg fun p _ => inner_self_nonneg] at h1
        ext1 p
        by_cases hp : p ∈ x.support
        · have h2 := h1 p hp
          rw [inner_self_eq_norm_sq] at h2
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
        · exact Finsupp.notMem_support_iff.mp hp }
  let _ : NormedAddCommGroup (KS (n := n) V) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ cr
  let _ : InnerProductSpace ℂ (KS (n := n) V) := InnerProductSpace.ofCore cr.toCore
  obtain ⟨u, -, -, h1, h2⟩ := lift_khw (ε := ε) (A := compactWordAction ε E V hV) (μ := μ)
    (B := fun a b => (E a b).compLeft (Fin n)) (fun a b hab x y => inner_compactWordAction_adjoint hV hU hab x y) (sT E V)
    (fun a b hab x => funext fun c => contraction_compactWordAction hV hE a b hab x c) hfd hS (x₀ := x)
    (fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp)
    ⟨fun a => funext fun c => (hμ c).1 a, fun a b hab he => funext fun c => (hμ c).2 a b hab he⟩
  exact ⟨u, h1, h2⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone

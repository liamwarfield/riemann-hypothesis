module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrR

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrS
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

def PlaceSt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceIn l OE R d em

def EigFreeSt : Prop :=
  ∀ (C : Type) [Field C] (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], vm.Integers R →
    ∀ (n : ℕ) (ι : Type) (L : ι → Matrix (Fin n) (Fin n) R) (χ : ι → R),
      ∃ (s : ℕ) (W : Fin s → Fin n → R), (∀ i a, (L a).mulVec (W i) = χ a • W i) ∧
        ∀ v : Fin n → R, (∀ a, (L a).mulVec v = χ a • v) → ∃! c : Fin s → R, ∑ i, c i • W i = v

section Eig

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {R : Type} [CommRing R] [Algebra R C]

theorem linAct_toC {Y : FBChart C V OE dd} (actR : OE → Fin dd → PS R 1 dd)
    (hact : ∀ a i, Y.B.A.act a i = toC (actR a i)) (x : OE) (v : Fin dd → R) (i : Fin dd) :
    algebraMap R C ((linPart (actR x)).mulVec v i) = linAct (Y.B.A.act x) (fun j => algebraMap R C (v j)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linAct, hact, toC, MvPowerSeries.coeff_map, linPart, Matrix.mulVec, dotProduct, Matrix.of_apply,
    map_sum, map_mul]

end Eig

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPlB
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

theorem placeSt_of_X (h : Pl.PlaceCriterionOfIdempotent) : PlaceSt := by
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl hd d _ em h1 h2 h3
  obtain ⟨e, he1, he2, he3, iN, t, jj, hj, ht, b, hb⟩ := h l OE R hl hd d em h1 h2 h3
  exact ⟨⟨e, he1, he2, he3⟩, iN, t, jj, hj, ht, b, hb⟩

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrEF
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

theorem echelon {C : Type} [Field C] (vm : Valuation C NNReal) (n : ℕ) :
    ∀ (k : ℕ) (M : Submodule C (Fin n → C)), Module.finrank C M = k →
    ∃ (s : ℕ) (J : Fin s → Fin n) (B : Fin s → Fin n → C), (∀ i, B i ∈ M) ∧ (∀ i x, vm (B i x) ≤ 1) ∧
      (∀ i i', B i (J i') = if i = i' then 1 else 0) ∧ ∀ v ∈ M, v = ∑ i, v (J i) • B i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M hM
  by_cases h0 : ∃ v ∈ M, v ≠ 0
  swap
  · push_neg at h0
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun v hv => ?_⟩
    simp [h0 v hv]
  obtain ⟨v, hvM, hv0⟩ := h0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hv0
  obtain ⟨j, -, hjmax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image (fun x => vm (v x))
    ⟨x₀, Finset.mem_univ _⟩
  have hvj : v j ≠ 0 := by
    intro h
    have h1 : vm (v x₀) ≤ vm (v j) := hjmax x₀ (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hx₀ ((Valuation.zero_iff vm).1 (le_antisymm h1 zero_le'))

  set v₀ : Fin n → C := (v j)⁻¹ • v with hv₀
  have hv₀j : v₀ j = 1 := by simp [hv₀, hvj]
  have hv₀M : v₀ ∈ M := M.smul_mem _ hvM
  have hv₀le : ∀ x, vm (v₀ x) ≤ 1 := by
    intro x
    have hpos : 0 < vm (v j) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff vm).2 hvj)
    simp only [hv₀, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hjmax x (Finset.mem_univ _)
  set M' : Submodule C (Fin n → C) := M ⊓ LinearMap.ker (LinearMap.proj j) with hM'
  have hlt : M' < M := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : v₀ ∈ M' := h ▸ hv₀M
    have h2 : v₀ j = 0 := (Submodule.mem_inf.1 h1).2
    rw [hv₀j] at h2
    exact one_ne_zero h2
  have hfr : Module.finrank C M' < k := hM ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨s, J', B', hB'M, hB'le, hB'δ, hB'span⟩ := ih _ hfr M' rfl
  have hB'j : ∀ i, B' i j = 0 := fun i => (Submodule.mem_inf.1 (hB'M i)).2
  have hB'M0 : ∀ i, B' i ∈ M := fun i => (Submodule.mem_inf.1 (hB'M i)).1
  set b : Fin n → C := v₀ - ∑ i, v₀ (J' i) • B' i with hb
  have hbM : b ∈ M := M.sub_mem hv₀M (M.sum_mem fun i _ => M.smul_mem _ (hB'M0 i))
  have hbj : b j = 1 := by simp [hb, Finset.sum_apply, hB'j, hv₀j]
  have hbJ : ∀ i', b (J' i') = 0 := by
    intro i'
    simp [hb, Finset.sum_apply, hB'δ]
  have hble : ∀ x, vm (b x) ≤ 1 := by
    intro x
    simp only [hb, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Valuation.map_sub_le _ (hv₀le x) (Valuation.map_sum_le _ fun i _ => ?_)
    rw [map_mul]
    exact mul_le_one' (hv₀le _) (hB'le i x)
  refine ⟨s + 1, (Fin.cons j J' : Fin (s + 1) → Fin n), (Fin.cons b B' : Fin (s + 1) → Fin n → C),
    ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hbM
    | succ i => simpa using hB'M0 i
  · intro i x
    induction i using Fin.cases with
    | zero => simpa using hble x
    | succ i => simpa using hB'le i x
  · intro i i'
    induction i using Fin.cases with
    | zero =>
      induction i' using Fin.cases with
      | zero => simp [hbj]
      | succ i' => simp only [Fin.cons_zero, Fin.cons_succ, hbJ]; rw [if_neg (Fin.succ_ne_zero i').symm]
    | succ i =>
      induction i' using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ, hB'j]; rw [if_neg (Fin.succ_ne_zero i)]
      | succ i' => simp [hB'δ, Fin.succ_inj]
  · intro w hw
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hw' : w - w j • b ∈ M' := by
      refine Submodule.mem_inf.2 ⟨M.sub_mem hw (M.smul_mem _ hbM), ?_⟩
      simp [LinearMap.mem_ker, hbj]
    have h1 := hB'span _ hw'
    have e : ∀ i, (w - w j • b) (J' i) = w (J' i) := by
      intro i
      simp [hbJ]
    simp only [e] at h1
    rw [← h1]
    abel

theorem eigFreeSt_holds : EigFreeSt := by
  intro C _ vm R _ _ hI n ι L χ
  set f := algebraMap R C
  let M : Submodule C (Fin n → C) :=
    { carrier := {w | ∀ a, ((L a).map f).mulVec w = f (χ a) • w}
      add_mem' := by
        intro w w' hw hw' a
        simp only [Set.mem_setOf_eq] at hw hw' ⊢
        rw [Matrix.mulVec_add, hw a, hw' a, smul_add]
      zero_mem' := by
        intro a
        simp
      smul_mem' := by
        intro c w hw a
        simp only [Set.mem_setOf_eq] at hw ⊢
        rw [Matrix.mulVec_smul, hw a, smul_comm] }
  obtain ⟨s, J, B, hBM, hBle, hBδ, hspan⟩ := echelon vm n _ M rfl
  have hlift : ∀ i x, ∃ r : R, f r = B i x := fun i x => hI.exists_of_le_one (hBle i x)
  choose W hW using hlift
  have hfW : ∀ i, f ∘ W i = B i := fun i => funext (hW i)
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R), f ∘ (A.mulVec v) = (A.map f).mulVec (f ∘ v) := by
    intro A v
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have hinj : Function.Injective f := hI.hom_inj
  have hinjv : ∀ v w : Fin n → R, f ∘ v = f ∘ w → v = w :=
    fun v w h => funext fun x => hinj (congrFun h x)
  refine ⟨s, W, fun i a => ?_, fun v hv => ?_⟩
  · apply hinjv
    rw [hmap, hfW, hBM i a]
    funext x
    simp [hW]
  · have hvM : f ∘ v ∈ M := by
      intro a
      rw [← hmap, hv a]
      funext x
      simp
    refine ⟨fun i => v (J i), ?_, ?_⟩
    · apply hinjv
      have h1 := hspan _ hvM
      funext x
      have hx := congrFun h1 x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hx ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul, hW]
      exact hx.symm
    · intro c hc
      funext i
      have h1 := congrFun hc (J i)
      apply hinj
      rw [← h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum, hW, hBδ]

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrRP
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

section Val

variable {C : Type} [Field C] (V : VF C)

def bb : NNReal := ((V.l : ℕ) : NNReal)⁻¹

theorem bb_pos : 0 < bb V := by
  simp [bb, V.l_prime.pos]

theorem bb_lt : bb V < 1 := by
  have h : (1 : NNReal) < ((V.l : ℕ) : NNReal) := by exact_mod_cast V.l_prime.one_lt
  exact inv_lt_one_of_one_lt₀ h

variable {V}

theorem exists_real {x : C} (hx : x ≠ 0) : ∃ t : ℝ, V.v x = (t : WithTop ℝ) := by
  have h : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨t, ht.symm⟩

variable (V)

def vmFun (x : C) : NNReal := if x = 0 then 0 else bb V ^ ((V.v x).untopD 0)

variable {V}

theorem vmFun_of {x : C} (hx : x ≠ 0) {t : ℝ} (ht : V.v x = (t : WithTop ℝ)) : vmFun V x = bb V ^ t := by
  simp [vmFun, hx, ht]

variable (V)

def vmOf : Valuation C NNReal where
  toFun := vmFun V
  map_zero' := by simp [vmFun]
  map_one' := by
    rw [vmFun_of one_ne_zero (t := 0) (by rw [V.v.map_one]; rfl), NNReal.rpow_zero]
  map_mul' := by
    intro x y
    by_cases hx : x = 0
    · simp [vmFun, hx]
    by_cases hy : y = 0
    · simp [vmFun, hy]
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    obtain ⟨s, hs⟩ := exists_real (V := V) hy
    rw [vmFun_of hx ht, vmFun_of hy hs, vmFun_of (mul_ne_zero hx hy) (t := t + s)
      (by rw [V.v.map_mul, ht, hs]; rfl), NNReal.rpow_add (bb_pos V).ne']
  map_add_le_max' := by
    intro x y
    by_cases hxy : x + y = 0
    · simp [vmFun, hxy]
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    obtain ⟨s, hs⟩ := exists_real (V := V) hy
    obtain ⟨r, hr⟩ := exists_real (V := V) hxy
    rw [vmFun_of hx ht, vmFun_of hy hs, vmFun_of hxy hr]
    rcases V.v.map_add' x y with h | h
    · rw [ht, hr] at h
      exact le_max_of_le_left (NNReal.rpow_le_rpow_of_exponent_ge (bb_pos V) (bb_lt V).le (WithTop.coe_le_coe.mp h))
    · rw [hs, hr] at h
      exact le_max_of_le_right (NNReal.rpow_le_rpow_of_exponent_ge (bb_pos V) (bb_lt V).le (WithTop.coe_le_coe.mp h))

variable {V}

theorem vmOf_of {x : C} (hx : x ≠ 0) {t : ℝ} (ht : V.v x = (t : WithTop ℝ)) : vmOf V x = bb V ^ t := by
  show vmFun V x = _
  exact vmFun_of hx ht

theorem vmOf_l : vmOf V (V.l : C) = bb V := by
  have hl : (V.l : C) ≠ 0 := by
    intro h
    have h1 := V.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  rw [vmOf_of hl (t := 1) (by rw [V.v_l]; rfl), NNReal.rpow_one]

theorem valTie_vmOf : ValTie V (vmOf V) := by
  intro x hx
  obtain ⟨t, ht⟩ := exists_real (V := V) hx
  refine ⟨t, ht, ?_⟩
  rw [vmOf_of hx ht, vmOf_l, NNReal.coe_rpow]

theorem integers_vmOf : (vmOf V).Integers V.RR := by
  refine ⟨Subtype.coe_injective, ?_, ?_⟩
  · intro x
    show vmOf V (x : C) ≤ 1
    by_cases hx : (x : C) = 0
    · simp [hx]
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    rw [vmOf_of hx ht]
    have h0 : V.Ge 0 (x : C) := x.2
    unfold VF.Ge at h0
    rw [ht] at h0
    exact NNReal.rpow_le_one (bb_lt V).le (WithTop.coe_le_coe.mp h0)
  · intro r hr
    suffices h : V.Ge 0 r from ⟨⟨r, h⟩, rfl⟩
    by_cases hx : r = 0
    · rw [hx]; exact VF.Ge.zero 0
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    rw [vmOf_of hx ht] at hr
    unfold VF.Ge
    rw [ht]
    refine WithTop.coe_le_coe.mpr ?_
    by_contra hneg
    exact absurd hr (not_le.mpr (NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg (bb_pos V) (bb_lt V) (not_le.mp hneg)))

theorem not_isUnit_of_mm {x : V.RR} (hx : V.MM (x : C)) : ¬ IsUnit x := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : (x : C) * (y : C) = 1 := by
    have := congrArg Subtype.val hy
    simpa using this
  have h2 := congrArg V.v h1
  rw [AddValuation.map_mul, AddValuation.map_one] at h2
  have hy0 : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
  have hx0 : (0 : WithTop ℝ) < V.v (x : C) := hx
  have h3 : (0 : WithTop ℝ) < V.v (x : C) + V.v (y : C) := lt_of_lt_of_le hx0 (le_add_of_nonneg_right hy0)
  rw [h2] at h3
  exact lt_irrefl _ h3

theorem v_l_pow (n : ℕ) : V.v ((V.l : C) ^ n) = ((n : ℝ) : WithTop ℝ) := by
  rw [AddValuation.map_pow, V.v_l]
  simp

theorem mem_pow_iff (n : ℕ) (x : V.RR) :
    x ∈ (Ideal.span {((V.l : ℕ) : V.RR)} ^ n • ⊤ : Submodule V.RR V.RR) ↔ V.Ge n (x : C) := by
  have hl : (V.l : C) ≠ 0 := by
    intro h
    have h1 := V.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hln : (V.l : C) ^ n ≠ 0 := pow_ne_zero _ hl
  rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    show ((n : ℝ) : WithTop ℝ) ≤ V.v ((((((V.l : ℕ) : V.RR) ^ n * y : V.RR)) : C))
    push_cast
    rw [AddValuation.map_mul, v_l_pow]
    have hy : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
    exact le_add_of_nonneg_right hy
  · intro hx
    have hxy : (x : C) = (V.l : C) ^ n * ((x : C) / (V.l : C) ^ n) := by
      field_simp
    have h2 : V.v (x : C) = ((n : ℝ) : WithTop ℝ) + V.v ((x : C) / (V.l : C) ^ n) := by
      conv_lhs => rw [hxy]
      rw [AddValuation.map_mul, v_l_pow]
    have h3 : ((n : ℝ) : WithTop ℝ) + 0 ≤ ((n : ℝ) : WithTop ℝ) + V.v ((x : C) / (V.l : C) ^ n) := by
      rw [add_zero, ← h2]
      exact hx
    have hy : V.Ge 0 ((x : C) / (V.l : C) ^ n) := (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp h3
    refine ⟨⟨(x : C) / (V.l : C) ^ n, hy⟩, ?_⟩
    apply Subtype.ext
    show (x : C) = ((((V.l : ℕ) : V.RR) ^ n : V.RR) : C) * ((x : C) / (V.l : C) ^ n)
    push_cast
    exact hxy

theorem hausdorff_RR : IsHausdorff (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR where
  haus' := by
    intro x hx
    apply Subtype.ext
    show (x : C) = 0
    by_contra h0
    obtain ⟨t, ht⟩ := exists_real (V := V) h0
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have h1 := hx n
    rw [SModEq.sub_mem, sub_zero, mem_pow_iff] at h1
    unfold VF.Ge at h1
    rw [ht] at h1
    exact absurd (WithTop.coe_le_coe.mp h1) (not_le.mpr hn)

theorem precomplete_RR
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) :
    IsPrecomplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR where
  prec' := by
    intro f hf
    obtain ⟨x, hx⟩ := hc (fun n => (f n : C)) (fun n => by
      have h1 := hf (Nat.le_succ n)
      rw [SModEq.sub_mem, mem_pow_iff] at h1
      have h2 := h1.neg
      have e : -(((f n - f (n + 1) : V.RR)) : C) = (f (n + 1) : C) - (f n : C) := by
        push_cast
        ring
      rw [e] at h2
      exact h2)
    have hx0 : V.Ge 0 x := by
      have h1 : V.Ge 0 (x - (f 0 : C)) := by simpa using hx 0
      have h2 : V.Ge 0 ((f 0 : V.RR) : C) := (f 0).2
      have := h1.add h2
      simpa using this
    refine ⟨⟨x, hx0⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_iff]
    have h2 := (hx n).neg
    have e : -(x - (f n : C)) = (((f n - (⟨x, hx0⟩ : V.RR) : V.RR)) : C) := by
      push_cast
      ring
    rw [e] at h2
    exact h2

end Val

section Zl

variable (l : ℕ) [Fact l.Prime] (S : Type) [CommRing S]

theorem ringChar_dvd_pow (n : ℕ) : ringChar (S ⧸ Ideal.span {(l : S)} ^ n) ∣ l ^ n := by
  apply ringChar.dvd
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (l : S)) n : (l : S) ^ n ∈ Ideal.span {(l : S)} ^ n)
  simpa using h

def zlStep (n : ℕ) : ℤ_[l] →+* S ⧸ Ideal.span {(l : S)} ^ n :=
  (ZMod.castHom (ringChar_dvd_pow l S n) (S ⧸ Ideal.span {(l : S)} ^ n)).comp (PadicInt.toZModPow n)

theorem zlStep_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(l : S)}) hle).comp (zlStep l S n) = zlStep l S m := by
  unfold zlStep
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

def zlHom [IsAdicComplete (Ideal.span {(l : S)}) S] : ℤ_[l] →+* S :=
  IsAdicComplete.liftRingHom (Ideal.span {(l : S)}) (zlStep l S) (fun hle => zlStep_compat l S hle)

end Zl

theorem ringPkSt_holds : RingPkSt := by
  intro C _ _ V hc
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  have hl : (V.l : C) ≠ 0 := by
    intro h
    have h1 := V.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hvl : V.MM ((((V.l : ℕ) : V.RR)) : C) := by
    show (0 : WithTop ℝ) < V.v ((((V.l : ℕ) : V.RR)) : C)
    push_cast
    rw [V.v_l]
    exact (WithTop.coe_lt_coe.mpr (zero_lt_one : (0 : ℝ) < 1))
  have hunit : ∀ x : V.RR, ¬ V.MM (x : C) → IsUnit x := by
    intro x hx
    have hx0 : (x : C) ≠ 0 := by
      intro h
      apply hx
      show (0 : WithTop ℝ) < V.v (x : C)
      rw [h, AddValuation.map_zero]
      exact WithTop.coe_lt_top 0
    have hv0 : V.v (x : C) = 0 := by
      have h1 : (0 : WithTop ℝ) ≤ V.v (x : C) := x.2
      have h2 : ¬ (0 : WithTop ℝ) < V.v (x : C) := hx
      exact le_antisymm (not_lt.mp h2) h1
    have hinv : V.Ge 0 ((x : C)⁻¹) := by
      show ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹)
      have h3 : V.v ((x : C) * (x : C)⁻¹) = 0 := by
        rw [mul_inv_cancel₀ hx0, AddValuation.map_one]
      rw [AddValuation.map_mul, hv0, zero_add] at h3
      rw [h3]
      rfl
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : C)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (x : C) * (x : C)⁻¹ = 1
    exact mul_inv_cancel₀ hx0
  have hloc : IsLocalRing V.RR := IsLocalRing.of_nonunits_add (fun a b ha hb => by
    have ha' : V.MM (a : C) := by
      by_contra h
      exact (mem_nonunits_iff.mp ha) (hunit a h)
    have hb' : V.MM (b : C) := by
      by_contra h
      exact (mem_nonunits_iff.mp hb) (hunit b h)
    exact mem_nonunits_iff.mpr (not_isUnit_of_mm (V := V) (x := a + b)
      (lt_of_lt_of_le (lt_min ha' hb') (V.v.map_add _ _))))
  haveI hcpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR :=
    { haus' := (hausdorff_RR (V := V)).haus', prec' := (precomplete_RR (V := V) hc).prec' }
  haveI := hloc
  exact ⟨{ vm := vmOf V
           tie := valTie_vmOf
           int := integers_vmOf
           pos := by
             rw [vmOf_l]
             exact_mod_cast bb_pos V
           lt := by
             rw [vmOf_l]
             exact_mod_cast bb_lt V
           nonunit := not_isUnit_of_mm (V := V) hvl
           cpl := hcpl
           loc := hloc
           alg := (zlHom V.l V.RR).toAlgebra
           mm := fun x hx => (IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr (not_isUnit_of_mm hx)) }⟩

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section RR

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem isUnit_RR {x : V.RR} (hx : V.v (x : C) = 0) : IsUnit x := by
  have hx0 : (x : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at hx
    exact WithTop.top_ne_zero hx
  have hi : V.Ge 0 ((x : C)⁻¹) := by
    have h1 : V.v ((x : C) * (x : C)⁻¹) = 0 := by rw [mul_inv_cancel₀ hx0, V.v.map_one]
    rw [V.v.map_mul, hx, zero_add] at h1
    unfold VF.Ge
    rw [h1]
    rfl
  exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, hi⟩ : V.RR) (Subtype.ext (mul_inv_cancel₀ hx0))

theorem v_of_isUnit_RR {x : V.RR} (hx : IsUnit x) : V.v (x : C) = 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : V.v ((x : C) * (y : C)) = 0 := by
    have : (x : C) * (y : C) = 1 := congrArg Subtype.val hy
    rw [this, V.v.map_one]
  rw [V.v.map_mul] at h1
  have hx0 : (0 : WithTop ℝ) ≤ V.v (x : C) := x.2
  have hy0 : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
  exact le_antisymm (by calc V.v (x : C) ≤ V.v (x : C) + V.v (y : C) := le_add_of_nonneg_right hy0
                          _ = 0 := h1) hx0

theorem not_isUnit_l {T : Type} [CommRing T] (i0 : T →+* C) (hint : ∀ t, V.Ge 0 (i0 t)) :
    ¬ IsUnit ((V.l : ℕ) : T) := by
  intro h
  have h1 := v_of_isUnit_RR (h.map (i0.codRestrict V.RR hint))
  have h2 : (((i0.codRestrict V.RR hint) ((V.l : ℕ) : T) : V.RR) : C) = (V.l : C) := map_natCast i0 _
  rw [h2, V.v_l] at h1
  exact one_ne_zero h1

end RR

section Chart

open Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem vV_pos (T : CDVR) {t : T.V} (ht : ¬ IsUnit t) (h0 : t ≠ 0) : 0 < vV T.V (algebraMap T.V T.Fr t) := by
  unfold vV
  have hne : valV T.V (algebraMap T.V T.Fr t) ≠ 0 :=
    valV_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 h0)
  have h1 : valV T.V (algebraMap T.V T.Fr t) < 1 := by
    unfold valV
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ t).2 ((mem_maximalIdeal t).2 ht)
  have h2 : WithZero.log (valV T.V (algebraMap T.V T.Fr t)) < 0 :=
    (WithZero.log_lt_iff_lt_exp hne).2 (by simpa using h1)
  omega


variable {Xo c} in
theorem chart_ties {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hie : EmbOK T V ie)
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y) :
    (∀ t, V.Ge 0 ((ie.comp (algebraMap T.V T.Fr)) t)) ∧
    (∀ t, V.v ((ie.comp (algebraMap T.V T.Fr)) t) = 0 → IsUnit t) ∧
    (∀ i, Y.B.G.F i = MvPowerSeries.map (ie.comp (algebraMap T.V T.Fr)) (C3.FT i)) ∧
    (∀ a i, Y.B.A.act a i = MvPowerSeries.map (ie.comp (algebraMap T.V T.Fr)) (C3.actT a i)) := by
  have hl0 : ((V.l : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
  have hvl : (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) ≠ 0 := by
    intro h0
    have := hie _ hl0
    rw [map_natCast, V.v_l, h0, div_zero] at this
    simp at this
  have hvl' : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have := vV_algebraMap_nonneg T (V.l : T.V)
    rw [map_natCast] at this
    exact lt_of_le_of_ne (by exact_mod_cast this) (Ne.symm hvl)
  refine ⟨fun t => embIntSt_holds T C V ie hie t, fun t ht => ?_, fun i => ?_, fun a i => ?_⟩
  · by_contra hu
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [map_zero, V.v.map_zero] at ht
      exact WithTop.top_ne_zero ht
    have hne : algebraMap T.V T.Fr t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 ht0
    have h1 := hie _ hne
    rw [RingHom.comp_apply] at ht
    rw [ht] at h1
    have h2 : (0 : ℝ) = (vV T.V (algebraMap T.V T.Fr t) : ℝ) / (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) :=
      WithTop.coe_injective (by simpa using h1)
    have h3 : (0 : ℝ) < (vV T.V (algebraMap T.V T.Fr t) : ℝ) := by exact_mod_cast vV_pos T hu ht0
    have := div_pos h3 hvl'
    linarith
  · rw [hY.F i]
    have e : (a3B C3).G.F i = MvPowerSeries.map (algebraMap T.V T.Fr) (C3.FT i) := C3.gen.1.1 i
    rw [e]
    ext mu
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [hY.act a i]
    have e : (a3B C3).A.act a i = MvPowerSeries.map (algebraMap T.V T.Fr) (C3.actT a i) := C3.gen.1.2.1 a i
    rw [e]
    ext mu
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]




end Chart

end UpFBr

end Formalism.L2.FormalSeriesBounds

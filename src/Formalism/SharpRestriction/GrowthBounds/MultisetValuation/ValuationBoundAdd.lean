module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem pivot {K κ : Type*} [Field K] (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (f : κ → K) (s : Finset κ) :
    (∃ k ∈ s, f k ≠ 0) → ∃ k0 ∈ s, f k0 ≠ 0 ∧ ∀ k ∈ s, f k / f k0 ∈ R := by
  classical
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | insert a s ha ih =>
    intro h
    by_cases hs : ∃ k ∈ s, f k ≠ 0
    · obtain ⟨k0, hk0, hfk0, hR0⟩ := ih hs
      by_cases hfa : f a / f k0 ∈ R
      · refine ⟨k0, Finset.mem_insert_of_mem hk0, hfk0, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hfa
        · exact hR0 k hk
      · have hinv : f k0 / f a ∈ R := by
          have := (hR (f a / f k0)).resolve_left hfa
          rwa [inv_div] at this
        have hfa0 : f a ≠ 0 := by
          intro h0; apply hfa; rw [h0, zero_div]; exact R.zero_mem
        refine ⟨a, Finset.mem_insert_self a s, hfa0, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · rw [div_self hfa0]; exact R.one_mem
        · have : f k / f a = (f k / f k0) * (f k0 / f a) := by field_simp
          rw [this]; exact R.mul_mem (hR0 k hk) hinv
    · push_neg at hs
      have hfa0 : f a ≠ 0 := by
        obtain ⟨k, hk, hfk⟩ := h
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hfk
        · exact absurd (hs k hk) hfk
      refine ⟨a, Finset.mem_insert_self a s, hfa0, ?_⟩
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · rw [div_self hfa0]; exact R.one_mem
      · rw [hs k hk, zero_div]; exact R.zero_mem

private theorem coeff_mem_range_algebraMap_of_linearIndependent {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0) {κ : Type*} (s : Finset κ) (z : κ → V)
    (hind : ∀ w : s → K, ∑ k : s, w k • z k = 0 → w = 0)
    (a : κ → Kc) (y : V) (hy : ι y = ∑ k ∈ s, a k • ι (z k)) (k0 : s) :
    a k0 ∈ Set.range (algebraMap K Kc) := by
  classical
  let T : (s → K) →ₗ[K] V :=
    { toFun := fun w => ∑ k : s, w k • z k
      map_add' := fun w w' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp [Finset.smul_sum, smul_smul] }
  let φ : M → Module.Dual K (s → K) := fun m => (π m).comp T
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    have h1 : (Submodule.span K (Set.range φ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      have hT : T w = 0 := hsep _ (fun m => hw (φ m) (Submodule.subset_span ⟨m, rfl⟩))
      simpa using hind w hT
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range φ))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hmem : (LinearMap.proj k0 : (s → K) →ₗ[K] K) ∈ Submodule.span K (Set.range φ) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  have hz : ∀ k : s, (∑ m ∈ l.support, l m * π m (z k)) = if k = k0 then 1 else 0 := by
    intro k
    have h3 := congrArg (fun f : Module.Dual K (s → K) => f (Pi.single k 1)) hl
    have hT : ∀ m, φ m (Pi.single k 1) = π m (z k) := by
      intro m; simp [φ, T, Pi.single_apply, ite_smul]
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, hT, smul_eq_mul] at h3
    rw [h3, Pi.single_apply]
    simp [eq_comm]
  have hy' : ι y = ∑ k : s, a k • ι (z k) := by
    rw [hy]; exact (Finset.sum_coe_sort s (fun k => a k • ι (z k))).symm
  have e1 : ∀ m, algebraMap K Kc (π m y) = ∑ k : s, a k * algebraMap K Kc (π m (z k)) := by
    intro m; rw [← hπ, hy', map_sum]; simp [hπ]
  refine ⟨∑ m ∈ l.support, l m * π m y, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h4 : ∀ k : s, ∑ m ∈ l.support, algebraMap K Kc (l m) * (a k * algebraMap K Kc (π m (z k))) =
      a k * algebraMap K Kc (if k = k0 then 1 else 0) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hz k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun k _ => h4 k)]
  simp

theorem descent_core {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0)
    (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R)
    (A : AddSubgroup Kc) (hA : ∀ r ∈ R, ∀ a ∈ A, algebraMap K Kc r * a ∈ A) {κ : Type*} [DecidableEq κ] :
    ∀ (n : ℕ) (s : Finset κ), s.card = n → ∀ (z : κ → V) (a : κ → Kc), (∀ k ∈ s, a k ∈ A) → ∀ y : V,
      ι y = ∑ k ∈ s, a k • ι (z k) →
      ∃ c : κ → K, (∀ k ∈ s, algebraMap K Kc (c k) ∈ A) ∧ y = ∑ k ∈ s, c k • z k := by
  classical
  have hιinj : ∀ v : V, ι v = 0 → v = 0 := fun v hv => hsep v (fun m => by
    have h0 := hπ m v
    rw [hv, map_zero] at h0
    exact (algebraMap K Kc).injective (h0.symm.trans (map_zero _).symm))
  intro n
  induction n with
  | zero =>
    intro s hs z a _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    refine ⟨0, by simp, ?_⟩
    simp only [Finset.sum_empty] at hy ⊢
    exact hιinj y hy
  | succ n ih =>
    intro s hs z a ha y hy
    by_cases hdep : ∃ b : κ → K, ∑ k ∈ s, b k • z k = 0 ∧ ∃ k ∈ s, b k ≠ 0
    · obtain ⟨b, hb0, hbne⟩ := hdep
      obtain ⟨k0, hk0, hbk0, hbR⟩ := pivot R hR b s hbne
      have hzk0 : ι (z k0) = - ∑ k ∈ s.erase k0, algebraMap K Kc (b k / b k0) • ι (z k) := by
        have h1 : ∑ k ∈ s, (b k / b k0) • z k = 0 := by
          simp_rw [div_eq_mul_inv, mul_comm _ (b k0)⁻¹, mul_smul, ← Finset.smul_sum, hb0, smul_zero]
        rw [← Finset.add_sum_erase s _ hk0, div_self hbk0, one_smul] at h1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_sum]
        simp only [hιs]
      have hy' : ι y = ∑ k ∈ s.erase k0,
          (a k - algebraMap K Kc (b k / b k0) * a k0) • ι (z k) := by
        rw [hy, ← Finset.add_sum_erase s _ hk0, hzk0, smul_neg, Finset.smul_sum,
          ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, sub_smul, mul_comm (a k0)]
        abel
      have hcard : (s.erase k0).card = n := by
        rw [Finset.card_erase_of_mem hk0, hs]; rfl
      obtain ⟨c, hcA, hyc⟩ := ih (s.erase k0) hcard z
        (fun k => a k - algebraMap K Kc (b k / b k0) * a k0)
        (fun k hk => A.sub_mem (ha k (Finset.mem_of_mem_erase hk))
          (hA _ (hbR k (Finset.mem_of_mem_erase hk)) _ (ha k0 hk0))) y hy'
      refine ⟨fun k => if k = k0 then 0 else c k, fun k hk => ?_, ?_⟩
      · by_cases hkk : k = k0
        · simp only [hkk, if_true, map_zero]; exact A.zero_mem
        · simp only [hkk, if_false]; exact hcA k (Finset.mem_erase.2 ⟨hkk, hk⟩)
      · rw [← Finset.add_sum_erase s _ hk0, hyc]
        simp only [if_true, zero_smul, zero_add]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_neg (Finset.ne_of_mem_erase hk)]
    · push_neg at hdep
      have hind : ∀ w : s → K, ∑ k : s, w k • z k = 0 → w = 0 := by
        intro w hw
        have h5 := hdep (fun k => if h : k ∈ s then w ⟨k, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort]; simpa using hw)
        funext k
        simpa using h5 k k.2
      have hr : ∀ k (hk : k ∈ s), a k ∈ Set.range (algebraMap K Kc) := fun k hk =>
        coeff_mem_range_algebraMap_of_linearIndependent ι hιs π πc hπ hsep s z hind a y hy ⟨k, hk⟩
      let c : κ → K := fun k => if hk : k ∈ s then (hr k hk).choose else 0
      have hc : ∀ k ∈ s, algebraMap K Kc (c k) = a k := fun k hk => by
        simp only [c, dif_pos hk]; exact (hr k hk).choose_spec
      refine ⟨c, fun k hk => ?_, ?_⟩
      · rw [hc k hk]; exact ha k hk
      · have h6 : ι (y - ∑ k ∈ s, c k • z k) = 0 := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sub, map_sum, hy, sub_eq_zero]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hιs, hc k hk]
        exact sub_eq_zero.1 (hιinj _ h6)

end Formalism.MainNotions.FormalGroupSystem.Pf
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem pKc_ne : (p : Y.Kc) ≠ 0 := by
  rw [← map_natCast (algebraMap (K0 p) Y.Kc)]
  exact (map_ne_zero (algebraMap (K0 p) Y.Kc)).mpr (WittVector.FractionRing.p_nonzero p (kb p))

include Y in
theorem pK_ne : (p : X.G.Kf) ≠ 0 := by
  intro h
  apply pKc_ne Y
  rw [← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]

theorem geC_zero (g : ℝ) : Y.geC 0 g := by
  intro a b hb _
  rw [zero_pow hb.ne', zero_mul]
  exact Y.Oc.zero_mem

theorem geC_neg {x : Y.Kc} {g : ℝ} (h : Y.geC x g) : Y.geC (-x) g := by
  intro a b hb hab
  rw [neg_pow, mul_assoc]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem (Y.Oc.neg_mem Y.Oc.one_mem) _) (h a b hb hab)

theorem geC_mul_shift {x y : Y.Kc} {g : ℝ} (k : ℤ) (hx : Y.geC x g) (hy : y * (p : Y.Kc) ^ k ∈ Y.Oc) :
    Y.geC (y * x) (g - k) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hx' := hx (a + k * b) b hb (by push_cast; nlinarith)
  have e : (y * x) ^ b * (p : Y.Kc) ^ (-a) =
      (y * (p : Y.Kc) ^ k) ^ b * (x ^ b * (p : Y.Kc) ^ (-(a + k * b))) := by
    have h1 : (p : Y.Kc) ^ (-a) = ((p : Y.Kc) ^ k) ^ b * (p : Y.Kc) ^ (-(a + k * b)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp]
      congr 1
      ring
    rw [h1]
    ring
  rw [e]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem hy _) hx'

theorem geC_mul_Oc {x y : Y.Kc} {g : ℝ} (hx : Y.geC x g) (hy : y ∈ Y.Oc) : Y.geC (y * x) g := by
  intro a b hb hab
  rw [mul_pow, mul_assoc]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem hy _) (hx a b hb hab)

theorem valuation_bound_add {x y : Y.Kc} {g : ℝ} (hy0 : y ≠ 0) (h : x / y ∈ Y.Oc) (hy : Y.geC y g) : Y.geC (x + y) g := by
  have e : x + y = (x / y + 1) * y := by
    field_simp
  rw [e]
  exact geC_mul_Oc Y hy (Y.Oc.add_mem h Y.Oc.one_mem)

theorem geC_add {x y : Y.Kc} {g : ℝ} (hx : Y.geC x g) (hy : Y.geC y g) : Y.geC (x + y) g := by
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]
    exact hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]
    exact hy
  rcases Y.Oc_val (x / y) with h | h
  · exact valuation_bound_add Y hy0 h hy
  · rw [add_comm]
    refine valuation_bound_add Y hx0 ?_ hx
    rw [inv_div] at h
    exact h

def geCgrp (g : ℝ) : AddSubgroup Y.Kc where
  carrier := {x | Y.geC x g}
  add_mem' := fun hx hy => geC_add Y hx hy
  zero_mem' := geC_zero Y g
  neg_mem' := fun hx => geC_neg Y hx

def RK (X : Sys p) : Subring X.G.Kf := (algebraMap X.G.O X.G.Kf).range

theorem mem_intKF {x : X.G.Kf} : x ∈ X.intK ↔ x ∈ RK X := by
  simp only [Sys.intK, RK, LinearMap.mem_range, RingHom.mem_range, Algebra.linearMap_apply]

theorem mem_RK_iff {x : X.G.Kf} : x ∈ RK X ↔ algebraMap X.G.Kf Y.Kc x ∈ Y.Oc := by
  rw [Y.Oc_K, mem_intKF]

include Y in
theorem RK_val (x : X.G.Kf) : x ∈ RK X ∨ x⁻¹ ∈ RK X := by
  rw [mem_RK_iff Y, mem_RK_iff Y, map_inv₀]
  exact Y.Oc_val _

theorem zpow_mem_RK {a : X.G.Kf} (h1 : a ∈ RK X) (h2 : a⁻¹ ∈ RK X) (z : ℤ) : a ^ z ∈ RK X := by
  rcases z with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_mem h1 n
  · rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h2 _

abbrev vpK (X : Sys p) : X.G.Kf := algebraMap X.G.O X.G.Kf X.vp

theorem vpK_inv_not_mem (h0 : vpK X ≠ 0) : (vpK X)⁻¹ ∉ RK X := by
  intro h
  obtain ⟨o, ho⟩ := RingHom.mem_range.mp (show (vpK X)⁻¹ ∈ (algebraMap X.G.O X.G.Kf).range from h)
  have hu : IsUnit (1 - X.vp * o) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      (mem_nonunits_iff.mpr fun h' => X.unif.1 (isUnit_of_mul_isUnit_left h'))
  have h1 : algebraMap X.G.O X.G.Kf (1 - X.vp * o) = 0 := by
    rw [map_sub, map_one, map_mul, ho, mul_inv_cancel₀ h0, sub_self]
  exact (hu.map (algebraMap X.G.O X.G.Kf)).ne_zero h1

theorem dvd_of_not_unit {o : X.G.O} (h : ¬ IsUnit o) : X.vp ∣ o := by
  have hm : o ∈ IsLocalRing.maximalIdeal X.G.O :=
    (IsLocalRing.mem_maximalIdeal o).mpr (mem_nonunits_iff.mpr h)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer X.vp).mp X.unif,
    Ideal.mem_span_singleton] at hm
  exact hm


include Y in
theorem RK_or (x : X.G.Kf) : x ∈ RK X ∨ ∃ o : X.G.O, x⁻¹ = vpK X * algebraMap X.G.O X.G.Kf o := by
  rcases RK_val Y x with h | h
  · exact Or.inl h
  · by_cases hx : x ∈ RK X
    · exact Or.inl hx
    · right
      obtain ⟨o', ho'⟩ := h
      have hnu : ¬ IsUnit o' := by
        rintro ⟨w, rfl⟩
        apply hx
        refine ⟨↑w⁻¹, ?_⟩
        rw [map_units_inv, ho', inv_inv]
      obtain ⟨o, rfl⟩ := dvd_of_not_unit hnu
      exact ⟨o, by rw [← ho', map_mul]⟩

theorem p_eq : ∃ u : X.G.Kf, u ∈ RK X ∧ u⁻¹ ∈ RK X ∧ u ≠ 0 ∧ (p : X.G.Kf) * u = vpK X ^ X.eO := by
  obtain ⟨u, hu⟩ := X.eO_spec
  refine ⟨algebraMap X.G.O X.G.Kf u, ⟨u, rfl⟩, ⟨↑u⁻¹, map_units_inv (algebraMap X.G.O X.G.Kf) u⟩,
    (u.isUnit.map (algebraMap X.G.O X.G.Kf)).ne_zero, ?_⟩
  have h := congrArg (algebraMap X.G.O X.G.Kf) hu
  rw [map_mul, map_pow, map_natCast] at h
  exact h

include Y in
theorem eO_zero_of_vpK_zero (h0 : vpK X = 0) : X.eO = 0 := by
  obtain ⟨u, -, -, hu0, hu⟩ := p_eq (X := X)
  by_contra hne
  rw [h0, zero_pow hne] at hu
  exact mul_ne_zero (pK_ne Y) hu0 hu

include Y in
theorem vsc_ne_zero (g : ℝ) : X.vsc g ≠ 0 := by
  unfold Sys.vsc
  by_cases h0 : vpK X = 0
  · rw [eO_zero_of_vpK_zero Y h0]
    simp
  · exact zpow_ne_zero _ h0

theorem mem_scale_iff {M : Type*} [AddCommGroup M] [Module X.G.Kf M] [Module X.G.O M] [IsScalarTower X.G.O X.G.Kf M]
    (c : X.G.Kf) (N : Submodule X.G.O M) (x : M) : x ∈ scale c N ↔ ∃ y ∈ N, c • y = x := by
  simp only [scale, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]

theorem exists_ab (e : ℕ) (g : ℝ) : ∃ (a : ℤ) (b : ℕ), 0 < b ∧ (a : ℝ) ≤ g * b ∧ (⌈g * (e : ℝ)⌉ - 1) * (b : ℤ) - e * a < 0 := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨⌊g⌋, 1, one_pos, by simpa using Int.floor_le g, ?_⟩
    simp
  · obtain ⟨c, hc⟩ : ∃ c : ℤ, c = ⌈g * (e : ℝ)⌉ := ⟨_, rfl⟩
    rw [← hc]
    have hc1 : ((c : ℝ) - 1) < g * e := by
      have := Int.ceil_lt_add_one (g * (e : ℝ))
      rw [← hc] at this
      linarith
    have hδ : 0 < g * e - ((c : ℝ) - 1) := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (g * e - ((c : ℝ) - 1)))
    have hk0' : (0 : ℝ) < k := lt_trans (by positivity) hk
    have hk0 : 0 < k := by exact_mod_cast hk0'
    have hkδ : 1 < (k : ℝ) * (g * e - ((c : ℝ) - 1)) := by
      have h1 : 1 / (g * e - ((c : ℝ) - 1)) * (g * e - ((c : ℝ) - 1)) = 1 := by field_simp
      nlinarith
    refine ⟨⌊g * ((e * k : ℕ) : ℝ)⌋, e * k, Nat.mul_pos he hk0, Int.floor_le _, ?_⟩
    have hfl : (c - 1) * (k : ℤ) < ⌊g * ((e * k : ℕ) : ℝ)⌋ := by
      rw [Int.lt_iff_add_one_le, Int.le_floor]
      push_cast
      nlinarith
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    push_cast at hfl ⊢
    nlinarith [mul_lt_mul_of_pos_left hfl he']

theorem vGeK_of_geC (c : X.G.Kf) (g : ℝ) (h : Y.geC (algebraMap X.G.Kf Y.Kc c) g) : X.vGeK c g := by
  have hv : X.vsc g ≠ 0 := vsc_ne_zero Y g
  have hvsc : X.vsc g = vpK X ^ ⌈g * (X.eO : ℝ)⌉ := rfl
  suffices hz : c * (X.vsc g)⁻¹ ∈ RK X by
    unfold Sys.vGeK
    rw [mem_scale_iff]
    refine ⟨c * (X.vsc g)⁻¹, (mem_intKF (X := X)).mpr hz, ?_⟩
    rw [smul_eq_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  by_contra hz
  rcases RK_or Y (c * (X.vsc g)⁻¹) with hz' | ⟨o, ho⟩
  · exact hz hz'
  have hz0 : c * (X.vsc g)⁻¹ ≠ 0 := fun h0 => hz (h0 ▸ (RK X).zero_mem)
  have hπ : vpK X ≠ 0 := fun h0 => by
    rw [h0, zero_mul, inv_eq_zero] at ho
    exact hz0 ho
  have hoK : algebraMap X.G.O X.G.Kf o ≠ 0 := fun h0 => by
    rw [h0, mul_zero, inv_eq_zero] at ho
    exact hz0 ho
  obtain ⟨u, hu1, hu2, hu0, hpu⟩ := p_eq (X := X)
  obtain ⟨a, b, hb, hab, hN⟩ := exists_ab X.eO g
  have hw : c ^ b * (p : X.G.Kf) ^ (-a) ∈ RK X := by
    rw [mem_RK_iff Y, map_mul, map_pow, map_zpow₀, map_natCast]
    exact h a b hb hab
  set m : ℤ := ⌈g * (X.eO : ℝ)⌉ with hm
  set Ok := algebraMap X.G.O X.G.Kf o with hOk
  have hc : c = (vpK X * Ok)⁻¹ * vpK X ^ m := by
    have h1 : c * (X.vsc g)⁻¹ = (vpK X * Ok)⁻¹ := by rw [← ho, inv_inv]
    calc c = c * (X.vsc g)⁻¹ * X.vsc g := by rw [mul_assoc, inv_mul_cancel₀ hv, mul_one]
      _ = (vpK X * Ok)⁻¹ * vpK X ^ m := by rw [h1, hvsc]
  have hp : (p : X.G.Kf) = vpK X ^ X.eO * u⁻¹ := by
    rw [← hpu, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  have hid : c ^ b * (p : X.G.Kf) ^ (-a) * (Ok ^ b * u ^ (-a)) =
      vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) := by
    rw [hc, hp]
    calc ((vpK X * Ok)⁻¹ * vpK X ^ m) ^ b * (vpK X ^ X.eO * u⁻¹) ^ (-a) * (Ok ^ b * u ^ (-a))
        = (vpK X ^ (-(b : ℤ)) * vpK X ^ (m * b) * vpK X ^ ((X.eO : ℤ) * -a)) *
            (Ok ^ (-(b : ℤ)) * Ok ^ (b : ℤ)) * (u ^ a * u ^ (-a)) := by
          simp only [← zpow_natCast, mul_zpow, inv_zpow', ← zpow_mul, neg_neg]
          ring
      _ = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) := by
          rw [← zpow_add₀ hπ, ← zpow_add₀ hπ, ← zpow_add₀ hoK, ← zpow_add₀ hu0, neg_add_cancel,
            add_neg_cancel, zpow_zero, zpow_zero, mul_one, mul_one]
          congr 1
          ring
  have hPN : vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) ∈ RK X := by
    rw [← hid]
    exact (RK X).mul_mem hw ((RK X).mul_mem ((RK X).pow_mem ⟨o, rfl⟩ _) (zpow_mem_RK hu1 hu2 _))
  have hk : 0 ≤ -((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) - 1 := by linarith
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk
  have hPn : vpK X ^ (n : ℤ) ∈ RK X := by
    rw [zpow_natCast]
    exact (RK X).pow_mem ⟨X.vp, rfl⟩ _
  have hinv : (vpK X)⁻¹ = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) * vpK X ^ (n : ℤ) := by
    rw [← zpow_add₀ hπ, ← hn, ← zpow_neg_one]
    congr 1
    ring
  exact vpK_inv_not_mem hπ (by rw [hinv]; exact (RK X).mul_mem hPN hPn)

end Formalism.MainNotions.FormalGroupSystem.Pf

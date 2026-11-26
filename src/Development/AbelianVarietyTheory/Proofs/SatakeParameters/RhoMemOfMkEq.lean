module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjugateModelExtremalDualParameter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedMemOfOrbitHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedMemOfOrbitHeight
open Submodule MulAction

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

def WA (V : ι → Submodule ℂ M) (A : Set ι) : Submodule ℂ M := ⨆ (j) (_ : j ∈ A), V j

theorem WA_mono (V : ι → Submodule ℂ M) {A B : Set ι} (h : A ⊆ B) : WA V A ≤ WA V B :=
  biSup_mono fun _ hj => h hj

theorem le_WA (V : ι → Submodule ℂ M) {A : Set ι} {j : ι} (hj : j ∈ A) : V j ≤ WA V A :=
  le_iSup₂_of_le j hj le_rfl

theorem WA_union (V : ι → Submodule ℂ M) (A B : Set ι) : WA V (A ∪ B) = WA V A ⊔ WA V B :=
  iSup_union

theorem iSup_orbit (V : ι → Submodule ℂ M) (i : ι) :
    (⨆ g : G, V (g • i)) = WA V (orbit G i) := by
  apply le_antisymm
  · exact iSup_le fun g => le_WA V (mem_orbit i g)
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨g, rfl⟩ := hj
    exact le_iSup (fun g : G => V (g • i)) g

theorem orbit_stable (i : ι) (g : G) {j : ι} (hj : j ∈ orbit G i) : g • j ∈ orbit G i := by
  obtain ⟨h, rfl⟩ := hj
  exact ⟨g * h, mul_smul g h i⟩

theorem map_WA_le (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (g : G) {x : M} (hx : x ∈ WA V A) :
    π g x ∈ WA V A := by
  have : (WA V A).map (π g) ≤ WA V A := by
    unfold WA
    rw [Submodule.map_iSup]
    refine iSup_le fun j => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hj => (hπ g j).trans (le_WA V (hA g j hj))
  exact this (Submodule.mem_map_of_mem hx)

theorem fixed_part (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A B : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (hB : ∀ (g : G), ∀ j ∈ B, g • j ∈ B)
    (hAB : Disjoint A B) {a b : M} (ha : a ∈ WA V A) (hb : b ∈ WA V B)
    (hfix : ∀ g, π g (a + b) = a + b) : ∀ g, π g a = a := by
  intro g
  have h1 : π g a - a ∈ WA V A := sub_mem (map_WA_le π V hπ hA g ha) ha
  have h2 : π g a - a ∈ WA V B := by
    have e : π g a - a = b - π g b := by
      rw [sub_eq_sub_iff_add_eq_add, ← map_add (f := _), hfix g, add_comm]
    rw [e]
    exact sub_mem hb (map_WA_le π V hπ hB g hb)
  have hd : Disjoint (WA V A) (WA V B) := hV.disjoint_biSup_biSup hAB
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ h1 h2)

theorem exists_comp (V : ι → Submodule ℂ M) (hV : iSupIndep V) (htop : (⨆ i, V i) = ⊤) :
    ∃ c : ι → M →ₗ[ℂ] M, (∀ i w, c i w ∈ V i) ∧ (∀ i v, v ∈ V i → c i v = v) ∧
      (∀ i j v, i ≠ j → v ∈ V j → c i v = 0) ∧ (∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w) := by
  classical
  letI := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV htop).chooseDecomposition
  refine ⟨fun i => (V i).subtype ∘ₗ (DirectSum.component ℂ ι (fun i => ↥(V i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv V).toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro i w; simp
  · intro i v hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_same V hv
  · intro i j v hij hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_ne V hv hij.symm
  · intro w
    refine ⟨(DirectSum.decompose V w).support, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact (DirectSum.sum_support_decompose V w).symm

end GlobalTheory.GradedFixed

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

section comp

variable (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (c : ι → M →ₗ[ℂ] M)
  (hc1 : ∀ i w, c i w ∈ V i) (hc2 : ∀ i v, v ∈ V i → c i v = v)
  (hc3 : ∀ i j v, i ≠ j → v ∈ V j → c i v = 0) (hc4 : ∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w)
include hc1 hc2 hc3 hc4

theorem comp_equivariant (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (g : G) (i : ι) (w : M) : c (g • i) (π g w) = π g (c i w) := by
  obtain ⟨F, hF⟩ := hc4 w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hF, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem : π g (c j w) ∈ V (g • j) := hπ g j (Submodule.mem_map_of_mem (hc1 j w))
  by_cases hij : j = i
  · subst hij
    rw [hc2 _ _ hmem, hc2 _ _ (hc1 j w)]
  · rw [hc3 _ _ _ (fun h => hij (smul_left_cancel g h).symm) hmem, hc3 _ _ _ (Ne.symm hij) (hc1 j w),
      map_zero]

omit hc1 hc2 hc4 in
theorem comp_outside {A : Set ι} {x : M} (hx : x ∈ WA V A) {l : ι} (hl : l ∉ A) : c l x = 0 := by
  have : WA V A ≤ LinearMap.ker (c l) :=
    iSup₂_le fun j hj v hv => LinearMap.mem_ker.mpr (hc3 l j v (fun h => hl (h ▸ hj)) hv)
  exact LinearMap.mem_ker.mp (this hx)

omit hc1 hc2 hc3 in
theorem eq_zero_of_comp {x : M} (h : ∀ l, c l x = 0) : x = 0 := by
  obtain ⟨F, hF⟩ := hc4 x
  rw [hF]
  exact Finset.sum_eq_zero fun l _ => h l

omit hc2 hc4 in
theorem mem_WA_of_sum {A : Set ι} {F : Finset ι} (hF : ∀ j ∈ F, j ∈ A) (w : M)
    (hw : w = ∑ i ∈ F, c i w) : w ∈ WA V A := by
  rw [hw]
  exact Submodule.sum_mem _ fun j hj => le_WA V (hF j hj) (hc1 j w)

theorem mem_span_of_fixed (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (hline : ∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) (i : ι) {x y : M}
    (hx : ∀ g, π g x = x) (hy : ∀ g, π g y = y) (hxO : x ∈ WA V (orbit G i))
    (hyO : y ∈ WA V (orbit G i)) (hy0 : y ≠ 0) : x ∈ Submodule.span ℂ {y} := by
  obtain ⟨F, hF⟩ := hc4 y
  obtain ⟨k, -, hk⟩ : ∃ k ∈ F, c k y ≠ 0 := by
    by_contra! h
    exact hy0 (by rw [hF]; exact Finset.sum_eq_zero h)
  have hkO : k ∈ orbit G i := by
    by_contra hkO
    exact hk (comp_outside V c hc3 hyO hkO)
  obtain ⟨v, hv⟩ := hline k
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hv (hc1 k y))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv (hc1 k x))
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hk (by rw [← hb, zero_smul])
  set z := x - (a / b) • y with hz
  have hzk : c k z = 0 := by
    rw [hz, map_sub, map_smul, ← ha, ← hb, smul_smul, div_mul_cancel₀ a hb0, sub_self]
  have hzfix : ∀ g, π g z = z := fun g => by rw [hz, map_sub, map_smul, hx, hy]
  have hzO : z ∈ WA V (orbit G i) := sub_mem hxO (Submodule.smul_mem _ _ hyO)
  have hz0 : z = 0 := by
    refine eq_zero_of_comp c hc4 fun l => ?_
    by_cases hl : l ∈ orbit G i
    · obtain ⟨g0, rfl⟩ := hkO
      obtain ⟨g1, rfl⟩ := hl
      have e : g1 • i = (g1 * g0⁻¹) • (g0 • i) := by rw [smul_smul, inv_mul_cancel_right]
      simp only at hzk ⊢
      rw [e, ← hzfix (g1 * g0⁻¹), comp_equivariant π V c hc1 hc2 hc3 hc4 hπ, hzk, map_zero]
    · exact comp_outside V c hc3 hzO hl
  rw [hz, sub_eq_zero] at hz0
  rw [hz0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)

end comp

end GlobalTheory.GradedFixed

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem mem_of_orbits (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) (S : Submodule ℂ M) (F : Finset ι) :
    (∀ i ∈ F, ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
    ∀ u, (∀ g, π g u = u) → u ∈ WA V (⋃ i ∈ F, orbit G i) → u ∈ S := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _ u _ hu
    have : u = 0 := by simpa [WA] using hu
    rw [this]; exact zero_mem S
  | insert i F hi ih =>
    intro hT u hu huF
    have hset : (⋃ j ∈ insert i F, orbit G j) = orbit G i ∪ ((⋃ j ∈ F, orbit G j) \ orbit G i) := by
      rw [Finset.set_biUnion_insert, Set.union_diff_self]
    rw [hset, WA_union, Submodule.mem_sup] at huF
    obtain ⟨a, ha, b, hb, rfl⟩ := huF
    have hA : ∀ (g : G), ∀ j ∈ orbit G i, g • j ∈ orbit G i := fun g j hj => orbit_stable i g hj
    have hU : ∀ (g : G), ∀ j ∈ (⋃ k ∈ F, orbit G k), g • j ∈ (⋃ k ∈ F, orbit G k) := by
      intro g j hj
      obtain ⟨k, hk, hjk⟩ := Set.mem_iUnion₂.mp hj
      exact Set.mem_iUnion₂.mpr ⟨k, hk, orbit_stable k g hjk⟩
    have hB : ∀ (g : G), ∀ j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i),
        g • j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i) := by
      intro g j hj
      exact ⟨hU g j hj.1, fun h => hj.2 (by simpa using orbit_stable i g⁻¹ h)⟩
    have hAB : Disjoint (orbit G i) ((⋃ k ∈ F, orbit G k) \ orbit G i) := Set.disjoint_sdiff_right
    have hafix := fixed_part π V hV hπ hA hB hAB ha hb hu
    have hbfix : ∀ g, π g b = b :=
      fixed_part π V hV hπ hB hA hAB.symm hb ha (fun g => by rw [add_comm]; exact hu g)
    exact add_mem (hT i (Finset.mem_insert_self i F) a hafix ha)
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)) b hbfix (WA_mono V Set.diff_subset hb))

end GlobalTheory.GradedFixed

namespace GlobalTheory


open GlobalTheory.GradedFixed in
theorem fixed_mem_of_orbit_height : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  intro G ι M _ _ _ _ π V hV htop hline hπ μ hμ S hS hstep
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := GradedFixed.exists_comp V hV htop
  have hsum : ∀ (p : ι → Prop) (u : M), (∀ l, ¬ p l → c l u = 0) →
      (∀ i, p i → ∀ x, (∀ g, π g x = x) → x ∈ GradedFixed.WA V (orbit G i) → x ∈ S) →
      (∀ g, π g u = u) → u ∈ S := by
    classical
    intro p u hp hgood hu
    obtain ⟨F, hF⟩ := hc4 u
    have hF' : u = ∑ j ∈ F.filter p, c j u := by
      rw [Finset.sum_filter_of_ne (fun j _ h => by_contra fun hpj => h (hp j hpj))]
      exact hF
    refine GradedFixed.mem_of_orbits π V hV hπ S (F.filter p)
      (fun j hj => hgood j (Finset.mem_filter.mp hj).2) u hu ?_
    exact GradedFixed.mem_WA_of_sum V c hc1 hc3
      (fun j hj => Set.mem_iUnion₂.mpr ⟨j, hj, (mem_orbit_self j : j ∈ orbit G j)⟩) u hF'
  have key : ∀ m i, μ i = m → ∀ x, (∀ g, π g x = x) → x ∈ GradedFixed.WA V (orbit G i) → x ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi x hx hxO
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem S
    obtain ⟨v, hvS, u, hu, hvu, hvu0⟩ :=
      hstep i ⟨x, hx0, hx, by rw [GradedFixed.iSup_orbit]; exact hxO⟩
    rw [GradedFixed.iSup_orbit] at hvu
    have huW : u ∈ GradedFixed.WA V {j | μ j < μ i} := hu
    have hsub : {j | μ j < μ i} ⊆ (orbit G i)ᶜ := by
      intro j hj hjO
      obtain ⟨g, rfl⟩ := hjO
      simp [hμ] at hj
    have hcompl : ∀ (g : G), ∀ j ∈ (orbit G i)ᶜ, g • j ∈ (orbit G i)ᶜ :=
      fun g j hj hgj => hj (by simpa using GradedFixed.orbit_stable i g⁻¹ hgj)
    have hfa : ∀ g, π g (v - u) = v - u :=
      GradedFixed.fixed_part π V hV hπ (fun g j hj => GradedFixed.orbit_stable i g hj)
        hcompl disjoint_compl_right hvu (GradedFixed.WA_mono V hsub huW)
        (fun g => by rw [sub_add_cancel]; exact hS v hvS g)
    have hufix : ∀ g, π g u = u := fun g => by
      have h1 := hfa g
      rw [map_sub, hS v hvS g] at h1
      exact sub_right_injective h1
    have huS : u ∈ S := hsum (fun j => μ j < μ i) u (fun l hl => GradedFixed.comp_outside V c hc3 huW hl)
      (fun j hj => ih (μ j) (hi ▸ hj) j rfl) hufix
    have hvuS : v - u ∈ S := sub_mem hvS huS
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (GradedFixed.mem_span_of_fixed π V c hc1 hc2 hc3 hc4 hπ hline i hx hfa hxO hvu hvu0)
    rw [← hr]
    exact S.smul_mem r hvuS
  intro w hw
  exact hsum (fun _ => True) w (fun l hl => absurd trivial hl) (fun i _ => key (μ i) i rfl) hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedMemOfOrbitHeightStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_mem_of_orbit_height_separation : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  first | exact @GlobalTheory.fixed_mem_of_orbit_height | exact GlobalTheory.fixed_mem_of_orbit_height | (intros; apply GlobalTheory.fixed_mem_of_orbit_height <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

section Glue

open Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem int_entry {m : ℕ} {h : GL (Fin m) L} (hh : h ∈ GLint (Fin m) (intL L)) (i j : Fin m) :
    (h : Matrix (Fin m) (Fin m) L) i j ∈ intL L := by
  obtain ⟨k, rfl⟩ := hh; simp [Formalism.UG.bc]

theorem mul_mem_intMat {a b : ℕ} {h : GL (Fin a) L} (hh : h ∈ GLint (Fin a) (intL L)) {u : Matrix (Fin a) (Fin b) L}
    (hu : u ∈ intMat L a b) : (h : Matrix (Fin a) (Fin a) L) * u ∈ intMat L a b := by
  rw [mem_intMat] at hu ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (int_entry hh i k) (hu k j)

def lmulQ {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) :
    Matrix (Fin a) (Fin b) L ⧸ intMat L a b →+ Matrix (Fin a) (Fin b) L ⧸ intMat L a b :=
  QuotientAddGroup.map _ _
    { toFun := fun x => (h : Matrix (Fin a) (Fin a) L) * x, map_zero' := Matrix.mul_zero _,
      map_add' := Matrix.mul_add _ }
    (fun _ hu => mul_mem_intMat hh hu)

theorem lmulQ_mk {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (x : Matrix (Fin a) (Fin b) L) :
    lmulQ h hh (QuotientAddGroup.mk x) = QuotientAddGroup.mk ((h : Matrix (Fin a) (Fin a) L) * x) := rfl

theorem lmulQ_mul {a b : ℕ} (h h' : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (hh' : h' ∈ GLint (Fin a) (intL L))
    (hhh : h * h' ∈ GLint (Fin a) (intL L)) (c : Matrix (Fin a) (Fin b) L ⧸ intMat L a b) :
    lmulQ (h * h') hhh c = lmulQ h hh (lmulQ h' hh' c) := by
  induction c using QuotientAddGroup.induction_on with
  | H x => simp only [lmulQ_mk, Units.val_mul, Matrix.mul_assoc]

abbrev KT (σ : L →+* L) {a : ℕ} (J : Matrix (Fin a) (Fin a) L) : Subgroup (UJ σ J) :=
  (GLint (Fin a) (intL L)).comap (UJ σ J).subtype

def actQ (σ : L →+* L) {a b : ℕ} (J : Matrix (Fin a) (Fin a) L) :
    MulAction (KT σ J) (Matrix (Fin a) (Fin b) L ⧸ intMat L a b) where
  smul k c := lmulQ ((k : UJ σ J) : GL (Fin a) L) (Subgroup.mem_comap.1 k.2) c
  one_smul c := by
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      show lmulQ _ _ _ = _
      simp [lmulQ]
  mul_smul k k' c :=
    lmulQ_mul (((k : UJ σ J) : GL (Fin a) L)) (((k' : UJ σ J) : GL (Fin a) L)) _ _ _ c

theorem psi_ne_zero (ψ : AddChar L ℂ) (a : L) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end Glue

section Data

open Formalism.UG

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

theorem rho_add_int (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (x u : Matrix (Fin n') (Fin n) L) (hu : u ∈ intMat L n' n) : ∃ c : ℂ, c ≠ 0 ∧ ρ (x + u) s = c • ρ x s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x u)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hs u ((mem_intMat u).1 hu)] at h1
  obtain ⟨c, hc, h2⟩ : ∃ c : ℂ, c ≠ 0 ∧ ρ x s = c • ρ (x + u) s := ⟨_, psi_ne_zero ψ _, h1⟩
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem rho_mem_of_mk_eq (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    {x y : Matrix (Fin n') (Fin n) L}
    (hxy : (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk y) :
    ρ x s ∈ Submodule.span ℂ {ρ y s} := by
  have hu : -y + x ∈ intMat L n' n := QuotientAddGroup.eq.1 hxy.symm
  obtain ⟨c, -, hc⟩ := rho_add_int hP hs y (-y + x) hu
  rw [add_neg_cancel_left] at hc
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem om_rho (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (h : UJ σ (JT : Matrix (Fin n') (Fin n') L)) (hh : (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L))
    (x : Matrix (Fin n') (Fin n) L) : ω (1, h) (ρ x s) = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.norm 1 h x)
  have hfix := hP.fix 1 h (by simpa using (GLint (Fin n) (intL L)).one_mem) hh s hs
  simp only [Module.End.mul_apply] at h1
  rw [h1, hfix]
  have h1' : (((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) = 1 := by
    rw [OneMemClass.coe_one, inv_one]
  rw [h1', Units.val_one, Matrix.mul_one]

theorem step (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) (s : M) (hs0 : s ≠ 0) (hs : GlobalTheory.Hk3.LocVac ρ s)
    (hspan : Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤) (x : Matrix (Fin n') (Fin n) L)
    (hfix : ∃ w : M, w ≠ 0 ∧ (∀ h : UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L) → ω (1, h) w = w) ∧ w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) :
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, latIdx y < latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  obtain ⟨l, hl, hg⟩ := GlobalTheory.T.exists_int_gram_of_fixed_alt L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan x hfix
  obtain ⟨v, hv, u, hu, h1, h2⟩ := GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan (x - l) hg
  have hidx : latIdx (x - l) = latIdx x := by
    rw [sub_eq_add_neg]; exact (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).1 _ (neg_mem hl)
  refine ⟨v, hv, u, by rwa [hidx] at hu, ?_, h2⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨h, hh, rfl⟩
  have hm : (QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (x - l)) :
      Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) := by
    rw [QuotientAddGroup.eq, Matrix.mul_sub]
    have : -(((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l) +
        ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x = ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l := by abel
    rw [this]; exact mul_mem_intMat hh hl
  have hmem : ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} :=
    Submodule.subset_span ⟨h, hh, rfl⟩
  exact (Submodule.span_singleton_le_iff_mem _ _).2 hmem (rho_mem_of_mk_eq hP hs hm)

end Data

section Half

open Formalism.UG

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

theorem fixed_mem_span (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) (s : M) (hs0 : s ≠ 0) (hs : GlobalTheory.Hk3.LocVac ρ s)
    (hspan : Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤) (w : M)
    (hw : ∀ h : UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L) → ω (1, h) w = w) :
    w ∈ Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
  letI := actQ (b := n) σ (JT : Matrix (Fin n') (Fin n') L)
  let V : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → Submodule ℂ M := fun c =>
    Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
      (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = c ∧ w = ρ x s}
  let π : KT σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M :=
    (ω.comp (MonoidHom.inr _ _)).comp (KT σ (JT : Matrix (Fin n') (Fin n') L)).subtype
  let μ : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → ℕ := fun c => latIdx (Quotient.out c)
  let S := Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s)
  have hπ_apply : ∀ k v, π k v = ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) v := fun _ _ => rfl
  have hsmul : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) (x : Matrix (Fin n') (Fin n) L),
      k • (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) =
        QuotientAddGroup.mk ((((k : UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) := fun _ _ => rfl
  have hμmk : ∀ x, μ (QuotientAddGroup.mk x) = latIdx x := by
    intro x
    have hu : -Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) + x ∈ intMat L n' n :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n (Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n))).1 _ hu
    rw [add_neg_cancel_left] at this
    exact this.symm
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := fun x => Submodule.subset_span ⟨x, rfl, rfl⟩
  have hVle : ∀ x, V (QuotientAddGroup.mk x) ≤ Submodule.span ℂ {ρ x s} := by
    intro x
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact rho_mem_of_mk_eq hP hs hy
  have hind := GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs
  have htop : (⨆ c, V c) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_iSup_of_mem (QuotientAddGroup.mk x) (hmemV x)
  have hline : ∀ c, ∃ v : M, V c ≤ Submodule.span ℂ {v} := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x => exact ⟨ρ x s, hVle x⟩
  have hπ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, (V c).map (π k) ≤ V (k • c) := by
    intro k c
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨x, rfl, rfl⟩, rfl⟩
    rw [hπ_apply, om_rho hP hs _ (Subgroup.mem_comap.1 k.2), hsmul]
    exact hmemV _
  have hμ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, μ (k • c) = μ c := by
    intro k c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [hsmul, hμmk, hμmk]
      exact (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).2 _ (Subgroup.mem_comap.1 k.2)
  have hS : ∀ v ∈ S, ∀ k, π k v = v := by
    intro v hv k
    have hle : S ≤ LinearMap.eqLocus (π k) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      show π k (ω (g, 1) s) = ω (g, 1) s
      rw [hπ_apply, ← Module.End.mul_apply, ← map_mul]
      have e : ((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)), (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) * (g, 1) =
          (g, 1) * (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) := by
        simp
      rw [e, map_mul, Module.End.mul_apply,
        hP.fix 1 _ (by simpa using (GLint (Fin n) (intL L)).one_mem) (Subgroup.mem_comap.1 k.2) s hs]
    exact hle hv
  have hstep : ∀ c, (∃ w : M, w ≠ 0 ∧ (∀ k, π k w = w) ∧ w ∈ ⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ c), V j,
        v - u ∈ (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) ∧ v - u ≠ 0 := by
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      have horb1 : (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) ≤
          Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} := by
        refine iSup_le fun k => ?_
        rw [hsmul]
        refine (hVle _).trans ?_
        exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ⟨k, Subgroup.mem_comap.1 k.2, rfl⟩)
      have horb2 : Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ≤
          (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, hh, rfl⟩
        refine Submodule.mem_iSup_of_mem (⟨h, hh⟩ : KT σ (JT : Matrix (Fin n') (Fin n') L)) ?_
        rw [hsmul]
        exact hmemV _
      obtain ⟨w, hw0, hwf, hwm⟩ := hc
      obtain ⟨v, hv, u, hu, h1, h2⟩ := step hP s hs0 hs hspan x ⟨w, hw0, fun h hh => hwf ⟨h, hh⟩, horb1 hwm⟩
      refine ⟨v, hv, u, ?_, horb2 h1, h2⟩
      refine Submodule.span_le.2 ?_ hu
      rintro _ ⟨y, hy, rfl⟩
      refine Submodule.mem_iSup_of_mem (QuotientAddGroup.mk y) (Submodule.mem_iSup_of_mem ?_ (hmemV y))
      rw [hμmk, hμmk]
      exact hy
  exact GlobalTheory.T.invariant_mem_of_orbit_height_separation π V hind htop hline hπ μ hμ S hS hstep w (fun k => hw k (Subgroup.mem_comap.1 k.2))

end Half

end GlobalTheory.Hk3.HoweDuality

namespace GlobalTheory.Hk3

open GlobalTheory.Hk3.HoweDuality

theorem howeUnram_holds : HoweUnram := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan
  refine ⟨?_, fixed_mem_span hP s hs0 hs hspan⟩
  intro w hw
  obtain ⟨hP', hv', hsp'⟩ := GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint L ϖ σ q δ n n' JS JT ψ M ρ ω hP
  have := fixed_mem_span hP' s hs0 (hv' s hs) (hsp' s hspan) w (fun h hh => by simpa using hw h hh)
  simpa using this

end GlobalTheory.Hk3

end

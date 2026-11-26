module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepL
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepB
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepA
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepF
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvSepM
set_option linter.unusedSectionVars false

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology
open GroundTheory.Automorphic.GLnLocal (congruenceSubgroup isOpen_congruenceSubgroup isCompact_congruenceSubgroup)

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem superDiag_mul {u v : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hv : v ∈ unipB k (Fin m)) :
    superDiag (u * v) = superDiag u + superDiag v := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    GlobalTheory.LocGL.unipB_mul_apply ⟨u, hu⟩ ⟨v, hv⟩ (Finset.mem_filter.1 hj).2

theorem superDiag_one : superDiag (1 : GL (Fin m) k) = 0 := by
  have := superDiag_mul (one_mem (unipB k (Fin m))) (one_mem (unipB k (Fin m)))
  rw [mul_one] at this
  exact left_eq_add.1 this

theorem continuous_superDiag : Continuous (superDiag : GL (Fin m) k → k) := by
  unfold superDiag
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Units.continuous_val.matrix_elem i j

variable (ψ : AddChar k Circle)

def WT : Submodule ℂ (GL (Fin m) k → ℂ) where
  carrier := {f | IsWhitTest ψ f}
  zero_mem' := ⟨fun _ _ _ => by simp, IsLocallyConstant.const 0, ∅, isCompact_empty, fun _ h => (h rfl).elim⟩
  add_mem' := by
    rintro f f' ⟨h1, h2, C, hC, h3⟩ ⟨h1', h2', C', hC', h3'⟩
    refine ⟨fun u hu g => ?_, h2.add h2', C ∪ C', hC.union hC', fun g hg => ?_⟩
    · simp only [Pi.add_apply, h1 u hu g, h1' u hu g]
      ring
    · by_cases hf : f g = 0
      · have hf' : f' g ≠ 0 := fun e => hg (by simp [hf, e])
        obtain ⟨u, hu, c, hc, e⟩ := h3' g hf'
        exact ⟨u, hu, c, Or.inr hc, e⟩
      · obtain ⟨u, hu, c, hc, e⟩ := h3 g hf
        exact ⟨u, hu, c, Or.inl hc, e⟩
  smul_mem' := by
    rintro a f ⟨h1, h2, C, hC, h3⟩
    refine ⟨fun u hu g => ?_, h2.comp (a * ·), C, hC, fun g hg => h3 g fun e => hg (by simp [e])⟩
    simp only [Pi.smul_apply, smul_eq_mul, h1 u hu g]
    ring

def rhoW : Representation ℂ (GL (Fin m) k) (WT (m := m) ψ) where
  toFun x :=
    { toFun := fun f => ⟨fun g => (f : GL (Fin m) k → ℂ) (g * x), by
        obtain ⟨h1, h2, C, hC, h3⟩ := f.2
        refine ⟨fun u hu g => by beta_reduce; rw [mul_assoc, h1 u hu],
          h2.comp_continuous (continuous_id.mul continuous_const), (· * x⁻¹) '' C,
          hC.image (continuous_id.mul continuous_const), fun g hg => ?_⟩
        obtain ⟨u, hu, c, hc, e⟩ := h3 _ hg
        exact ⟨u, hu, _, ⟨c, hc, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f g
    simp
  map_mul' x y := by
    ext f g
    simp [mul_assoc]

@[simp] theorem rhoW_apply (x : GL (Fin m) k) (f : WT (m := m) ψ) (g : GL (Fin m) k) :
    (rhoW ψ x f : GL (Fin m) k → ℂ) g = (f : GL (Fin m) k → ℂ) (g * x) := rfl

variable {ψ}

theorem WT.left (x : WT (m := m) ψ) {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (g : GL (Fin m) k) :
    (x : GL (Fin m) k → ℂ) (u * g) = (ψ (superDiag u) : ℂ) * (x : GL (Fin m) k → ℂ) g := x.2.1 u hu g

theorem exists_congruence_subset {U : Set (GL (Fin m) k)} (hU : U ∈ 𝓝 (1 : GL (Fin m) k)) :
    ∃ r : ℕ, (congruenceSubgroup k m r : Set (GL (Fin m) k)) ⊆ U := by
  obtain ⟨r, -, hr⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k m).mem_iff.1 hU
  exact ⟨r, hr⟩

theorem exists_fix_congruence (x : WT (m := m) ψ) :
    ∃ r : ℕ, ∀ κ ∈ congruenceSubgroup k m r, rhoW ψ κ x = x := by
  obtain ⟨h1, h2, C, hC, h3⟩ := x.2
  have hlc : IsLocallyConstant fun p : GL (Fin m) k × GL (Fin m) k =>
      (x : GL (Fin m) k → ℂ) (p.1 * p.2) - (x : GL (Fin m) k → ℂ) p.1 :=
    (h2.comp_continuous (continuous_fst.mul continuous_snd)).sub (h2.comp_continuous continuous_fst)
  obtain ⟨U, V, -, hV, hCU, h1V, hUV⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (1 : GL (Fin m) k)))
    (hlc.isOpen_fiber 0) (by
      rintro ⟨c, y⟩ ⟨-, hy⟩
      have : y = 1 := hy
      simp [this])
  obtain ⟨r, hr⟩ := exists_congruence_subset (hV.mem_nhds (h1V rfl))
  have key : ∀ κ ∈ congruenceSubgroup k m r, ∀ g, (x : GL (Fin m) k → ℂ) g ≠ 0 →
      (x : GL (Fin m) k → ℂ) (g * κ) = (x : GL (Fin m) k → ℂ) g := by
    intro κ hκ g hg
    obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hg
    have h4 : (x : GL (Fin m) k → ℂ) (c * κ) - (x : GL (Fin m) k → ℂ) c = 0 :=
      hUV (Set.mk_mem_prod (hCU hc) (hr hκ))
    rw [mul_assoc, h1 u hu, h1 u hu, sub_eq_zero.1 h4]
  refine ⟨r, fun κ hκ => Subtype.ext (funext fun g => ?_)⟩
  rw [rhoW_apply]
  by_cases hg : (x : GL (Fin m) k → ℂ) g = 0
  · by_contra hne
    have := key κ⁻¹ (inv_mem hκ) (g * κ) (by rw [← hg]; exact hne)
    rw [mul_inv_cancel_right] at this
    exact hne this.symm
  · exact key κ hκ g hg

theorem exists_fix (x : WT (m := m) ψ) : ∃ K : Subgroup (GL (Fin m) k), IsOpen (K : Set (GL (Fin m) k)) ∧
    IsCompact (K : Set (GL (Fin m) k)) ∧ ∀ κ ∈ K, rhoW ψ κ x = x := by
  obtain ⟨r, hr⟩ := exists_fix_congruence x
  exact ⟨_, isOpen_congruenceSubgroup k m r, isCompact_congruenceSubgroup k m r, hr⟩

theorem isSmooth_rhoW : IsSmooth (rhoW (m := m) ψ) := fun x => by
  obtain ⟨K, hK, -, h⟩ := exists_fix x
  refine isOpen_iff_mem_nhds.2 fun g hg => ?_
  have hg' : rhoW ψ g x = x := hg
  refine Filter.mem_of_superset
    ((hK.preimage (continuous_const.mul continuous_id : Continuous fun y => g⁻¹ * y)).mem_nhds (by simp)) ?_
  intro y hy
  show rhoW ψ y x = x
  have : y = g * (g⁻¹ * y) := by simp
  rw [this, map_mul, Module.End.mul_apply, h (g⁻¹ * y) hy, hg']


variable (ψ) in
def Good (K : Subgroup (GL (Fin m) k)) : Prop :=
  IsOpen (K : Set (GL (Fin m) k)) ∧ IsCompact (K : Set (GL (Fin m) k)) ∧
    ∀ u ∈ unipB k (Fin m), u ∈ K → ψ (superDiag u) = 1

theorem circle_eq_one {z : Circle} (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  by_contra hz
  have h1 : (z : ℂ) ≠ 1 := fun e => hz (Subtype.ext e)
  have hb : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, (z : ℂ) ^ i‖ ≤ 2 / ‖(z : ℂ) - 1‖ := fun n => by
    rw [geom_sum_eq h1, norm_div]
    refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
    rw [norm_pow, Circle.norm_coe, one_pow, norm_one]
    norm_num
  have hq : ∀ n : ℕ, (1 / 2 : ℝ) ≤ ((z : ℂ) ^ n).re := fun n => by
    have h2 := h (2 * n)
    have h0 := h n
    have hn : ((z : ℂ) ^ n).re ^ 2 + ((z : ℂ) ^ n).im ^ 2 = 1 := by
      have : Complex.normSq ((z : ℂ) ^ n) = 1 := by
        rw [map_pow, Circle.normSq_coe, one_pow]
      rw [Complex.normSq_apply] at this
      nlinarith
    rw [Circle.coe_pow] at h0
    rw [Circle.coe_pow, mul_comm, pow_mul, sq, Complex.mul_re] at h2
    nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (2 / ‖(z : ℂ) - 1‖))
  have h3 : (n : ℝ) * (1 / 2) ≤ (∑ i ∈ Finset.range n, (z : ℂ) ^ i).re := by
    rw [Complex.re_sum]
    calc (n : ℝ) * (1 / 2) = ∑ _i ∈ Finset.range n, (1 / 2 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hq i
  have h4 := (Complex.re_le_norm _).trans (hb n)
  linarith

theorem exists_good (hψ : Continuous ψ) {U : Set (GL (Fin m) k)} (hU : U ∈ 𝓝 (1 : GL (Fin m) k)) :
    ∃ K : Subgroup (GL (Fin m) k), Good ψ K ∧ (K : Set (GL (Fin m) k)) ⊆ U := by
  have hc : Continuous fun g : GL (Fin m) k => ((ψ (superDiag g) : Circle) : ℂ).re :=
    Complex.continuous_re.comp (continuous_subtype_val.comp (hψ.comp continuous_superDiag))
  have hV : {g : GL (Fin m) k | 0 < ((ψ (superDiag g) : Circle) : ℂ).re} ∈ 𝓝 (1 : GL (Fin m) k) :=
    (isOpen_lt continuous_const hc).mem_nhds (by simp [superDiag_one])
  obtain ⟨r, hr⟩ := exists_congruence_subset (Filter.inter_mem hU hV)
  refine ⟨congruenceSubgroup k m r, ⟨isOpen_congruenceSubgroup k m r, isCompact_congruenceSubgroup k m r,
    fun u hu huK => circle_eq_one fun n => ?_⟩, fun g hg => (hr hg).1⟩
  have hp : ∀ n : ℕ, ψ (superDiag (u ^ n)) = ψ (superDiag u) ^ n := fun n => by
    induction n with
    | zero => simp [superDiag_one]
    | succ n ih => rw [pow_succ, superDiag_mul (pow_mem hu n) hu, AddChar.map_add_eq_mul, ih, pow_succ]
  rw [← hp]
  exact (hr (pow_mem huK n)).2


open Classical in
variable (ψ) in
def deltaFun (K : Subgroup (GL (Fin m) k)) (g : GL (Fin m) k) : ℂ :=
  if h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ then (ψ (superDiag h.choose) : ℂ) else 0

theorem deltaFun_mul {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u κ : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (hκ : κ ∈ K) : deltaFun ψ K (u * κ) = (ψ (superDiag u) : ℂ) := by
  have h : ∃ u' ∈ unipB k (Fin m), ∃ κ' ∈ K, u * κ = u' * κ' := ⟨u, hu, κ, hκ, rfl⟩
  rw [deltaFun, dite_eq_left h]
  obtain ⟨hu', κ', hκ', e⟩ := h.choose_spec
  set u' := h.choose
  have e2 : u'⁻¹ * u = κ' * κ⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]
  have h1 := hK.2.2 _ (mul_mem (inv_mem hu') hu) (e2 ▸ mul_mem hκ' (inv_mem hκ))
  have h2 := superDiag_mul hu' (mul_mem (inv_mem hu') hu)
  rw [mul_inv_cancel_left] at h2
  rw [h2, AddChar.map_add_eq_mul, h1, mul_one]

theorem deltaFun_eq_zero {K : Subgroup (GL (Fin m) k)} {g : GL (Fin m) k}
    (h : ¬ ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ) : deltaFun ψ K g = 0 := by
  rw [deltaFun, dite_eq_right h]

theorem deltaFun_right {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (g : GL (Fin m) k) {κ : GL (Fin m) k}
    (hκ : κ ∈ K) : deltaFun ψ K (g * κ) = deltaFun ψ K g := by
  by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
  · obtain ⟨u, hu, κ', hκ', rfl⟩ := h
    rw [mul_assoc, deltaFun_mul hK hu (mul_mem hκ' hκ), deltaFun_mul hK hu hκ']
  · rw [deltaFun_eq_zero h, deltaFun_eq_zero]
    rintro ⟨u, hu, κ', hκ', e⟩
    exact h ⟨u, hu, κ' * κ⁻¹, mul_mem hκ' (inv_mem hκ), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem isWhitTest_deltaFun {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : IsWhitTest ψ (deltaFun ψ K) := by
  refine ⟨fun v hv g => ?_, ?_, K, hK.2.1, fun g hg => ?_⟩
  · by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
    · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
      rw [← mul_assoc, deltaFun_mul hK (mul_mem hv hu) hκ, deltaFun_mul hK hu hκ, superDiag_mul hv hu,
        AddChar.map_add_eq_mul, Circle.coe_mul]
    · rw [deltaFun_eq_zero h, deltaFun_eq_zero, mul_zero]
      rintro ⟨u, hu, κ, hκ, e⟩
      exact h ⟨v⁻¹ * u, mul_mem (inv_mem hv) hu, κ, hκ, by rw [mul_assoc, ← e, inv_mul_cancel_left]⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun y => g⁻¹ * y) ⁻¹' K,
      hK.1.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
    rw [← deltaFun_right hK g hy, mul_inv_cancel_left]
  · by_contra h
    exact hg (deltaFun_eq_zero h)


open Classical in
variable (ψ) in
def delta (K : Subgroup (GL (Fin m) k)) : WT (m := m) ψ :=
  if h : Good ψ K then ⟨deltaFun ψ K, isWhitTest_deltaFun h⟩ else 0

theorem coe_delta {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) :
    (delta ψ K : GL (Fin m) k → ℂ) = deltaFun ψ K := by
  rw [delta, dite_eq_left hK]

theorem delta_mul {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u κ : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (hκ : κ ∈ K) : (delta ψ K : GL (Fin m) k → ℂ) (u * κ) = (ψ (superDiag u) : ℂ) := by
  rw [coe_delta hK, deltaFun_mul hK hu hκ]

theorem delta_eq_zero {K : Subgroup (GL (Fin m) k)} {g : GL (Fin m) k}
    (h : ¬ ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ) : (delta ψ K : GL (Fin m) k → ℂ) g = 0 := by
  by_cases hK : Good ψ K
  · rw [coe_delta hK, deltaFun_eq_zero h]
  · rw [delta, dite_eq_right hK]
    rfl

theorem rhoW_delta {K : Subgroup (GL (Fin m) k)} {κ : GL (Fin m) k} (hκ : κ ∈ K) :
    rhoW ψ κ (delta ψ K) = delta ψ K := by
  by_cases hK : Good ψ K
  · refine Subtype.ext (funext fun g => ?_)
    rw [rhoW_apply, coe_delta hK, deltaFun_right hK g hκ]
  · rw [delta, dite_eq_right hK, map_zero]

theorem apply_mul_of_fixed {x : WT (m := m) ψ} {κ : GL (Fin m) k} (h : rhoW ψ κ x = x) (g : GL (Fin m) k) :
    (x : GL (Fin m) k → ℂ) (g * κ) = (x : GL (Fin m) k → ℂ) g := by
  rw [← rhoW_apply, h]

theorem eq_smul_delta {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (x : WT (m := m) ψ)
    (hx : ∀ κ ∈ K, rhoW ψ κ x = x)
    (hs : ∀ g, (x : GL (Fin m) k → ℂ) g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ) :
    x = (x : GL (Fin m) k → ℂ) 1 • delta ψ K := by
  refine Subtype.ext (funext fun g => ?_)
  show _ = (x : GL (Fin m) k → ℂ) 1 * (delta ψ K : GL (Fin m) k → ℂ) g
  by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
  · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
    rw [delta_mul hK hu hκ, apply_mul_of_fixed (hx κ hκ), mul_comm, ← WT.left x hu, mul_one]
  · rw [delta_eq_zero h, mul_zero]
    by_contra h0
    exact h (hs g h0)

theorem mem_conj {K : Subgroup (GL (Fin m) k)} {g y : GL (Fin m) k} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    simpa [mul_assoc] using hκ
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem mem_span_delta_of_cover {K : Subgroup (GL (Fin m) k)} (hKo : IsOpen (K : Set (GL (Fin m) k)))
    (hKc : IsCompact (K : Set (GL (Fin m) k))) (D : Set (GL (Fin m) k)) (s : Finset (GL (Fin m) k)) :
    (∀ g ∈ s, g ∈ D) → ∀ x : WT (m := m) ψ, (∀ κ ∈ K, rhoW ψ κ x = x) →
      (∀ y, (x : GL (Fin m) k → ℂ) y ≠ 0 → ∃ g ∈ s, ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, y = u * g * κ) →
      x ∈ Submodule.span ℂ {y | ∃ g ∈ D, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
        y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ x _ hs
    have : x = 0 := Subtype.ext (funext fun y => by
      by_contra h
      obtain ⟨g, hg, -⟩ := hs y h
      simp at hg)
    rw [this]
    exact zero_mem _
  | insert g s _ ih =>
    intro hD x hx hs
    have hD' : ∀ g ∈ s, g ∈ D := fun a ha => hD a (Finset.mem_insert_of_mem ha)
    have hval : ∀ u ∈ unipB k (Fin m), ∀ κ ∈ K, (x : GL (Fin m) k → ℂ) (u * g * κ) =
        (ψ (superDiag u) : ℂ) * (x : GL (Fin m) k → ℂ) g := fun u hu κ hκ => by
      rw [apply_mul_of_fixed (hx κ hκ), WT.left x hu]
    by_cases hg : (x : GL (Fin m) k → ℂ) g = 0
    · refine ih hD' x hx fun y hy => ?_
      obtain ⟨a, ha, u, hu, κ, hκ, e⟩ := hs y hy
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact absurd (by rw [e, hval u hu κ hκ, hg, mul_zero]) hy
      · exact ⟨a, ha, u, hu, κ, hκ, e⟩
    · have hgood : Good ψ (K.map (MulAut.conj g).toMonoidHom) := by
        refine ⟨?_, ?_, fun u hu huK => ?_⟩
        · have : ((K.map (MulAut.conj g).toMonoidHom : Subgroup _) : Set (GL (Fin m) k)) =
              (fun y => g⁻¹ * y * g) ⁻¹' K := Set.ext fun y => mem_conj
          rw [this]
          exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
        · rw [Subgroup.coe_map]
          exact hKc.image ((continuous_const.mul continuous_id).mul continuous_const :
            Continuous fun y => g * y * g⁻¹)
        · have h1 := apply_mul_of_fixed (hx _ (mem_conj.1 huK)) g
          rw [← mul_assoc, mul_inv_cancel_left, WT.left x hu] at h1
          exact Subtype.ext ((mul_eq_right₀ hg).1 h1)
      set d := rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom)) with hd
      have hdK : ∀ κ ∈ K, rhoW ψ κ d = d := fun κ hκ => by
        have e : κ * g⁻¹ = g⁻¹ * (g * κ * g⁻¹) := by simp [mul_assoc]
        rw [hd, ← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply,
          rhoW_delta (mem_conj.2 (by simpa [mul_assoc] using hκ))]
      have h2 := ih hD' (x - (x : GL (Fin m) k → ℂ) g • d)
        (fun κ hκ => by rw [map_sub, map_smul, hx κ hκ, hdK κ hκ]) fun y hy => by
          have hy' : (x : GL (Fin m) k → ℂ) y - (x : GL (Fin m) k → ℂ) g *
              (delta ψ (K.map (MulAut.conj g).toMonoidHom) : GL (Fin m) k → ℂ) (y * g⁻¹) ≠ 0 := hy
          by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, y = u * g * κ
          · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
            have e : u * g * κ * g⁻¹ = u * (g * κ * g⁻¹) := by simp [mul_assoc]
            rw [e, delta_mul hgood hu (mem_conj.2 (by simpa [mul_assoc] using hκ)), hval u hu κ hκ] at hy'
            exact absurd (by ring) hy'
          · rw [delta_eq_zero, mul_zero, sub_zero] at hy'
            · obtain ⟨a, ha, hrest⟩ := hs y hy'
              rcases Finset.mem_insert.1 ha with rfl | ha
              · exact absurd hrest h
              · exact ⟨a, ha, hrest⟩
            · rintro ⟨u, hu, κ, hκ, e⟩
              refine h ⟨u, hu, _, mem_conj.1 hκ, ?_⟩
              rw [mul_inv_eq_iff_eq_mul.1 e]
              simp [mul_assoc]
      have h3 : d ∈ Submodule.span ℂ {y | ∃ g ∈ D, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
          y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} :=
        Submodule.subset_span ⟨g, hD g (Finset.mem_insert_self _ _), hgood, rfl⟩
      have h4 := add_mem h2 (Submodule.smul_mem _ ((x : GL (Fin m) k → ℂ) g) h3)
      rwa [sub_add_cancel] at h4

theorem mem_span_delta_of_dense {K : Subgroup (GL (Fin m) k)} (hKo : IsOpen (K : Set (GL (Fin m) k)))
    (hKc : IsCompact (K : Set (GL (Fin m) k))) {D : Set (GL (Fin m) k)} (hD : Dense D) (x : WT (m := m) ψ)
    (hx : ∀ κ ∈ K, rhoW ψ κ x = x) :
    x ∈ Submodule.span ℂ {y | ∃ g ∈ D, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
      y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} := by
  classical
  obtain ⟨-, -, C, hC, h3⟩ := x.2
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun d : D => (fun y => (d : GL (Fin m) k)⁻¹ * y) ⁻¹' K)
    (fun d => hKo.preimage (continuous_const.mul continuous_id)) fun c _ => by
      obtain ⟨d, hd, hdD⟩ := hD.inter_open_nonempty ((fun y => y⁻¹ * c) ⁻¹' K)
        (hKo.preimage (continuous_inv.mul continuous_const)) ⟨c, by simp⟩
      exact Set.mem_iUnion.2 ⟨⟨d, hdD⟩, hd⟩
  refine mem_span_delta_of_cover hKo hKc D (t.image Subtype.val) (fun g hg => ?_) x hx fun y hy => ?_
  · obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hg
    exact d.2
  · obtain ⟨u, hu, c, hc, rfl⟩ := h3 y hy
    obtain ⟨d, hd, hcd⟩ := Set.mem_iUnion₂.1 (ht hc)
    exact ⟨d, Finset.mem_image_of_mem _ hd, u, hu, _, hcd, by simp [mul_assoc]⟩

theorem mem_span_delta {K : Subgroup (GL (Fin m) k)} (hKo : IsOpen (K : Set (GL (Fin m) k)))
    (hKc : IsCompact (K : Set (GL (Fin m) k))) (x : WT (m := m) ψ) (hx : ∀ κ ∈ K, rhoW ψ κ x = x) :
    x ∈ Submodule.span ℂ {y | ∃ g, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
      y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} :=
  Submodule.span_mono (by rintro _ ⟨g, -, h⟩; exact ⟨g, h⟩) (mem_span_delta_of_dense hKo hKc dense_univ x hx)

theorem exists_countable_span : ∃ s : Set (WT (m := m) ψ), s.Countable ∧ Submodule.span ℂ s = ⊤ := by
  have : SecondCountableTopology (GL (Fin m) k) := GlobalTheory.LocGL.secondCountableTopology_GL k _
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (GL (Fin m) k)
  refine ⟨⋃ r : ℕ, (fun g => rhoW ψ g⁻¹ (delta ψ ((congruenceSubgroup k m r).map (MulAut.conj g).toMonoidHom))) '' D,
    Set.countable_iUnion fun r => hDc.image _, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨r, hr⟩ := exists_fix_congruence x
  refine Submodule.span_mono ?_ (mem_span_delta_of_dense (isOpen_congruenceSubgroup k m r)
    (isCompact_congruenceSubgroup k m r) hDd x hr)
  rintro _ ⟨g, hg, -, rfl⟩
  exact Set.mem_iUnion.2 ⟨r, g, hg, rfl⟩

theorem isTestFun_mul (x : WT (m := m) ψ) (W : GL (Fin m) k → ℂ)
    (hW : ∀ u ∈ unipB k (Fin m), ∀ g, W (u * g) = (ψ⁻¹ (superDiag u) : ℂ) * W g) (hlc : IsLocallyConstant W) :
    IsTestFun fun g => (x : GL (Fin m) k → ℂ) g * W g := by
  obtain ⟨h1, h2, C, hC, h3⟩ := x.2
  refine ⟨fun u hu g => ?_, h2.mul hlc, C, hC, fun g hg => h3 g (left_ne_zero_of_mul hg)⟩
  have hpp : (ψ (superDiag u) : ℂ) * ((ψ⁻¹ : AddChar k Circle) (superDiag u) : ℂ) = 1 := by
    rw [AddChar.inv_apply', Circle.coe_inv]
    exact mul_inv_cancel₀ (Circle.coe_ne_zero _)
  beta_reduce
  rw [h1 u hu, hW u hu]
  linear_combination ((x : GL (Fin m) k → ℂ) g * W g) * hpp

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem form_eq_zero_of_self {M : Type} [AddCommGroup M] [Module ℂ M] {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hh : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (hp : ∀ x, 0 ≤ (B x x).re) {z : M} (hz : B z z = 0)
    (x : M) : B z x = 0 := by
  by_contra ha
  have hn : 0 < Complex.normSq (B z x) := Complex.normSq_pos.2 ha
  have hxz : B x z = (starRingEnd ℂ) (B z x) := (hh z x).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B z x) = (B x x).re + 1 :=
    ⟨((B x x).re + 1) / (2 * Complex.normSq (B z x)), by field_simp⟩
  have key := hp (x + ((-(t : ℂ)) * B z x) • z)
  have e1 : B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z) =
      B x x + (-(t : ℂ)) * B z x * (starRingEnd ℂ) (B z x) +
        (starRingEnd ℂ) (-(t : ℂ) * B z x) * B z x := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz, hxz]
    ring
  have e2 : (B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z)).re =
      (B x x).re - 2 * t * Complex.normSq (B z x) := by
    rw [e1]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg,
      Complex.conj_ofReal, Complex.normSq_apply]
    ring
  linarith

theorem circle_conj_mul (z : Circle) : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

theorem conj_mul_self_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem conj_psi (c : k) : (starRingEnd ℂ) ((ψ c : Circle) : ℂ) = ((ψ⁻¹ c : Circle) : ℂ) := by
  rw [AddChar.inv_apply', Circle.coe_inv_eq_conj]

theorem superDiag_inv {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : superDiag u⁻¹ = -superDiag u := by
  have h := superDiag_mul ((unipB k (Fin m)).inv_mem hu) hu
  rw [inv_mul_cancel, superDiag_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem superDiag_conj {u n : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hn : n ∈ unipB k (Fin m)) :
    superDiag (u⁻¹ * n * u) = superDiag n := by
  have hu' := (unipB k (Fin m)).inv_mem hu
  rw [superDiag_mul ((unipB k (Fin m)).mul_mem hu' hn) hu, superDiag_mul hu' hn, superDiag_inv hu]
  ring

theorem delta_one {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : (delta ψ K : GL (Fin m) k → ℂ) 1 = 1 := by
  have := delta_mul hK (unipB k (Fin m)).one_mem K.one_mem
  rw [mul_one, superDiag_one, AddChar.map_zero_eq_one, Circle.coe_one] at this
  exact this

theorem delta_ne_zero {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : delta ψ K ≠ 0 := fun h => by
  have := delta_one hK
  rw [h] at this
  exact zero_ne_one this

theorem delta_eq_of_le {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (g : GL (Fin m) k) (hg : (delta ψ K' : GL (Fin m) k → ℂ) g ≠ 0) :
    (delta ψ K : GL (Fin m) k → ℂ) g = (delta ψ K' : GL (Fin m) k → ℂ) g := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K', g = u * κ := by
    by_contra h
    exact hg (delta_eq_zero h)
  rw [delta_mul hK hu (hle hκ), delta_mul hK' hu hκ]

theorem good_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) : Good ψ (K.map (MulAut.conj u).toMonoidHom) := by
  have e : ((K.map (MulAut.conj u).toMonoidHom : Subgroup (GL (Fin m) k)) : Set (GL (Fin m) k)) =
      (fun y => u⁻¹ * y * u) ⁻¹' K := Set.ext fun _ => mem_conj
  have hc : Continuous fun κ : GL (Fin m) k => u * κ * u⁻¹ := by fun_prop
  refine ⟨?_, ?_, fun n hn hnK => ?_⟩
  · rw [e]
    exact hK.1.preimage (by fun_prop)
  · rw [Subgroup.coe_map]
    exact hK.2.1.image hc
  · rw [← superDiag_conj hu hn]
    exact hK.2.2 _ ((unipB k (Fin m)).mul_mem ((unipB k (Fin m)).mul_mem
      ((unipB k (Fin m)).inv_mem hu) hn) hu) (mem_conj.1 hnK)

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem delta_avg {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (L₁ L₂ : WT (m := m) ψ →ₗ[ℂ] ℂ) (h₁ : ∀ κ ∈ K, ∀ x, L₁ (rhoW ψ κ x) = L₁ x)
    (h₂ : ∀ κ ∈ K, ∀ x, L₂ (rhoW ψ κ x) = L₂ x) :
    L₁ (delta ψ K') * L₂ (delta ψ K) = L₁ (delta ψ K) * L₂ (delta ψ K') := by
  have hKc : CompactSpace K := isCompact_iff_compactSpace.1 hK.2.1
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.1.preimage continuous_subtype_val
  have : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  set P : WT (m := m) ψ := ∑ q : K ⧸ K'.subgroupOf K,
    rhoW ψ ((Quotient.out q : K) : GL (Fin m) k) (delta ψ K') with hP
  have hrep : ∀ a b : K, b⁻¹ * a ∈ K'.subgroupOf K →
      rhoW ψ (a : GL (Fin m) k) (delta ψ K') = rhoW ψ (b : GL (Fin m) k) (delta ψ K') := by
    intro a b hab
    have e : (a : GL (Fin m) k) = b * ((b⁻¹ * a : K) : GL (Fin m) k) := by simp
    rw [e, map_mul, Module.End.mul_apply, rhoW_delta (Subgroup.mem_subgroupOf.1 hab)]
  have hfix : ∀ κ ∈ K, rhoW ψ κ P = P := by
    intro κ hκ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨κ, hκ⟩ : K)) _ _ fun q => ?_
    rw [MulAction.toPerm_apply, ← Module.End.mul_apply, ← map_mul]
    have e : (QuotientGroup.mk (Quotient.out ((⟨κ, hκ⟩ : K) • q)) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk ((⟨κ, hκ⟩ : K) * Quotient.out q) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    have := hrep ((⟨κ, hκ⟩ : K) * Quotient.out q) (Quotient.out ((⟨κ, hκ⟩ : K) • q)) (QuotientGroup.eq.1 e)
    simpa using this
  have hL : ∀ L : WT (m := m) ψ →ₗ[ℂ] ℂ, (∀ κ ∈ K, ∀ x, L (rhoW ψ κ x) = L x) →
      L P = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) * L (delta ψ K') := by
    intro L hL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum, Finset.sum_congr rfl fun q _ => hL _ (Quotient.out q).2 _, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hs : ∀ g, (P : GL (Fin m) k → ℂ) g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ := by
    intro g hg
    rw [hP, Submodule.coe_sum, Finset.sum_apply] at hg
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    rw [rhoW_apply] at hq
    by_contra hno
    refine hq (delta_eq_zero ?_)
    rintro ⟨u, hu, κ', hκ', he⟩
    exact hno ⟨u, hu, κ' * ((Quotient.out q : K) : GL (Fin m) k)⁻¹,
      K.mul_mem (hle hκ') (K.inv_mem (Quotient.out q).2), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩
  obtain ⟨s, hPs⟩ : ∃ s : ℂ, P = s • delta ψ K := ⟨_, eq_smul_delta hK P hfix hs⟩
  have a1 := hL L₁ h₁
  have a2 := hL L₂ h₂
  rw [hPs, map_smul, smul_eq_mul] at a1 a2
  have c0 : (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ c0
  linear_combination (-L₂ (delta ψ K)) * a1 + L₁ (delta ψ K) * a2

def pairI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) : ℂ :=
  I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g


variable (ψ) in
def formI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pairI I)
    (fun x x' y => by
      simp only [pairI]
      rw [← map_add (f := _)]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]; ring)
    (fun x y y' => by
      simp only [pairI]
      rw [← map_add (f := _)]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem formI_apply (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) :
    formI ψ I x y = I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := rfl

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

def PosInt (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  IsInvIntegral I ∧ (∀ f, IsTestFun f → I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f)) ∧
    ∀ f, IsTestFun f → (∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0)

theorem isTestFun_pair (x y : WT (m := m) ψ) :
    IsTestFun fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := by
  have h := isTestFun_mul y (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g))
    (fun u hu g => by
      show (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) (u * g)) =
        ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g)
      rw [WT.left x hu, map_mul, conj_psi]) (x.2.2.1.comp _)
  have e : (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g) =
      fun g => (y : GL (Fin m) k → ℂ) g * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) :=
    funext fun g => mul_comm _ _
  rw [e]
  exact h

theorem isInvForm_formI {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) :
    IsInvForm (rhoW ψ) (formI ψ I) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩
  · rw [formI_apply, formI_apply, ← hI.2.1 _ (isTestFun_pair x y)]
    congr 1
    funext g
    simp [map_mul, mul_comm]
  · exact (hI.2.2 _ (isTestFun_pair x x) fun g => by rw [conj_mul_self_re]; exact Complex.normSq_nonneg _).1
  · rw [formI_apply, formI_apply]
    simp only [rhoW_apply]
    exact hI.1 _ (isTestFun_pair x y) g

theorem formI_self_ne_zero {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) {x : WT (m := m) ψ} (hx : x ≠ 0) :
    formI ψ I x x ≠ 0 := by
  intro h0
  apply hx
  have hn : ∀ g, 0 ≤ ((starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (x : GL (Fin m) k → ℂ) g).re := fun g => by
    rw [conj_mul_self_re]; exact Complex.normSq_nonneg _
  have h := (hI.2.2 _ (isTestFun_pair x x) hn).2 (by rw [← formI_apply, h0, Complex.zero_re])
  refine Subtype.ext (funext fun g => ?_)
  have := h g
  rw [conj_mul_self_re] at this
  exact Complex.normSq_eq_zero.1 this


variable (ψ) in
def cK (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (K : Subgroup (GL (Fin m) k)) : ℂ :=
  formI ψ I (delta ψ K) (delta ψ K)

theorem cK_ne_zero {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) {K : Subgroup (GL (Fin m) k)}
    (hK : Good ψ K) : cK ψ I K ≠ 0 :=
  formI_self_ne_zero hI (delta_ne_zero hK)

theorem formI_delta_le (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K)
    (hK' : Good ψ K') (hle : K' ≤ K) : formI ψ I (delta ψ K) (delta ψ K') = cK ψ I K' := by
  rw [cK, formI_apply, formI_apply]
  congr 1
  funext g
  by_cases h : (delta ψ K' : GL (Fin m) k → ℂ) g = 0
  · simp [h]
  · rw [delta_eq_of_le hK hK' hle g h]

theorem rhoW_inv_delta_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) :
    rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) =
      ((ψ⁻¹ (superDiag u) : Circle) : ℂ) • delta ψ K := by
  have hK' := good_conj hK hu
  have hfix : ∀ κ ∈ K, rhoW ψ κ (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom))) =
      rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) := by
    intro κ hκ
    rw [← Module.End.mul_apply, ← map_mul]
    have e1 : κ * u⁻¹ = u⁻¹ * (u * κ * u⁻¹) := by group
    have e2 : u⁻¹ * (u * κ * u⁻¹) * u = κ := by group
    rw [e1, map_mul, Module.End.mul_apply, rhoW_delta (mem_conj.2 (by rw [e2]; exact hκ))]
  have hs : ∀ g, (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) : GL (Fin m) k → ℂ) g ≠ 0 →
      ∃ n ∈ unipB k (Fin m), ∃ κ ∈ K, g = n * κ := by
    intro g hg
    rw [rhoW_apply] at hg
    obtain ⟨n, hn, κ', hκ', he⟩ : ∃ n ∈ unipB k (Fin m), ∃ κ' ∈ K.map (MulAut.conj u).toMonoidHom,
        g * u⁻¹ = n * κ' := by
      by_contra h
      exact hg (delta_eq_zero h)
    refine ⟨n * u, (unipB k (Fin m)).mul_mem hn hu, u⁻¹ * κ' * u, mem_conj.1 hκ', ?_⟩
    calc g = g * u⁻¹ * u := by group
      _ = n * κ' * u := by rw [he]
      _ = n * u * (u⁻¹ * κ' * u) := by group
  rw [eq_smul_delta hK _ hfix hs, rhoW_apply, one_mul]
  congr 1
  have := delta_mul hK' ((unipB k (Fin m)).inv_mem hu) (K.map (MulAut.conj u).toMonoidHom).one_mem
  rw [mul_one] at this
  rw [this, superDiag_inv hu, AddChar.inv_apply]

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem exists_good_fix (hψ : Continuous ψ) (y z : WT (m := m) ψ) : ∃ K : Subgroup (GL (Fin m) k), Good ψ K ∧
    ∀ κ ∈ K, rhoW ψ κ y = y ∧ rhoW ψ κ z = z := by
  obtain ⟨K₁, h1o, -, h1⟩ := exists_fix y
  obtain ⟨K₂, h2o, -, h2⟩ := exists_fix z
  obtain ⟨K, hK, hsub⟩ := exists_good hψ (Filter.inter_mem (h1o.mem_nhds K₁.one_mem) (h2o.mem_nhds K₂.one_mem))
  exact ⟨K, hK, fun κ hκ => ⟨h1 κ (hsub hκ).1, h2 κ (hsub hκ).2⟩⟩


variable (ψ) in
def lamK (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ)
    (K : Subgroup (GL (Fin m) k)) (y : WT (m := m) ψ) : ℂ :=
  B y (delta ψ K) / cK ψ I K

theorem lamK_mono {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B)
    {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K) {y : WT (m := m) ψ}
    (hy : ∀ κ ∈ K, rhoW ψ κ y = y) : lamK ψ I B K' y = lamK ψ I B K y := by
  have h1 : ∀ κ ∈ K, ∀ x, B y (rhoW ψ κ x) = B y x := fun κ hκ x => by
    calc B y (rhoW ψ κ x) = B (rhoW ψ κ y) (rhoW ψ κ x) := by rw [hy κ hκ]
      _ = B y x := hB.2.2 κ y x
  have h2 : ∀ κ ∈ K, ∀ x, formI ψ I (delta ψ K) (rhoW ψ κ x) = formI ψ I (delta ψ K) x := fun κ hκ x => by
    calc formI ψ I (delta ψ K) (rhoW ψ κ x) = formI ψ I (rhoW ψ κ (delta ψ K)) (rhoW ψ κ x) := by
          rw [rhoW_delta hκ]
      _ = _ := (isInvForm_formI hI).2.2 κ _ x
  have h := delta_avg hK hK' hle (B y) (formI ψ I (delta ψ K)) h1 h2
  rw [formI_delta_le I hK hK' hle] at h
  rw [lamK, lamK, div_eq_div_iff (cK_ne_zero hI hK') (cK_ne_zero hI hK)]
  exact h

theorem lamK_eq (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B)
    {K₁ K₂ : Subgroup (GL (Fin m) k)} (h1 : Good ψ K₁) (h2 : Good ψ K₂) {y : WT (m := m) ψ}
    (hy1 : ∀ κ ∈ K₁, rhoW ψ κ y = y) (hy2 : ∀ κ ∈ K₂, rhoW ψ κ y = y) :
    lamK ψ I B K₁ y = lamK ψ I B K₂ y := by
  obtain ⟨K, hK, hsub⟩ := exists_good hψ (Filter.inter_mem (h1.1.mem_nhds K₁.one_mem) (h2.1.mem_nhds K₂.one_mem))
  rw [← lamK_mono hI hB h1 hK (fun x hx => (hsub hx).1) hy1, lamK_mono hI hB h2 hK (fun x hx => (hsub hx).2) hy2]


variable (ψ) in
def lam (hψ : Continuous ψ) (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ)
    (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ) (y : WT (m := m) ψ) : ℂ :=
  lamK ψ I B (Classical.choose (exists_good_fix hψ y y)) y

theorem lam_eq (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B)
    {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {y : WT (m := m) ψ} (hy : ∀ κ ∈ K, rhoW ψ κ y = y) :
    lam ψ hψ I B y = lamK ψ I B K y := by
  have h := Classical.choose_spec (exists_good_fix hψ y y)
  exact lamK_eq hψ hI hB h.1 hK (fun κ hκ => (h.2 κ hκ).1) hy

theorem lam_add (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B) (y z : WT (m := m) ψ) :
    lam ψ hψ I B (y + z) = lam ψ hψ I B y + lam ψ hψ I B z := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ y z
  rw [lam_eq hψ hI hB hK (fun κ hκ => by rw [map_add (f := _), (hKf κ hκ).1, (hKf κ hκ).2]),
    lam_eq hψ hI hB hK (fun κ hκ => (hKf κ hκ).1), lam_eq hψ hI hB hK (fun κ hκ => (hKf κ hκ).2)]
  simp only [lamK, map_add (f := _), LinearMap.add_apply, add_div]

theorem lam_smul (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B) (a : ℂ) (y : WT (m := m) ψ) :
    lam ψ hψ I B (a • y) = (starRingEnd ℂ) a * lam ψ hψ I B y := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ y y
  rw [lam_eq hψ hI hB hK (fun κ hκ => by rw [map_smul, (hKf κ hκ).1]),
    lam_eq hψ hI hB hK (fun κ hκ => (hKf κ hκ).1)]
  simp only [lamK, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ}

include hψ in
theorem lam_unip (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y : WT (m := m) ψ) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) :
    lam ψ hψ I B (rhoW ψ u y) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * lam ψ hψ I B y := by
  obtain ⟨K, hK, hKy⟩ := exists_good_fix hψ y y
  have hK' := good_conj hK hu
  have hfix' : ∀ κ ∈ K.map (MulAut.conj u).toMonoidHom, rhoW ψ κ (rhoW ψ u y) = rhoW ψ u y := by
    intro κ hκ
    have e : κ * u = u * (u⁻¹ * κ * u) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hKy _ (mem_conj.1 hκ)).1]
  rw [lam_eq hψ hI hB hK' hfix', lam_eq hψ hI hB hK (fun κ hκ => (hKy κ hκ).1)]
  have hB' : B (rhoW ψ u y) (delta ψ (K.map (MulAut.conj u).toMonoidHom)) =
      ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * B y (delta ψ K) := by
    rw [← hB.2.2 u⁻¹ (rhoW ψ u y), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, rhoW_inv_delta_conj hK hu, map_smul, smul_eq_mul]
  have hc' : cK ψ I (K.map (MulAut.conj u).toMonoidHom) = cK ψ I K := by
    rw [cK, cK, ← (isInvForm_formI hI).2.2 u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)),
      rhoW_inv_delta_conj hK hu]
    simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    linear_combination (formI ψ I (delta ψ K) (delta ψ K)) * circle_conj_mul (ψ⁻¹ (superDiag u))
  rw [lamK, lamK, hB', hc', mul_div_assoc]

include hψ in
theorem lam_eq_zero (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {z : WT (m := m) ψ} (hz : B z z = 0)
    (g : GL (Fin m) k) : lam ψ hψ I B (rhoW ψ g z) = 0 := by
  obtain ⟨K, hK, hKy⟩ := exists_good_fix hψ (rhoW ψ g z) (rhoW ψ g z)
  rw [lam_eq hψ hI hB hK (fun κ hκ => (hKy κ hκ).1), lamK,
    form_eq_zero_of_self hB.1 hB.2.1 (by rw [hB.2.2]; exact hz), zero_div]


variable (ψ) in
def Wf (hψ : Continuous ψ) (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ)
    (y : WT (m := m) ψ) (g : GL (Fin m) k) : ℂ :=
  lam ψ hψ I B (rhoW ψ g y)

theorem Wf_apply (y : WT (m := m) ψ) (g : GL (Fin m) k) : Wf ψ hψ I B y g = lam ψ hψ I B (rhoW ψ g y) := rfl

theorem Wf_right (y : WT (m := m) ψ) (g x : GL (Fin m) k) : Wf ψ hψ I B y (g * x) = Wf ψ hψ I B (rhoW ψ x y) g := by
  simp only [Wf, map_mul, Module.End.mul_apply]

theorem Wf_left (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y : WT (m := m) ψ) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (g : GL (Fin m) k) :
    Wf ψ hψ I B y (u * g) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * Wf ψ hψ I B y g := by
  simp only [Wf]
  rw [map_mul, Module.End.mul_apply, lam_unip hψ hI hB _ hu]

theorem Wf_add (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y z : WT (m := m) ψ) :
    Wf ψ hψ I B (y + z) = Wf ψ hψ I B y + Wf ψ hψ I B z := by
  funext g
  simp only [Wf, map_add (f := _), Pi.add_apply]
  exact lam_add hψ hI hB _ _

theorem Wf_smul (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (a : ℂ) (y : WT (m := m) ψ) :
    Wf ψ hψ I B (a • y) = (starRingEnd ℂ) a • Wf ψ hψ I B y := by
  funext g
  simp only [Wf, map_smul, Pi.smul_apply, smul_eq_mul]
  exact lam_smul hψ hI hB _ _

theorem Wf_eq_zero (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {z : WT (m := m) ψ} (hz : B z z = 0) :
    Wf ψ hψ I B z = 0 :=
  funext fun g => lam_eq_zero hψ hI hB hz g

theorem isLocallyConstant_Wf (y : WT (m := m) ψ) : IsLocallyConstant (Wf ψ hψ I B y) := by
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨(fun x => g⁻¹ * x) ⁻¹' K, hKo.preimage (by fun_prop), by simp [K.one_mem], fun x hx => ?_⟩
  have e : x = g * (g⁻¹ * x) := by group
  rw [e, Wf_right, hK _ hx]

end DiscreteGroups.sglob.LConv

end

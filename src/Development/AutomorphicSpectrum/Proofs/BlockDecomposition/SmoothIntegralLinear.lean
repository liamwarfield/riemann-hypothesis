module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntEl

open MeasureTheory

theorem finite_range {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem measure_level_ne_top {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [AddCommGroup W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ : X → W} (hc : HasCompactSupport φ) {v : W}
    (hv : v ≠ 0) : μ (φ ⁻¹' {v}) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (IsCompact.measure_lt_top hc))
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support, show φ x = v from hx]
  exact hv

theorem smInt_comp {X Y W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X)
    (ψ : X → Y) (g : Y → W) (S : Finset Y) (hS : ∀ x, ψ x ∈ S)
    (hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y})) (hf : ∀ y ∈ S, g y ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤) :
    smInt μ (g ∘ ψ) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • g y := by
  classical
  have hsupp : (Function.support fun v : W => (((μ ((g ∘ ψ) ⁻¹' {v})).toReal : ℝ) : ℂ) • v)
      ⊆ ↑(S.image g) := by
    intro v hv
    by_contra hvS
    apply hv
    have : (g ∘ ψ) ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hvS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ψ x, hS x, hx⟩))
    simp [this]
  unfold smInt
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
      (fun y hy => Finset.mem_image_of_mem g hy)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv0 : v = 0
  · subst hv0
    rw [smul_zero]
    symm
    exact Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.1 hy).2, smul_zero]
  · have hset : (g ∘ ψ) ⁻¹' {v} = ⋃ y ∈ S.filter (fun y => g y = v), ψ ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp, Set.mem_iUnion,
        Finset.mem_filter, exists_prop]
      constructor
      · intro hx
        exact ⟨ψ x, ⟨hS x, hx⟩, rfl⟩
      · rintro ⟨y, ⟨_, hy⟩, rfl⟩
        exact hy
    have hmeas : μ ((g ∘ ψ) ⁻¹' {v}) = ∑ y ∈ S.filter (fun y => g y = v), μ (ψ ⁻¹' {y}) := by
      rw [hset]
      refine measure_biUnion_finset ?_ fun y hy => hm y (Finset.mem_filter.1 hy).1
      intro a _ b _ hab
      exact Disjoint.preimage ψ (Set.disjoint_singleton.2 hab)
    rw [hmeas, ENNReal.toReal_sum (fun y hy => hf y (Finset.mem_filter.1 hy).1
      (by rw [(Finset.mem_filter.1 hy).2]; exact hv0)), Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2]

theorem smInt_add {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ₁ φ₂ : X → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂ := by
  classical
  let ψ : X → W × W := fun x => (φ₁ x, φ₂ x)
  let S : Finset (W × W) := (finite_range l₁ c₁).toFinset ×ˢ (finite_range l₂ c₂).toFinset
  have hS : ∀ x, ψ x ∈ S := fun x =>
    Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩,
      (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩
  have hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y}) := fun y _ =>
    ((l₁.prodMk l₂).isOpen_fiber y).measurableSet
  have f₁ : ∀ y : W × W, y.1 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₁ hy) (measure_mono fun x hx => by
      show φ₁ x = y.1
      rw [← show ψ x = y from hx])
  have f₂ : ∀ y : W × W, y.2 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₂ hy) (measure_mono fun x hx => by
      show φ₂ x = y.2
      rw [← show ψ x = y from hx])
  have e₀ : smInt μ (φ₁ + φ₂) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • (y.1 + y.2) :=
    smInt_comp μ ψ (fun y => y.1 + y.2) S hS hm fun y _ hy => by
      by_cases h : y.1 = 0
      · refine f₂ y fun h' => hy ?_
        show y.1 + y.2 = 0
        rw [h, h', add_zero]
      · exact f₁ y h
  have e₁ : smInt μ φ₁ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.1 :=
    smInt_comp μ ψ (fun y => y.1) S hS hm fun y _ hy => f₁ y hy
  have e₂ : smInt μ φ₂ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.2 :=
    smInt_comp μ ψ (fun y => y.2) S hS hm fun y _ hy => f₂ y hy
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => smul_add _ _ _

theorem smInt_linear {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (T : W →ₗ[ℂ] W') {φ : X → W}
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    smInt μ (T ∘ φ) = T (smInt μ φ) := by
  classical
  let S : Finset W := (finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have hm : ∀ y ∈ S, MeasurableSet (φ ⁻¹' {y}) := fun y _ => (l.isOpen_fiber y).measurableSet
  have e₀ : smInt μ (T ∘ φ) = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • T y :=
    smInt_comp μ φ T S hS hm fun y _ hy =>
      measure_level_ne_top μ c fun h => hy (by rw [h, map_zero])
  have e₁ : smInt μ φ = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • y :=
    smInt_comp μ φ id S hS hm fun y _ hy => measure_level_ne_top μ c hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e₀, e₁, map_sum]
  exact Finset.sum_congr rfl fun y _ => (map_smul T _ y).symm

theorem smInt_comp_measurePreserving {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X) {c : X → X} {φ : X → W}
    (hc : MeasurePreserving c μ μ) (l : IsLocallyConstant φ) :
    smInt μ (φ ∘ c) = smInt μ φ := by
  unfold smInt
  refine finsum_congr fun v => ?_
  have h : μ (c ⁻¹' (φ ⁻¹' {v})) = μ (φ ⁻¹' {v}) :=
    hc.measure_preimage (l.isOpen_fiber v).measurableSet.nullMeasurableSet
  rw [Set.preimage_comp, h]

theorem smInt_indicator {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W]
    (μ : Measure X) (A : Set X) (v : W) :
    smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  classical
  unfold smInt
  by_cases hv : v = 0
  · subst hv
    rw [smul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have : (A.indicator fun _ => (0 : W)) ⁻¹' {w} = ∅ := by
        ext x
        simp [Set.indicator_zero', Ne.symm hw]
      rw [this, measure_empty]
      simp
  · rw [finsum_eq_single _ v]
    · have : (A.indicator fun _ => v) ⁻¹' {v} = A := by
        ext x
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx, Ne.symm hv]
      rw [this]
    · intro w hw
      by_cases hw0 : w = 0
      · rw [hw0, smul_zero]
      · have : (A.indicator fun _ => v) ⁻¹' {w} = ∅ := by
          ext x
          by_cases hx : x ∈ A
          · simp [hx, Ne.symm hw]
          · simp [hx, Ne.symm hw0]
        simp [this]

theorem smInt_properties : ∀ {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts μ], (∀ φ₁ φ₂ : X → W, IsLocallyConstant φ₁ → HasCompactSupport φ₁ → IsLocallyConstant φ₂ → HasCompactSupport φ₂ → smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂) ∧ (∀ (T : W →ₗ[ℂ] W') (φ : X → W), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (T ∘ φ) = T (smInt μ φ)) ∧ (∀ (c : X → X) (φ : X → W), MeasureTheory.MeasurePreserving c μ μ → IsLocallyConstant φ → smInt μ (φ ∘ c) = smInt μ φ) ∧ ∀ (A : Set X) (v : W), IsCompact A → IsOpen A → IsClosed A → smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  intro X W W' _ _ _ _ _ _ _ μ _
  exact ⟨fun φ₁ φ₂ l₁ c₁ l₂ c₂ => smInt_add μ l₁ c₁ l₂ c₂,
    fun T φ l c => smInt_linear μ T l c,
    fun c φ hc l => smInt_comp_measurePreserving μ hc l,
    fun A v _ _ _ => smInt_indicator μ A v⟩

end GlobalTheory.CompanionTheory.Rodier.SmIntEl

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExists
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ScalarEx

theorem exists_scalarBy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  intro k _ _ _ _ x t
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  exact ⟨(ω t : ℂ), fun v => hω t v⟩

end GlobalTheory.CompanionTheory.ScalarEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  first | exact @GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | exact GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | (intros; apply GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptionsStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptions
namespace GlobalTheory.CompanionTheory.Segments

theorem shufcomb (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l)
    (hi : w i = 0) (hj : w j = l - 1)
    (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a)
    (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a) : StrictAnti w := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    omega
  intro a b hab
  by_cases hbi : b = i
  · by_cases haj : a = j
    · rw [hbi, haj, hi, hj]
      omega
    · exact h2 a b hab haj (by rw [hbi]; exact hij)
  · by_cases hai : a = i
    · by_cases hbj : b = j
      · exfalso
        have hij' : i < j := by
          rw [← hai, ← hbj]
          exact hab
        obtain ⟨c, hci, hcj⟩ : ∃ c : Fin l, c ≠ i ∧ c ≠ j := by
          by_contra hc
          push_neg at hc
          have key : ∀ k : ℕ, ∀ hk : k < l, k = i.val ∨ k = j.val := by
            intro k hk
            by_cases h : (⟨k, hk⟩ : Fin l) = i
            · left
              exact congrArg Fin.val h
            · right
              exact congrArg Fin.val (hc ⟨k, hk⟩ h)
          have k0 := key 0 (by omega)
          have k1 := key 1 (by omega)
          have k2 := key 2 (by omega)
          omega
        rcases lt_or_gt_of_ne hci with hc | hc
        · have h3 := h1 c j (lt_trans hc hij') hci (Ne.symm hij)
          have h4 := hw c
          omega
        · have h3 := h2 i c hc hij hcj
          omega
      · exact h2 a b hab (by rw [hai]; exact hij) hbj
    · exact h1 a b hab hai hbi

end GlobalTheory.CompanionTheory.Segments
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_anti_of_two_exceptions : ∀ (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l) (hi : w i = 0) (hj : w j = l - 1) (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a) (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a), StrictAnti w := by
  first | exact @GlobalTheory.CompanionTheory.Segments.shufcomb | exact GlobalTheory.CompanionTheory.Segments.shufcomb | (intros; apply GlobalTheory.CompanionTheory.Segments.shufcomb <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

theorem isTopCut_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len) :
    IsTopCut Δ (topCut Δ c hc) :=
  ⟨h, fun _ => rfl⟩

theorem eq_topCut {Δ : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut Δ Γ) :
    Γ = topCut Δ (fun a => (Γ a).len) (fun a => (Γ a).len_pos) :=
  funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl

theorem sum_split {s : ℕ} (c : Fin s → ℕ) (a : Fin s) :
    ∑ b, c b = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + c a + ∑ b ∈ Finset.univ.filter (fun b => a < b), c b := by
  have h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b := by
    refine Finset.sum_bij (fun t _ => Fin.castLE a.2.le t)
      (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩)
      (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)
    have hb' : (b : ℕ) < a := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
  rw [h1]
  have h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]

theorem concat_dec_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len)
    (i : Fin (∑ a, c a)) : concat c (fun a => dec (topCut Δ c hc a)) i = dec Δ (Fin.cast h i) := by
  show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)
  rcases hq : finSigmaFinEquiv.symm i with ⟨a, j⟩
  have hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j := by
    rw [← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]
  have hs := sum_split c a
  have hj : (j : ℕ) < c a := j.2
  simp only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]
  congr 1
  simp only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]
  have key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1)) := by
    rw [← h]; omega
  rw [key]
  push_cast
  congr 1

theorem concat_injective {s : ℕ} {c : Fin s → ℕ} {x x' : ∀ a, Fin (c a) → IrrGL (k := k)} (h : concat c x = concat c x') :
    x = x' := by
  funext a j
  have := congrFun h (finSigmaFinEquiv ⟨a, j⟩)
  change (fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) =
    (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem concat_apply_equiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (p : (a : Fin s) × Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  change (fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem sum_concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ j, (x a j).1 := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  simp only [concat_apply_equiv]

theorem sum_dec (Δ : Segment k) : ∑ a, (dec Δ a).1 = Δ.deg := by
  rw [← Segment.sum_term_fst]
  exact Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)

theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

theorem jm_reindex {n m N : ℕ} (h : n = m) (x : Fin n → IrrGL (k := k)) (x' : Fin m → IrrGL (k := k))
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  rfl

theorem eq_of_isLSeg {Γ : Segment k} {x x' : IrrGL (k := k)} (h : IsLSeg Γ x.rep) (h' : IsLSeg Γ x'.rep) : x = x' := by
  obtain ⟨n, c⟩ := x
  obtain ⟨n', c'⟩ := x'
  have e1 := h.deg_eq
  have e2 := h'.deg_eq
  obtain rfl : n = n' := e1.symm.trans e2
  obtain ⟨φ⟩ := h.unique h'
  have := (IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩)
    (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩
  rw [IrrGL.of_rep, IrrGL.of_rep] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SegCoarse

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem conj_perm_entry {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (p q : Fin N) :
    ((GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) (w p) (w q) = (g : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv]
  change ((w⁻¹).permMatrix k * (g : Matrix (Fin N) (Fin N) k) * (w⁻¹⁻¹).permMatrix k) (w p) (w q) = _
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd p) < blk (stdBlocks d hd) (wOpen d hd q)) : q < p := by
  by_contra hqp
  have hm := Tuple.monotone_sort (wKey d hd) (not_lt.mp hqp)
  change wKey d hd (wOpen d hd p) ≤ wKey d hd (wOpen d hd q) at hm
  unfold wKey at hm
  rw [Prod.Lex.le_iff] at hm
  simp only [ofLex_toLex] at hm
  rcases hm with hlt | ⟨heq, _⟩
  · exact lt_asymm hb (OrderDual.toDual_lt_toDual.mp hlt)
  · rw [OrderDual.toDual_inj] at heq
    rw [heq] at hb
    exact lt_irrefl _ hb

variable (k : Type) [Field k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem mem_unipU {u : GL (Fin N) k} : u ∈ unipU k d hd ↔
    u ∈ unipB k (Fin N) ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  exact Iff.rfl

theorem conj_mem_parabLower {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹ ∈ parabLower k (stdBlocks d hd) := by
  rw [GlobalTheory.SmGL.mem_parabLower_iff k]
  intro a b i j hab
  obtain ⟨p, hp⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨a, i⟩)
  obtain ⟨q, hq⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨b, j⟩)
  rw [← hp, ← hq]
  unfold pm
  rw [conj_perm_entry]
  apply ((GlobalTheory.SmGL.mem_unipB k).mp hn).1
  apply lt_of_blk_lt d hd
  rw [hp, hq, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  exact hab

theorem exists_mul {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u := by
  have hc0 := conj_mem_parabLower k d hd hn
  set P := pm k (wOpen d hd) with hP
  set e := stdBlocks d hd with he
  have hc : P * n * P⁻¹ ∈ parab k (opp e) := hc0
  obtain ⟨v, hv, hcv⟩ := exists_levi_mul_unip k (opp e) ⟨P * n * P⁻¹, hc⟩
  set L := leviEmb k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) with hL
  have hcv' : P * n * P⁻¹ = L * v := hcv
  have hLentry : ∀ p q : Fin N, ((P⁻¹ * L * P : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p q =
      if blk e (wOpen d hd p) = blk e (wOpen d hd q) then (n : Matrix (Fin N) (Fin N) k) p q else 0 := by
    intro p q
    have h1 := conj_perm_entry (wOpen d hd) (P⁻¹ * L * P) p q
    simp only [show GroundTheory.Automorphic.permGL k (wOpen d hd) = P from rfl] at h1
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group] at h1
    rw [← h1]
    obtain ⟨⟨x, i⟩, hxi⟩ := e.surjective (wOpen d hd p)
    obtain ⟨⟨y, j⟩, hyj⟩ := e.surjective (wOpen d hd q)
    rw [← hxi, ← hyj, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
    split_ifs with hxy
    · subst hxy
      refine (GlobalTheory.SmGL.leviEmb_apply_same k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) x i j).trans ?_
      refine (GlobalTheory.SmGL.leviProj_apply k (opp e) ⟨P * n * P⁻¹, hc⟩ x i j).trans ?_
      change ((P * n * P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨x, i⟩) (e ⟨x, j⟩) = _
      rw [hxi, hyj]
      exact conj_perm_entry (wOpen d hd) n p q
    · exact GlobalTheory.SmGL.leviEmb_apply_ne k (opp e) _ hxy i j
  have haB : P⁻¹ * L * P ∈ unipB k (Fin N) := by
    rw [GlobalTheory.SmGL.mem_unipB k]
    refine ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hLentry]
      split_ifs
      · exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).1 p q hqp
      · rfl
    · rw [hLentry, ite_eq_left rfl]
      exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).2 p
  refine ⟨P⁻¹ * L * P, ?_, P⁻¹ * v * P, ?_, ?_⟩
  · change P⁻¹ * L * P ∈ unipB k (Fin N) ∧
      P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    refine ⟨haB, ?_⟩
    show P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group]
    exact ⟨leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩, rfl⟩
  · rw [mem_unipU k d hd]
    refine ⟨?_, ?_⟩
    · have hv' : v = L⁻¹ * (P * n * P⁻¹) := by
        rw [hcv']
        group
      rw [show P⁻¹ * v * P = (P⁻¹ * L * P)⁻¹ * n by rw [hv']; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haB) hn
    · show P * (P⁻¹ * v * P) * P⁻¹ ∈ unipRadLower k e
      rw [show P * (P⁻¹ * v * P) * P⁻¹ = v by group]
      exact hv
  · rw [show P⁻¹ * L * P * (P⁻¹ * v * P) = P⁻¹ * (L * v) * P by group, ← hcv']
    group

theorem conj_mem_unipU {n u : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) (hu : u ∈ unipU k d hd) :
    n * u * n⁻¹ ∈ unipU k d hd := by
  rw [mem_unipU k d hd] at hu ⊢
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hu.1) (Subgroup.inv_mem _ hn), ?_⟩
  have hN := GlobalTheory.SmGL.parab_le_normalizer k (GlobalTheory.SmGL.opp (stdBlocks d hd)) (conj_mem_parabLower k d hd hn)
  have key : pm k (wOpen d hd) * (n * u * n⁻¹) * (pm k (wOpen d hd))⁻¹ =
      (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) *
        (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹)⁻¹ := by group
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hu.2

end GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun n hn => GlobalTheory.CompanionTheory.Rodier.OpenFactor.exists_mul k d hd hn,
    fun n hn u hu => GlobalTheory.CompanionTheory.Rodier.OpenFactor.conj_mem_unipU k d hd hn hu⟩

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_decomposition_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad | exact GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad | (intros; apply GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapStable

theorem qdet_mem {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (h : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

def blockM {R : Type} [CommRing R] {r s : ℕ} (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    Matrix (Fin (r + s)) (Fin (r + s)) R :=
  Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (fromBlocks A 0 0 B)

theorem val_lev {R : Type} [CommRing R] {r s : ℕ} (g : GL (Fin r) R × GL (Fin s) R) :
    (lev R r s g).val = blockM g.1.val g.2.val :=
  GlobalTheory.SmGL.val_emb₂ R _ g

theorem blockM_map {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    (blockM A B).map p = blockM (A.map p) (B.map p) := by
  ext i j
  simp only [blockM, Matrix.map_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (g : GL (Fin r) R × GL (Fin s) R) :
    Matrix.GeneralLinearGroup.map p (lev R r s g) =
      lev S r s (Matrix.GeneralLinearGroup.map p g.1, Matrix.GeneralLinearGroup.map p g.2) := by
  apply Units.ext
  change (lev R r s g).val.map p = (lev S r s _).val
  rw [val_lev, val_lev, blockM_map]
  rfl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem infGL_lev (y : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
    infGL E (r + s) (lev (Cinf E) r s y) = lev (Ad E) r s (infGL E r y.1, infGL E s y.2) := by
  refine ga_ext ?_ ?_
  · rw [map_lev]; simp
  · rw [map_lev]; simp only [pFin_infGL, pFin_infGL]; exact (map_one _).symm

theorem blockM_add {R : Type} [CommRing R] {r s : ℕ} (A A' : Matrix (Fin r) (Fin r) R)
    (B B' : Matrix (Fin s) (Fin s) R) : blockM A B + blockM A' B' = blockM (A + A') (B + B') := by
  ext i j
  simp only [blockM, Matrix.add_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem blockM_smul {R : Type} [CommRing R] {r s : ℕ} (t : ℝ) [Module ℝ R] (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin s) (Fin s) R) : t • blockM A B = blockM (t • A) (t • B) := by
  ext i j
  simp only [blockM, Matrix.smul_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem one_add_smul_blockM (t : ℝ) (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    1 + t • blockM X₁ X₂ = blockM (1 + t • X₁) (1 + t • X₂) := by
  have h1 : (1 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) = blockM 1 1 := by
    simp [blockM, fromBlocks_one]
  rw [h1, blockM_smul, blockM_add]

theorem lieD_block {F : Sm E (r + s)} (hF : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0)
    (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) (m : GA E r × GA E s) :
    lieD (toL (blockM X₁ X₂)) F.1 (lev (Ad E) r s m) = 0 := by
  set g := lev (Ad E) r s m with hg
  set X : Lie E (r + s) := toL (blockM X₁ X₂) with hX
  let c : ℝ → Lie E (r + s) := fun t => oneL E (r + s) + t • X
  have hc : HasDerivAt c X 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul ℝ X)
  have h0 : c 0 = oneL E (r + s) := by simp [c]
  have hd : HasFDerivAt (chart F.1 g) (fderiv ℝ (chart F.1 g) (oneL E (r + s))) (c 0) := by
    rw [h0]; exact (differentiableAt_chart F.2 g).hasFDerivAt
  have h2 := hd.comp_hasDerivAt (0 : ℝ) hc
  have ev : ∀ (n : ℕ) (Y : Lie E n), ∀ᶠ t : ℝ in 𝓝 0, oneL E n + t • Y ∈ invSet E n := by
    intro n Y
    have hcont : Continuous fun t : ℝ => oneL E n + t • Y := by fun_prop
    refine hcont.continuousAt.eventually_mem (isOpen_invSet.mem_nhds ?_)
    simp only [zero_smul, add_zero]
    change IsUnit (Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) (Cinf E))))
    rw [Equiv.apply_symm_apply]
    exact isUnit_one
  have hz : (chart F.1 g ∘ c) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ev r (toL X₁), ev s (toL X₂)] with t h1 h2
    obtain ⟨u₁, hu₁⟩ := h1
    obtain ⟨u₂, hu₂⟩ := h2
    have e : c t = toL (lev (Cinf E) r s (u₁, u₂)).val := by
      rw [val_lev]
      change c t = toL (blockM u₁.val u₂.val)
      rw [hu₁, hu₂]
      exact one_add_smul_blockM t X₁ X₂
    rw [Function.comp_apply, e, chart_val, infGL_lev, hg, ← map_mul]
    exact hF _
  exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)


variable (E r s) in
def vanAlg : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) where
  carrier := {z | ∀ F : Sm E (r + s), (∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
    ∀ m : GA E r × GA E s, (z F).1 (lev (Ad E) r s m) = 0}
  mul_mem' hx hy F hF := hx _ (hy F hF)
  add_mem' {x y} hx hy F hF m := by
    change (x F).1 _ + (y F).1 _ = 0
    rw [hx F hF m, hy F hF m, add_zero]
  algebraMap_mem' c F hF m := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hF m, smul_zero]

theorem Eop_mem_of {a : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (τ : E →+* ℂ) (p q : Fin a)
    (h : ∀ x, lieS E a p q x ∈ S) : Eop τ p q ∈ S :=
  S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _

theorem lie_block_mem (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    lie E (r + s) (toL (blockM X₁ X₂)) ∈ vanAlg E r s :=
  fun _ hF m => lieD_block hF X₁ X₂ m

theorem single_castAdd (i j : Fin r) (x : Cinf E) :
    Matrix.single (Fin.castAdd s i) (Fin.castAdd s j) x = blockM (Matrix.single i j x) (0 : Matrix (Fin s) (Fin s) (Cinf E)) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hc, hc]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem single_natAdd (i j : Fin s) (x : Cinf E) :
    Matrix.single (Fin.natAdd r i) (Fin.natAdd r j) x = blockM (0 : Matrix (Fin r) (Fin r) (Cinf E)) (Matrix.single i j x) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hn, hn]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem capR_mem (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_castAdd]; exact lie_block_mem _ _) _

theorem capS_mem (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_natAdd]; exact lie_block_mem _ _) _


variable (E) in
def nInvAlg (a r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ ψ : Sm E a, (∀ (x : BlockIx a r → Ad E) (g : GA E a), ψ.1 (unip x * g) = ψ.1 g) →
    ∀ (x : BlockIx a r → Ad E) (g : GA E a), (z ψ).1 (unip x * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ v g := by
    change (x ψ).1 _ + (y ψ).1 _ = (x ψ).1 _ + (y ψ).1 _
    rw [hx ψ hψ v g, hy ψ hψ v g]
  algebraMap_mem' c ψ hψ v g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ v g]

theorem lie_mem_nInvAlg (a r : ℕ) (X : Lie E a) : lie E a X ∈ nInvAlg E a r := by
  intro ψ hψ v g
  have e : chart ψ.1 (unip v * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ v]
    · rfl
  simp only [GlobalTheory.CuspRep.lie_apply, lieD, e]

theorem cap_mem_nInvAlg (a r : ℕ) (τ : E →+* ℂ) (u : ℂ) : cap (a := a) τ u ∈ nInvAlg E a r :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => lie_mem_nInvAlg a r _) _

theorem capStable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)) :
    ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
      (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
        ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
    ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)),
        (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) :=
  ⟨fun hF => ⟨capR_mem τ u F hF, capS_mem τ u F hF⟩, fun hF => cap_mem_nInvAlg (r + s) r τ u F hF⟩

end GlobalTheory.CompanionTheory.CTFin.CapStable

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishingStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_constant_term_vanishing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (r + s)), ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) → (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧ ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧ ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapStable.capStable | exact GlobalTheory.CompanionTheory.CTFin.CapStable.capStable | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapStable.capStable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZero
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocalFieldPow


open ValuativeRel in
theorem exists_unit_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  intro k _ _ _ _
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  have hr : r ≠ 0 := by simpa using hr0
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨Units.mk0 r hr, ?_⟩
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  rw [Units.val_mk0] at hm
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : ValuativeRel.valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ ValuativeRel.valuation k r ^ m := by
    simpa using pow_le_pow_of_le_one zero_le' hr1.le hn
  simpa using lt_of_le_of_lt h hm

end GlobalTheory.CompanionTheory.LocalFieldPow
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZero
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
open MeasureTheory ValuativeRel

noncomputable section
namespace GlobalTheory.CompanionTheory.NabsContract

theorem valuation_lt_one_of_tendsto_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0)) : valuation k (t : k) < 1 := by
  by_contra H
  rw [not_lt] at H
  have hs : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (ht.eventually hs).exists
  have hn' : valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact (not_lt.mpr (one_le_pow₀ H)) hn'

theorem nabs_lt_one_of_tendsto_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ),
    Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → nabs k t < 1 := by
  intro k _ _ _ _ t ht
  have hv := GlobalTheory.CompanionTheory.NabsContract.valuation_lt_one_of_tendsto_pow t ht
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.t2Space k
  set ν : Measure k := Measure.addHaar with hν
  set O : Set k := ((valuation k).integer : Set k) with hO_def
  set B : Set k := GlobalTheory.SplitWeil.cball t with hB_def
  have hO : IsOpen O := GlobalTheory.SplitWeil.isOpen_int k
  have hBO : B ⊆ O := fun x hx =>
    (Valuation.mem_integer_iff _ _).mpr
      (le_trans (show valuation k x ≤ valuation k (t : k) from hx) hv.le)
  have hO1 : O ⊆ GlobalTheory.SplitWeil.cball (1 : kˣ) := fun x hx => by
    have hx' := (Valuation.mem_integer_iff _ _).mp hx
    show valuation k x ≤ valuation k ((1 : kˣ) : k)
    rw [Units.val_one, map_one]
    exact hx'
  have hOfin : ν O ≠ ⊤ :=
    measure_ne_top_of_subset hO1 (GlobalTheory.SplitWeil.isCompact_cball (1 : kˣ)).measure_lt_top.ne
  have hBfin : ν B ≠ ⊤ := measure_ne_top_of_subset hBO hOfin
  have h1 : (1 : k) ∈ O \ B := by
    refine ⟨(Valuation.mem_integer_iff _ _).mpr (map_one _).le, fun h => ?_⟩
    have h' : valuation k (1 : k) ≤ valuation k (t : k) := h
    rw [map_one] at h'
    exact not_lt.mpr h' hv
  have hdiff : 0 < ν (O \ B) :=
    (hO.sdiff (GlobalTheory.SplitWeil.isCompact_cball t).isClosed).measure_pos ν ⟨1, h1⟩
  rw [measure_sdiff hBO (GlobalTheory.SplitWeil.isOpen_cball t).measurableSet.nullMeasurableSet
    hBfin, tsub_pos_iff_lt] at hdiff
  have hlt : ν.real B < ν.real O := (ENNReal.toReal_lt_toReal hBfin hOfin).mpr hdiff
  have hOpos : 0 < ν.real O :=
    ENNReal.toReal_pos (hO.measure_pos ν ⟨0, (Valuation.mem_integer_iff _ _).mpr (by simp)⟩).ne'
      hOfin
  have hmeas : ν.real B = GlobalTheory.SplitWeil.nabs k t * ν.real O :=
    GlobalTheory.SplitWeil.measureReal_cball ν t
  rw [hmeas] at hlt
  exact lt_of_mul_lt_mul_right (by rwa [one_mul]) hOpos.le

end GlobalTheory.CompanionTheory.NabsContract
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZeroStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → nabs k t < 1 := by
  first | exact @GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow | exact GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow | (intros; apply GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistAbsPow
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_of_equiv_nu {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (g : G) (c : ℂ)
    (h : ∀ v, π g v = c • v) (w : W) : σ g w = c • w := by
  rw [← Representation.Equiv.conj_apply_self g φ, LinearEquiv.conj_apply]
  simp [h]
  congr 1
  exact φ.right_inv w

theorem scalarBy_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (s : ℂ) (t : kˣ) (c : ℂ), Zl.ScalarBy x t c →
      Zl.ScalarBy (x.nu s) t (c * ((absPow k s (t ^ x.1) : ℂˣ) : ℂ)) := by
  intro k _ _ _ _ x s t c hx v
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  refine smul_of_equiv_nu (x.twEquiv (absPow k s) (isSmoothChar_absPow s))
    (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) _ (fun u => ?_) v
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.detChar_apply, hx u, smul_smul, hdet, mul_comm]

end GlobalTheory.CompanionTheory.Dblock
end

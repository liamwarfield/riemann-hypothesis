module

public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableMmRight
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI.QuotInvW

variable {m : ℕ}

def mm (a b : MtM m) : MtM m := fun i j => (Matrix.of a * Matrix.of b) i j

lemma continuous_mm : Continuous (fun p : MtM m × MtM m => mm p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mm, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma measurable_mm : Measurable (fun p : MtM m × MtM m => mm p.1 p.2) :=
  continuous_mm.measurable

lemma measurable_mm_left (b : MtM m) : Measurable (fun a : MtM m => mm a b) :=
  measurable_mm.comp (measurable_id.prodMk measurable_const)

def minv (a : MtM m) : MtM m := fun i j => (Matrix.of a)⁻¹ i j

def oneM : MtM m := fun i j => (1 : Matrix (Fin m) (Fin m) ℂ) i j

lemma mm_oneM (a : MtM m) : mm a oneM = a := by
  funext i j
  show (Matrix.of a * 1 : Matrix (Fin m) (Fin m) ℂ) i j = a i j
  rw [Matrix.mul_one]
  rfl

lemma mm_assoc (a b c : MtM m) : mm (mm a b) c = mm a (mm b c) := by
  change (Matrix.of a * Matrix.of b * Matrix.of c : Matrix (Fin m) (Fin m) ℂ) =
    Matrix.of a * (Matrix.of b * Matrix.of c)
  exact Matrix.mul_assoc _ _ _

lemma inv_mul_of {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ G) : a⁻¹ * a = 1 :=
  mul_eq_one_comm.mp (hG.2.2.2 a ha).2

lemma measurableSet_mem {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∈ G} := by
  have hc : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  exact (hG.1.preimage hc).measurableSet

lemma mm_mem {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a b : MtM m}
    (ha : Matrix.of a ∈ G) (hb : Matrix.of b ∈ G) : Matrix.of (mm a b) ∈ G :=
  hG.2.2.1 _ ha _ hb

section HidaSetting

variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

lemma ae_mem_S (h : QuotientSetting G S μG μS ν) : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by
  have := h.2.2.2.2.1.2.2.1
  rw [ae_iff]
  simpa using this

lemma weil (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν :=
  h.2.2.2.2.2.2.2 f hf

lemma nu_compl (h : QuotientSetting G S μG μS ν) : ν {x | Matrix.of x ∉ G} = 0 := by
  have hG := h.1
  have hS := h.2.1
  have hSG := h.2.2.1
  have hμG := h.2.2.2.1
  have hμS := h.2.2.2.2.1
  set C : Set (MtM m) := {x | Matrix.of x ∉ G} with hC
  have hCm : MeasurableSet C := (measurableSet_mem hG).compl
  have hW := weil h (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm, hμG.2.2.1] at hW
  have hle : ∀ x, C.indicator 1 x * μS Set.univ ≤ ∫⁻ s, C.indicator 1 (mm s x) ∂μS := by
    intro x
    by_cases hx : x ∈ C
    · have hae : ∀ᵐ s ∂μS, C.indicator (1 : MtM m → ℝ≥0∞) (mm s x) = 1 := by
        filter_upwards [ae_mem_S h] with s hs
        have : mm s x ∈ C := by
          intro hsx
          apply hx
          have h1 : (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) ∈ G :=
            hG.2.2.1 _ (hSG (hS.2.2.2 _ hs).1) _ hsx
          rwa [← Matrix.mul_assoc, inv_mul_of hS hs, Matrix.one_mul] at h1
        simp [Set.indicator_of_mem this]
      rw [lintegral_congr_ae hae]
      simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have h2 : ∫⁻ x, C.indicator 1 x * μS Set.univ ∂ν = 0 :=
    nonpos_iff_eq_zero.mp ((lintegral_mono hle).trans hW.symm.le)
  rw [lintegral_mul_const _ (measurable_one.indicator hCm), lintegral_indicator_one hCm,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd (Measure.measure_univ_eq_zero.mp h2) hμS.2.1

lemma ae_mem_G (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  rw [ae_iff]
  simpa using nu_compl h

lemma weil_inv (h : QuotientSetting G S μG μS ν) {H f : MtM m → ℝ≥0∞} (hH : Measurable H)
    (hf : Measurable f) (hHi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → H (mm s x) = H x) :
    ∫⁻ x, H x * f x ∂μG = ∫⁻ x, H x * (∫⁻ s, f (mm s x) ∂μS) ∂ν := by
  have hW := weil h (hH.mul hf)
  simp only [Pi.mul_apply] at hW
  rw [hW]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_G h] with x hx
  rw [← lintegral_const_mul (H x) (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S h] with s hs
  rw [show H (mm s x) = H x from hHi _ hs x hx]

end HidaSetting

end PI.QuotInvW
end
end

open MeasureTheory Matrix
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotInvW

variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

def avgS (μS : Measure (MtM m)) (f : MtM m → ℝ≥0∞) (x : MtM m) : ℝ≥0∞ := ∫⁻ s, f (mm s x) ∂μS

lemma measurable_avgS [SFinite μS] {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    Measurable (avgS μS f) := by
  exact (hf.comp (measurable_mm (m := m))).lintegral_prod_left'

lemma avgS_mm (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f)
    {t : MtM m} (ht : Matrix.of t ∈ S) (y : MtM m) : avgS μS f (mm t y) = avgS μS f y := by
  have hR : μS.map (rmulQ (Matrix.of t)) = μS := h.2.2.2.2.2.2.1 _ ht
  have hg : Measurable fun s => f (mm s y) := hf.comp (measurable_mm_left y)
  unfold avgS
  symm
  calc ∫⁻ s, f (mm s y) ∂μS = ∫⁻ s, f (mm s y) ∂(μS.map (rmulQ (Matrix.of t))) := by rw [hR]
    _ = ∫⁻ s, f (mm (rmulQ (Matrix.of t) s) y) ∂μS := lintegral_map hg (measurable_mm_left t)
    _ = ∫⁻ s, f (mm s (mm t y)) ∂μS := by
        congr 1; funext s
        rw [← mm_assoc]; rfl

lemma avgS_ne_zero (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f)
    (hpos : ∀ x, f x ≠ 0) (x : MtM m) : avgS μS f x ≠ 0 := by
  intro h0
  unfold avgS at h0
  have h1 := (lintegral_eq_zero_iff (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))).1 h0
  have hμ : μS Set.univ = 0 := by
    have := ae_iff.1 h1
    simpa [hpos] using this
  exact h.2.2.2.2.1.2.1 (Measure.measure_univ_eq_zero.1 hμ)

theorem ineq (h : QuotientSetting G S μG μS ν) {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x)
    {g : MtM m} (hg : Matrix.of g ∈ G) :
    ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := by
  have hGg := h.1
  haveI : SigmaFinite μG := h.2.2.2.1.1
  haveI : SigmaFinite μS := h.2.2.2.2.1.1
  obtain ⟨f0, hf0pos, hf0m, hf0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set f : MtM m → ℝ≥0∞ := fun x => (f0 x : ℝ≥0∞) with hfdef
  have hfm : Measurable f := measurable_coe_nnreal_ennreal.comp hf0m
  have hfpos : ∀ x, f x ≠ 0 := fun x => by simp [f, (hf0pos x).ne']
  have ham : Measurable (avgS μS f) := measurable_avgS hfm
  have ha0 : ∀ x, avgS μS f x ≠ 0 := avgS_ne_zero h hfm hfpos

  have hafin : ∀ᵐ x ∂ν, avgS μS f x < ⊤ := by
    apply ae_lt_top ham
    have := weil h hfm
    change ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν ≠ ⊤
    rw [← this]
    exact (hf0int.trans ENNReal.one_lt_top).ne
  obtain ⟨hginvG, hgg⟩ := hGg.2.2.2 _ hg
  have hgiG : Matrix.of (minv g) ∈ G := hginvG
  have hdet : IsUnit (Matrix.of g).det :=
    isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩
  have hgig : mm (minv g) g = oneM := by
    have := Matrix.nonsing_inv_mul (Matrix.of g) hdet
    funext i j; exact congrFun (congrFun this i) j
  have hggi : mm g (minv g) = oneM := by
    funext i j; exact congrFun (congrFun hgg i) j
  have hRG : μG.map (rmulQ (Matrix.of (minv g))) = μG := h.2.2.2.2.2.1 _ hgiG

  set F' : MtM m → ℝ≥0∞ := fun x => F x / avgS μS f (mm x (minv g)) with hF'def
  have hF'm : Measurable F' := hF.div (ham.comp (measurable_mm_left (minv g)))
  have hF'i0 : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x := by
    intro s hs x hx
    simp only [F']
    rw [hFi s hs x hx, mm_assoc, avgS_mm h hfm hs]
  have hF'i : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x :=
    fun s hs x hx => hF'i0 (Matrix.of.symm s) hs x hx
  have hL : ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν = ∫⁻ x, F' (mm x g) * f x ∂μG := by
    have := weil_inv h (H := fun x => F' (mm x g)) (f := f) (hF'm.comp (measurable_mm_left g)) hfm
      (by
        intro s hs x hx
        have key : ∀ s' : MtM m, Matrix.of s' ∈ S → F' (mm (mm s' x) g) = F' (mm x g) := by
          intro s' hs'
          rw [mm_assoc]
          exact hF'i0 s' hs' (mm x g) (mm_mem hGg hx hg)
        exact key (Matrix.of.symm s) hs)
    exact this.symm
  have hmid : ∫⁻ x, F' (mm x g) * f x ∂μG = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG := by
    have hφ : Measurable fun x => F' (mm x g) * f x := (hF'm.comp (measurable_mm_left g)).mul hfm
    calc ∫⁻ x, F' (mm x g) * f x ∂μG
        = ∫⁻ x, F' (mm x g) * f x ∂(μG.map (rmulQ (Matrix.of (minv g)))) := by rw [hRG]
      _ = ∫⁻ x, F' (mm (rmulQ (Matrix.of (minv g)) x) g) * f (rmulQ (Matrix.of (minv g)) x) ∂μG :=
          lintegral_map hφ (measurable_mm_left (minv g))
      _ = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG := by
        congr 1; funext x
        have e : mm (rmulQ (Matrix.of (minv g)) x) g = x := by
          change mm (mm x (minv g)) g = x
          rw [mm_assoc, hgig, mm_oneM]
        rw [e]; rfl
  have hR : ∫⁻ x, F' x * f (mm x (minv g)) ∂μG = ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν := by
    have := weil_inv h (H := F') (f := fun x => f (mm x (minv g))) hF'm
      (hfm.comp (measurable_mm_left (minv g))) hF'i
    rw [this]
    congr 1; funext x; congr 1
    unfold avgS
    congr 1; funext s; simp only [mm_assoc]
  have hRHS : ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν ≤ ∫⁻ x, F x ∂ν := by
    apply lintegral_mono; intro x
    simp only [F']
    by_cases hx : avgS μS f (mm x (minv g)) = ⊤
    · rw [hx]; simp
    · rw [ENNReal.div_mul_cancel (ha0 _) hx]
  have hLHS : ∫⁻ x, F (mm x g) ∂ν = ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hafin] with x hx
    simp only [F']
    rw [mm_assoc, hggi, mm_oneM, ENNReal.div_mul_cancel (ha0 x) hx.ne]
  calc ∫⁻ x, F (mm x g) ∂ν = _ := hLHS
    _ = _ := hL
    _ = _ := hmid
    _ = _ := hR
    _ ≤ _ := hRHS

theorem quotInv : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFi g0 hg0
  obtain ⟨g, rfl⟩ : ∃ g : MtM m, Matrix.of g = g0 := ⟨Matrix.of.symm g0, rfl⟩
  have hg : Matrix.of g ∈ G := hg0
  have hFi' : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x :=
    fun s hs x hx => hFi s hs x hx
  have h1 : ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := ineq h hF hFi' (g := g) hg
  obtain ⟨hginvG, hgg⟩ := h.1.2.2.2 _ hg
  have hdet : IsUnit (Matrix.of g).det :=
    isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩
  have hgig : mm (minv g) g = oneM := by
    have := Matrix.nonsing_inv_mul (Matrix.of g) hdet
    funext i j; exact congrFun (congrFun this i) j
  have h2 : ∫⁻ x, F (mm (mm x (minv g)) g) ∂ν ≤ ∫⁻ x, F (mm x g) ∂ν :=
    ineq h (F := fun x => F (mm x g)) (hF.comp (measurable_mm_left g))
      (by
        intro s hs x hx
        rw [mm_assoc]
        exact hFi' s hs _ (mm_mem h.1 hx hg))
      (g := minv g) hginvG
  simp only [mm_assoc, hgig, mm_oneM] at h2
  exact le_antisymm h1 h2

end PI.QuotInvW

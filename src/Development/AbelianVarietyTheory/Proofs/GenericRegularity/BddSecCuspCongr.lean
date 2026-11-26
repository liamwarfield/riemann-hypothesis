module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueHomExtensionSemiAbelianDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DomCongr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma isSec_of_eqOn_dom {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) (hP : X.IsSec la P) : X.IsSec la Q := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP ⊢
  obtain ⟨hd, hb, hg⟩ := hP
  refine ⟨hd.congr fun x hx => (hPQ x hx).symm, fun x hx b hb' => ?_, fun γ hγ x hx => ?_⟩
  · rw [← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb'), ← hPQ x hx, hb x hx b hb']
  · rw [← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← hPQ x hx, hg γ hγ x hx]

private lemma pnorm_eq_of_eqOn_dom (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x = X.pnorm la Q x := by
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPQ x hx]

private lemma fj_eq_of_eqOn_dom (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) {ξ : Fin r → E} (hξ : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0)
    (ν : ↥X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ ν P x = X.fj la ξ ν Q x := by
  have key : ∀ s : ↥X.Ψ → ℝ, P (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) =
      Q (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) :=
    fun s => hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj
  simp only [key]

theorem _root_.GlobalTheory.DomCongr.bddSec_cusp_congr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∀ (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ),
    (∀ x ∈ X.dom, P x = Q x) → (X.IsBddSec la P → X.IsBddSec la Q) ∧
      (P ∈ X.SS la → Q ∈ X.SS la) := by
  intro E _ _ _ r X la P Q hPQ
  have hB : X.IsBddSec la P → X.IsBddSec la Q := by
    intro hP
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsBddSec at hP ⊢
    obtain ⟨hs, C, hC⟩ := hP
    exact ⟨isSec_of_eqOn_dom X hPQ hs, C,
      fun x hx => (pnorm_eq_of_eqOn_dom X la hPQ hx) ▸ hC x hx⟩
  refine ⟨hB, fun hP => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP ⊢
  obtain ⟨hb, hc⟩ := hP
  refine ⟨hB hb, fun ξ hξ x hx => ?_⟩
  rw [← fj_eq_of_eqOn_dom X la hPQ (by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIso at hξ; exact hξ.2.1) 0 hx]
  exact hc ξ hξ x hx

end GlobalTheory.DomCongr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_fg_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), KapFG Xo c ∧ KapTrdeg Xo c Dw.dim := by
  intro E _ _ _ H Dw l Xo c
  have hs : SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have h := fun Z : Comp Xo c =>
    GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension c.F (Xo.XF c) strK Dw.dim hs Z.1 Z.2
  exact ⟨fun Z => (h Z).1, fun Z => (h Z).2⟩

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameSign

private theorem hermC_emb_eq_map_herm' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (Gm : Matrix (Fin r) (Fin r) E) (v w : Fin r → E) :
    hermC τ Gm (Data.emb τ v) (Data.emb τ w) = τ (herm Gm v w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, cc, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]

private theorem re_emb' {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) (ξ : E)
    (hξ : cc ξ = -ξ) : (τ ξ).re = 0 := by
  have h1 : τ (cc ξ) = τ (-ξ) := by rw [hξ]
  rw [cc, IsCMField.complexEmbedding_complexConj, map_neg] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.conj_re, Complex.neg_re] at h2
  linarith

private theorem im_hermForm_diagonal_eq_sum {g : ℕ} (c : Fin g → ℝ) (z w : Fin g → ℂ) :
    (hermForm (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) z w).im =
      ∑ k, c k * (z k * (starRingEnd ℂ) (w k)).im := by
  simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Complex.im_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.im_ofReal_mul]

theorem im_hermForm_signed {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (q : ℕ) (ξ : E)
    (Gm : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (idx : Fin g ≃ Ψ × Fin r)
    (hξ : cc ξ = -ξ) (x : Frame Ψ r)
    (hx : ∀ τ : Ψ, gram τ.1 Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ))
    (P : (Fin r → E) → Fin g → ℂ)
    (hP : ∀ v k, P v k = if ((idx k).2 : ℕ) < q then
      hermC (idx k).1.1 Gm (col (mat x (idx k).1) (idx k).2) (Data.emb (idx k).1.1 v)
      else ((mat x (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 v) (idx k).2) (v w : Fin r → E) :
    (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ)) (P v) (P w)).im =
      ((Algebra.trace ℚ E (ξ * herm Gm v w) : ℚ) : ℝ) := by
  classical
  rw [im_hermForm_diagonal_eq_sum (fun k => 2 * ((idx k).1.1 ξ).im), ← Equiv.sum_comp idx.symm, Fintype.sum_prod_type,
    GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hΨ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hsum := GlobalTheory.UnitFrame.im_sum_periods q τ.1 Gm (mat x τ) (hx τ) (Data.emb τ.1 v) (Data.emb τ.1 w)
  simp only [hP, Equiv.apply_symm_apply]
  rw [← Finset.mul_sum, ← Complex.im_sum, hsum, hermC_emb_eq_map_herm', map_mul, Complex.mul_re, re_emb' τ.1 ξ hξ]
  ring

theorem pos_of_pullback_pos {g : ℕ} (d : Fin g → ℝ) (h : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (hermForm (Matrix.diagonal fun k => ((d k : ℝ) : ℂ)) (h *ᵥ z) (h *ᵥ z)).re) (j : Fin g) :
    0 < d j := by
  have hinj : Function.Injective (Matrix.mulVecLin h) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have hp := hpos z hne
    rw [Matrix.mulVecLin_apply] at hz
    rw [hz] at hp
    simp [hermForm] at hp
  obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hinj (Pi.single j 1)
  rw [Matrix.mulVecLin_apply] at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h1 := congrFun hz j
    simp at h1
  have hp := hpos z hz0
  rw [hz] at hp
  simpa [hermForm, Matrix.mulVec_diagonal, Pi.single_apply] using hp

theorem im_neg_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → ∀ x ∈ X.dom, ∀ P : D.La →+ (Fin g → ℂ), (∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) → IsPeriod D (fun j => relab c σ (e j).1) P → r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0 := by
  intro E _ _ _ H Dw l c σ g e D r X φ hgood hr hp0 hΨ hEF x hx P hP hper hr0 τ hτ
  classical

  have hrtE : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (fun z : 𝓞 E => (z : E)) H.5
  have hrt : ∀ τ' : E →+* ℂ, relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
    intro τ'
    have hs : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hrtE, H.12]
      simp
    have hv : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    have hz : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hgood
    have hz0 : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · have he : (⟨τ' (H.rt : E), c.conj τ' _⟩ : c.F) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hz0.symm)
      rw [hv, he, hz]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · have he : (⟨τ' (H.rt : E), c.conj τ' _⟩ : c.F) = -IntermediateField.inclusion c.le (baseKA l).ρ := by
        apply Subtype.ext
        show τ' (H.rt : E) = ((-IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
        rw [h, IntermediateField.coe_neg, hz0]
      rw [hv, he, map_neg, hz, h]
  have hρinj : Function.Injective (relab c σ) := by
    intro τ1 τ2 h12
    ext a
    have h : σ ⟨τ1 a, c.conj τ1 a⟩ = σ ⟨τ2 a, c.conj τ2 a⟩ := congrArg (fun ρ' : E →+* ℂ => ρ' a) h12
    exact congrArg Subtype.val (σ.injective h)
  have hρ : Function.Bijective (relab c σ) := Finite.injective_iff_bijective.mp hρinj
  have hmult : ∀ τ' : E →+* ℂ, Dw.mult τ' = if τ' (H.rt : E) = H.rt0 then Dw.p else Dw.q := fun _ => rfl
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hρ Dw.mult
    (fun τ' h => by rw [hmult, if_pos ((hrt τ').1 ((hΨ _).1 h))])
    (fun τ' h => by rw [hmult, if_neg (fun h' => h ((hΨ _).2 ((hrt τ').2 h')))])
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ k,
      (relab c σ (e k).1 ∈ X.Ψ ∧ (idx k).1.1 = relab c σ (e k).1 ∧ ((idx k).2 : ℕ) = Dw.q + (e k).2) ∨
      (relab c σ (e k).1 ∉ X.Ψ ∧ (idx k).1.1 = ComplexEmbedding.conjugate (relab c σ (e k).1) ∧
        ((idx k).2 : ℕ) = Dw.q - 1 - (e k).2 ∧ ((e k).2 : ℕ) < Dw.q) :=
    ⟨e.trans f, fun k => hf (e k)⟩

  have hPa : ∀ a k, P a k = if ((idx k).2 : ℕ) < Dw.q then
      hermC (idx k).1.1 X.Gm (col (mat x (idx k).1) (idx k).2) (Data.emb (idx k).1.1 (φ a : Fin r → E))
      else ((mat x (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 (φ a : Fin r → E)) (idx k).2 := by
    intro a k
    rw [hP a k]
    unfold perFr
    rcases hidx k with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · have hi : X.p0 + ((e k).2 : ℕ) < r := by rw [hp0, ← h3]; exact (idx k).2.isLt
      have hk1 : (idx k).1 = ⟨relab c σ (e k).1, h1⟩ := Subtype.ext h2
      have hk2 : (idx k).2 = ⟨X.p0 + (e k).2, hi⟩ :=
        Fin.ext (show ((idx k).2 : ℕ) = X.p0 + (e k).2 by rw [hp0]; exact h3)
      have hnot : ¬ (((idx k).2 : ℕ) < Dw.q) := by rw [h3]; omega
      rw [dite_eq_left h1, dite_eq_left hi, if_neg hnot, hk1, hk2]
    · have hc : conjEmb (relab c σ (e k).1) ∈ X.Ψ := by
        have h5 := (idx k).1.2
        rw [h2] at h5
        exact h5
      have hj : X.p0 - 1 - ((e k).2 : ℕ) < r := by rw [hp0, ← h3]; exact (idx k).2.isLt
      have hk1 : (idx k).1 = ⟨conjEmb (relab c σ (e k).1), hc⟩ := Subtype.ext h2
      have hk2 : (idx k).2 = ⟨X.p0 - 1 - (e k).2, hj⟩ :=
        Fin.ext (show ((idx k).2 : ℕ) = X.p0 - 1 - (e k).2 by rw [hp0]; exact h3)
      have hlt : ((idx k).2 : ℕ) < Dw.q := by rw [h3]; omega
      rw [dite_eq_right h1, dite_eq_left hc, dite_eq_left hj, if_pos hlt, hk1, hk2]

  obtain ⟨x₀, b, hb, hon, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  rw [hp0] at hon
  have hξ' : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  let Q : (Fin r → E) → Fin g → ℂ := fun v k => if ((idx k).2 : ℕ) < Dw.q then
      hermC (idx k).1.1 X.Gm (col (mat (rmul x b) (idx k).1) (idx k).2) (Data.emb (idx k).1.1 v)
      else ((mat (rmul x b) (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 v) (idx k).2
  have hform : ∀ a a', (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ))
      (Q (φ a)) (Q (φ a'))).im = ((D.EF a a' : ℤ) : ℝ) := by
    intro a a'
    rw [im_hermForm_signed Dw.q (-X.ξ0) X.Gm X.Ψ X.cmType idx hξ' (rmul x b) hon Q (fun v k => rfl),
      ← hEF a a', Rat.cast_intCast]
  have hmove : ∀ a, Q (φ a) = GlobalTheory.PerBor.moveMat Dw.q idx b *ᵥ P a := fun a =>
    GlobalTheory.PerBor.moveMat_mulVec Dw.q idx hb X.Gm x (φ a : Fin r → E) (P a) (Q (φ a)) (hPa a) (fun k => rfl)
  obtain ⟨-, -, -, hspan, Hm, -, hpos, hIm⟩ := hper

  have hHm : Hm = (GlobalTheory.PerBor.moveMat Dw.q idx b)ᵀ *
      ((Matrix.diagonal fun k => ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ)) *
        (GlobalTheory.PerBor.moveMat Dw.q idx b).map (starRingEnd ℂ)) := by
    apply GlobalTheory.UnitDet.eq_of_im_hermForm_eq (Set.range P) hspan
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hIm, ← GlobalTheory.UnitDet.hermForm_mulVec, ← hmove, ← hmove, hform]
  have hpos' : ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ))
        (GlobalTheory.PerBor.moveMat Dw.q idx b *ᵥ z) (GlobalTheory.PerBor.moveMat Dw.q idx b *ᵥ z)).re := by
    intro z hz
    rw [GlobalTheory.UnitDet.hermForm_mulVec, ← hHm]
    exact hpos z hz
  have hr0' : 0 < r := Nat.pos_of_ne_zero hr0
  have h1 : (idx (idx.symm (⟨τ, hτ⟩, ⟨0, hr0'⟩))).1.1 = τ := by rw [Equiv.apply_symm_apply]
  have key : 0 < 2 * ((idx (idx.symm (⟨τ, hτ⟩, ⟨0, hr0'⟩))).1.1 (-X.ξ0)).im :=
    pos_of_pullback_pos (fun k => 2 * ((idx k).1.1 (-X.ξ0)).im) (GlobalTheory.PerBor.moveMat Dw.q idx b) hpos' _
  rw [h1, map_neg, Complex.neg_im] at key
  linarith

end GlobalTheory.FrameSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVectorStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.im_neg_of_frame_period_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → ∀ x ∈ X.dom, ∀ P : D.La →+ (Fin g → ℂ), (∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) → IsPeriod D (fun j => relab c σ (e j).1) P → r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0 := by
  first | exact @GlobalTheory.FrameSign.im_neg_of_isPeriod | exact GlobalTheory.FrameSign.im_neg_of_isPeriod | (intros; apply GlobalTheory.FrameSign.im_neg_of_isPeriod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecMulAndConstTermMul
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem _root_.GlobalTheory.bddSec_mul_and_constTerm_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r),
      ∀ (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ), X.IsBddSec la P → X.IsBddSec la' Q →
        X.IsBddSec (la + la') (P * Q) ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom,
          X.fj (la + la') ξ 0 (P * Q) x = X.fj la ξ 0 P x * X.fj la' ξ 0 Q x := by
  intro E _ _ _ r X la la' P Q hP hQ
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_mul X hP hQ, fun ξ hξ x hx => ?_⟩
  have h3e : @_root_.ReciprocityTheory.ChartRestriction.G.FD.CoefficientConvolution E _ _ _ := _root_.ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds
  have hm3d : @_root_.ReciprocityTheory.ChartRestriction.G.FD.ModerateCoefficientPositivity E _ _ _ := _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.CoefficientConvolution at h3e
  have hsum := h3e r X la la' P Q hP.1 hQ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.mod_of_bdd X hP) (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.mod_of_bdd X hQ) ξ hξ x hx 0
  have hzero : ∀ ν' ≠ (0 : ↥X.Ψ → ℝ), X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x = 0 := by
    intro ν' hν'
    by_contra hne
    apply hν'
    have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd X hm3d hP hξ ν' hx (left_ne_zero_of_mul hne)
    have h2 := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd X hm3d hQ hξ (0 - ν') hx (right_ne_zero_of_mul hne)
    funext τ
    have a := h1 τ
    have b := h2 τ
    simp only [zero_sub, Pi.neg_apply] at b
    simp only [Pi.zero_apply]
    linarith
  have hs := hasSum_single (f := fun ν' => X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x) 0 hzero
  simpa using hsum.unique hs

end GlobalTheory
end

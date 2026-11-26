module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LetterSquaredLengthLeFlowHeight
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArchBoundFlow
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb lieFac lieFac_pos toC relab rdU laU IsUnf ModelsOf
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nfac_of_add {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la l₁ l₂ : Wt X.Ψ r) (h : ∀ τ i, la τ i = l₁ τ i + l₂ τ i) :
    X.nfac la x = X.nfac l₁ x * X.nfac l₂ x := by
  simp only [Data.nfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_add (norm_pos_iff.mpr
    (div_ne_zero (FlowCoefficientBounds.dmin_ne X hx τ _) (FlowCoefficientBounds.dmin_ne X hx τ _))), h]
  congr 1
  push_cast
  ring

theorem arch_bound_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : (U.X k).dom) (C ep xi : ℝ) (κ : ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → 0 < C → 0 < ep → Even n → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 → ∃ hx : (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 ∈ (U.X k).dom, (∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep) ∧ (∀ (P : Frame (U.X k).Ψ r → ℂ) (ν : (U.X k).Ψ → ℝ), (U.X k).IsBddSec (laU U a' n k) P → ‖(U.X k).fj (laU U a' n k) ξ' ν P x.1‖ = Real.exp (4 * Real.pi * ∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ)) * ‖(U.X k).fj (laU U a' n k) ξ' ν P ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)‖) ∧ ∀ Hm, IsRiem Uw.F (Uw.ik k) (Uw.Pm k ⟨_, hx⟩) Hm → ‖κ‖ / (lieFac Dw xi a' * (U.X k).nfac (laU U a' n k) ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)) ≤ (C * (ep⁻¹) ^ (U.X k).Ψ.card) ^ ((n : ℝ) / 2) * ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k ξ' x C ep xi κ a' n hσ hU hξ hC hep hn hxi hκ
  have him : ∀ τ, (U.X k).tt ξ' x.1 τ +
      ((((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I)).im = ep := by
    intro τ; simp
  have hd := GlobalTheory.FjCauchy.flow_mem_dom (U.X k) hξ x.2
    (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) (fun τ => by rw [him]; exact hep)
  have ht : ∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ'
      (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep := fun τ => by
    rw [GlobalTheory.FjCauchy.tt_flow (U.X k) hξ x.2 _ hd, him]
  refine ⟨hd, ht, ?_, ?_⟩
  · intro P ν hP
    rw [GlobalTheory.FjCauchy.fj_flow (U.X k) hP hξ ν x.2 _ hd, norm_mul, ← mul_assoc, Complex.norm_exp,
      ← Real.exp_add]
    have hs : ∑ τ, (ν τ : ℂ) * (((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) =
        ((∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Complex.ofReal_mul, mul_assoc]
    rw [hs]
    generalize (∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) = S
    have : (4 * (Real.pi : ℂ) * Complex.I * ((S : ℂ) * Complex.I)).re = -(4 * Real.pi * S) := by
      simp
    rw [this, add_neg_cancel, Real.exp_zero, one_mul]
  · intro Hm hH
    have hb := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k ⟨_, hd⟩ Hm hσ hU hH).2.2 xi a' hxi
    have hf := nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hn hξ x.1 x.2 _ hd
    have hadd := nfac_of_add (U.X k) hd (laU U a' n k) (laU U a' 0 k) (laU U 0 n k) (by
      intro τ j
      simp only [laU]
      split_ifs <;> simp <;> ring)
    have hN := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U 0 n k)
    have hA := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U a' 0 k)
    have hL := lieFac_pos Dw xi a'
    simp only [ht, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at hf
    have hp : 0 ≤ ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹ :=
      Finset.prod_nonneg fun τ _ => (inv_pos.mpr (GlobalTheory.FjCauchy.tt_pos (U.X k) hξ x.2 τ)).le
    have he : 0 ≤ (ep⁻¹) ^ (U.X k).Ψ.card := by positivity
    rw [hκ, hadd, Real.mul_rpow hC.le hp, mul_assoc, mul_comm _ ((U.X k).nfac (laU U 0 n k) x.1), ← hf,
      Real.mul_rpow hC.le he]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hb (by positivity))
    dsimp only
    generalize (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 = y at hN hA ⊢
    field_simp

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfSumSq
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb lieFac lieFac_pos toC relab rdU laU IsUnf ModelsOf
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.IsoTime

section Pair
variable {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem trace_mul_pairE (ξ : Module.Dual ℤ X) (b : 𝓞 E) (x : X) :
    Algebra.trace ℚ E ((b : E) * pairE ξ x) = (ξ (b • x) : ℚ) := by
  classical
  have h1 : ∀ j, Algebra.trace ℚ E (((RingOfIntegers.basis E j : 𝓞 E) : E) * pairE ξ x) =
      (ξ (RingOfIntegers.basis E j • x) : ℚ) := by
    intro j
    unfold pairE
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum, Finset.sum_eq_single j]
    · have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
        (integralBasis E) j j
      rw [Algebra.traceForm_apply, if_pos rfl, integralBasis_apply] at this
      rw [← mul_assoc, mul_comm _ ((_ : ℤ) : E), ← zsmul_eq_mul, map_zsmul, mul_comm]
      erw [this]
      simp
    · intro i _ hij
      have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
        (integralBasis E) i j
      rw [Algebra.traceForm_apply, if_neg (Ne.symm hij), integralBasis_apply] at this
      rw [← mul_assoc, mul_comm _ ((_ : ℤ) : E), ← zsmul_eq_mul, map_zsmul, mul_comm]
      erw [this]
      simp
    · simp
  have hb := (RingOfIntegers.basis E).sum_repr b
  conv_lhs => rw [← hb]
  conv_rhs => rw [← hb]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_smul, Finset.sum_mul, map_zsmul, smul_assoc, smul_mul_assoc]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  have := h1 j
  simp only [zsmul_eq_mul] at *
  erw [this]
  simp

theorem pairE_smul (ξ : Module.Dual ℤ X) (a : 𝓞 E) (x : X) : pairE ξ (a • x) = (a : E) * pairE ξ x := by
  have h : ∀ j, Algebra.traceForm ℚ E (pairE ξ (a • x) - (a : E) * pairE ξ x) (integralBasis E j) = 0 := by
    intro j
    rw [Algebra.traceForm_apply, integralBasis_apply, mul_comm, mul_sub, map_sub, ← mul_assoc]
    have h1 := trace_mul_pairE ξ (RingOfIntegers.basis E j) (a • x)
    have h2 := trace_mul_pairE ξ (RingOfIntegers.basis E j * a) x
    rw [mul_smul, ← h1] at h2
    push_cast at h2
    erw [h2]
    exact sub_self _
  have h0 : Algebra.traceForm ℚ E (pairE ξ (a • x) - (a : E) * pairE ξ x) = 0 :=
    (integralBasis E).ext h
  refine sub_eq_zero.mp ((traceForm_nondegenerate ℚ E).1 _ fun n => ?_)
  rw [h0]; rfl

end Pair

theorem re_herm_eq {g : ℕ} {Λ : Type} (P : Λ → (Fin g → ℂ)) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ a b, (hermForm Hm' (L (P a)) (L (P b))).im = (hermForm Hm (P a) (P b)).im) (z : Fin g → ℂ) :
    (hermForm Hm' (L z) (L z)).re = (hermForm Hm z z).re := by
  have hs : ∀ (r : ℝ) (u : Fin g → ℂ), r • u = (r : ℂ) • u := fun r u => by ext; simp
  have h1 : ∀ b u, (hermForm Hm' (L u) (L (P b))).im = (hermForm Hm u (P b)).im := by
    intro b u
    have hu : u ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a b
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add (f := _), add_dotProduct, Complex.add_im] at *
      rw [hx, hy]
    | smul r x _ hx =>
      simp only [hermForm, hs, map_smul, smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul] at *
      rw [hx]
  have h2 : ∀ u v, (hermForm Hm' (L u) (L v)).im = (hermForm Hm u v).im := by
    intro u v
    have hu : v ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h1 a u
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at *
      rw [hx, hy]
    | smul r x _ hx =>
      simp only [hermForm, hs, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at *
      rw [hx]
  have h3 := h2 (Complex.I • z) z
  simpa [hermForm, smul_dotProduct] using h3

theorem herm_nsmul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (m : ℤ) (z : Fin g → ℂ) :
    (hermForm Hm (m • z) (m • z)).re = (m : ℝ) ^ 2 * (hermForm Hm z z).re := by
  have hs : m • z = ((m : ℝ) : ℂ) • z := by ext; simp
  simp only [hermForm, hs, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem emb_cc (τ : E →+* ℂ) (a : E) : τ (cc a) = (starRingEnd ℂ) (τ a) :=
  IsCMField.complexEmbedding_complexConj E τ a

theorem maj_smul (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = ‖c‖ ^ 2 * X.maj x τ v := by
  have h1 : ∀ u, hermC τ.1 X.Gm (c • v) u = c * hermC τ.1 X.Gm v u := by
    intro u
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : hermC τ.1 X.Gm v (c • v) = (starRingEnd ℂ) c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h3 : c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h4 : X.posPart x τ (c • v) = ‖c‖ ^ 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [← Complex.re_ofReal_mul, ← h3]
    congr 1
    simp only [h1, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  unfold Data.maj
  rw [h4, h1, h2, ← mul_assoc c, h3, Complex.re_ofReal_mul]
  ring

theorem sum_cm (X : Data E r) (f : (E →+* ℂ) → ℂ) :
    ∑ τ, f τ = ∑ τ : X.Ψ, (f τ.1 + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have hinv : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext; simp
  rw [Finset.sum_coe_sort X.Ψ (fun τ => f τ + f (ComplexEmbedding.conjugate τ)), Finset.sum_add_distrib,
    ← Finset.sum_add_sum_compl X.Ψ]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [X.cmType, hinv]; simpa using hτ
  · intro τ hτ
    simpa using (X.cmType τ).1 hτ
  · intro τ _; exact hinv τ
  · intro τ _; exact hinv τ
  · intro τ _; rw [hinv]

theorem trace_cm (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ τ : E →+* ℂ, τ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
  rw [h2, sum_cm X] at h
  have := congrArg Complex.re h
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Complex.add_re,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at this
  rw [this]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [IsCMField E] in
theorem exists_den (z : E) : ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • z) :=
  ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)).exists_integral_multiple

theorem eq_zero_of_sum_sq (X : Data E r) (d : X.Ψ → ℝ)
    (h : ∀ a : 𝓞 E, ∑ τ : X.Ψ, ‖τ.1 (a : E)‖ ^ 2 * d τ = 0) (τ : X.Ψ) : d τ = 0 := by
  classical
  have h1 : ∀ a : 𝓞 E, ∑ τ : X.Ψ, 2 * (τ.1 (a : E)).re * d τ = 0 := by
    intro a
    have e1 := h (a + 1)
    have e2 := h a
    have e3 := h 1
    have : ∑ τ : X.Ψ, 2 * (τ.1 (a : E)).re * d τ = ∑ τ : X.Ψ, ‖τ.1 ((a + 1 : 𝓞 E) : E)‖ ^ 2 * d τ -
        ∑ τ : X.Ψ, ‖τ.1 (a : E)‖ ^ 2 * d τ - ∑ τ : X.Ψ, ‖τ.1 ((1 : 𝓞 E) : E)‖ ^ 2 * d τ := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      push_cast
      simp
      ring
    rw [this, e1, e2, e3]; ring
  let D : (E →+* ℂ) → ℂ := fun τ => if hτ : τ ∈ X.Ψ then (d ⟨τ, hτ⟩ : ℂ) else
    (d ⟨ComplexEmbedding.conjugate τ, by by_contra hc; exact hτ ((X.cmType τ).2 hc)⟩ : ℂ)
  have hinv : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext; simp
  have hD1 : ∀ τ : X.Ψ, D τ.1 = d τ := fun τ => by simp [D]
  have hD2 : ∀ τ : X.Ψ, D (ComplexEmbedding.conjugate τ.1) = d τ := fun τ => by
    simp only [D, dif_neg ((X.cmType τ.1).1 τ.2), hinv]
  have h2 : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, D τ * τ (a : E) = 0 := by
    intro a
    rw [sum_cm X]
    have := congrArg (fun t : ℝ => (t : ℂ)) (h1 a)
    simp only [Complex.ofReal_sum, Complex.ofReal_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hD1, hD2, ComplexEmbedding.conjugate_coe_eq, ← mul_add, Complex.add_conj]
    push_cast; ring
  have h3 : ∀ z : E, ∑ τ : E →+* ℂ, D τ * τ z = 0 := by
    intro z
    obtain ⟨m, hm, hi⟩ := exists_den z
    have := h2 ⟨m • z, hi⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    refine (mul_eq_zero.1 ?_).resolve_left hm'
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change _ = D τ * τ (m • z)
    rw [map_zsmul, zsmul_eq_mul]; ring
  have hli : LinearIndependent ℂ (fun τ : E →+* ℂ => (τ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun τ : E →+* ℂ => (τ : E →* ℂ)) RingHom.coe_monoidHom_injective
  have h4 := Fintype.linearIndependent_iff.1 hli D (by ext z; simpa using h3 z) τ.1
  rw [hD1] at h4
  exact_mod_cast h4

theorem tt_eq_im_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (k : U.Comp) (ξ : Module.Dual ℤ a.D₀.X) (ξ' : Fin r → E) (sE : E) (w : ℂ) (x : (U.X k).dom) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), GoodEmb c σ → IsUnf U → NormOne Ha → Ha.T < w.im → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → IsBePar ξ a.be sE → (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') → ∀ τ, (U.X k).tt ξ' x.1 τ = w.im * (τ.1 sE).re := by
  intro E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha k ξ ξ' sE w x L γ hG hU hN hw _ hξ hs hL hE ⟨t, ht, htξ⟩ τ₀
  obtain ⟨nn, hn1, hn2, hn3, hn4, -, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
  obtain ⟨-, -, -, hsp, Hm, hH⟩ := Ha.period w hw
  obtain ⟨-, -, -, -, Hm', hH'⟩ := Uw.period k x
  have hmaj := (GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k x Hm' hG hU hH').1
  have hre : ∀ u, (hermForm Hm (Ha.Pw w u) (Ha.Pw w u)).re =
      ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k (γ u) : Fin r → E)) := by
    intro u
    rw [← hmaj, hL]
    refine (re_herm_eq (Ha.Pw w) hsp Hm Hm' L.toLinearMap (fun u v => ?_) _).symm
    simp only [LinearEquiv.coe_coe]
    rw [← hL, ← hL, hH'.2.2, hH.2.2, hE]
  set M : (U.X k).Ψ → ℝ := fun τ => (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 ξ') with hM
  have hreal : ∀ τ : E →+* ℂ, τ sE = ((τ sE).re : ℂ) := fun τ => by
    have := emb_cc τ sE
    rw [hs.1] at this
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  have hcc : ∀ z : E, Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z := fun z => by
    have : ((Algebra.trace ℚ E (cc z) : ℚ) : ℝ) = ((Algebra.trace ℚ E z : ℚ) : ℝ) := by
      rw [trace_cm (U.X k), trace_cm (U.X k)]
      simp only [emb_cc, Complex.conj_re]
    exact_mod_cast this
  have key : ∀ v, ∑ τ : (U.X k).Ψ, ‖τ.1 (pairE ξ (Ha.y v))‖ ^ 2 *
      ((τ.1 sE).re ^ 2 * M τ * w.im - (τ.1 sE).re) = 0 := by
    intro v
    set p : E := pairE ξ (Ha.y v) with hp
    obtain ⟨m, hm, hi⟩ := exists_den (2 * sE * p)
    set b : 𝓞 E := ⟨_, hi⟩ with hb
    have hbE : (b : E) = m • (2 * sE * p) := rfl
    have h1 : m • nn v = b • t := by
      apply (Uw.F.Di Ha.i).unimod.1
      ext v'
      have e1 := hn2 v v'
      have e2 := ht (H.bar b • v')
      rw [← (Uw.F.Di Ha.i).adj, Ha.y.map_smul] at e2
      have e3 := trace_mul_pairE ξ (H.bar b) (Ha.y v')
      have e4 := hs.2 (Ha.y v) (Ha.y v')
      rw [← hcc, H.bar_eq] at e3
      have e5 : cc (IsCMField.complexConj E (b : E) * pairE ξ (Ha.y v')) =
          m • (2 * sE * p * cc (pairE ξ (Ha.y v'))) := by
        unfold cc
        rw [map_mul, IsCMField.complexConj_apply_apply, hbE, smul_mul_assoc]
      rw [e5, map_zsmul, hp, e4, ← e2, ← e1] at e3
      have : (((Uw.F.Di Ha.i).EF (m • nn v) v' : ℤ) : ℚ) = (((Uw.F.Di Ha.i).EF (b • t) v' : ℤ) : ℚ) := by
        rw [map_zsmul, LinearMap.smul_apply]
        simp only [zsmul_eq_mul, smul_eq_mul] at e3 ⊢
        push_cast at e3 ⊢
        linarith
      exact_mod_cast this
    have h2 : Ha.N v = Ha.Pw w (nn v) := by
      rw [Ha.Pw_eq, hn1 (nn v), hn4 _ (hn3 v), map_zero, smul_zero, add_zero, hn1]
    have h3 := hre (m • nn v)
    rw [map_zsmul, herm_nsmul, ← h2, h1] at h3
    have h4 : ∀ τ : (U.X k).Ψ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k (γ (b • t)) : Fin r → E)) =
        (m : ℝ) ^ 2 * (4 * (τ.1 sE).re ^ 2 * ‖τ.1 p‖ ^ 2 * M τ) := by
      intro τ
      have : Data.emb τ.1 (Uw.φ k (γ (b • t)) : Fin r → E) = τ.1 (b : E) • Data.emb τ.1 ξ' := by
        rw [map_smul, map_smul, Submodule.coe_smul, htξ]
        ext i
        simp only [Data.emb, Pi.smul_apply, smul_eq_mul, ← map_mul]
        rfl
      rw [this, maj_smul, hbE, map_zsmul, zsmul_eq_mul, map_mul, map_mul, hreal τ.1]
      simp only [norm_mul, mul_pow, Complex.norm_intCast, sq_abs, Complex.norm_real, Real.norm_eq_abs, map_ofNat,
        Complex.norm_ofNat, Complex.ofReal_re, hM]
      ring
    simp only [h4, ← Finset.mul_sum] at h3
    have hm' : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm)
    have h5 := mul_left_cancel₀ hm' h3
    have h6 := hN w hw Hm hH v
    have h7 : ((a.be (Ha.y v) (Ha.y v) : ℤ) : ℝ) = ∑ τ : (U.X k).Ψ, 4 * ‖τ.1 p‖ ^ 2 * (τ.1 sE).re := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hs.2 (Ha.y v) (Ha.y v))
      simp only [Rat.cast_intCast] at this
      rw [← this, trace_cm (U.X k)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← hp, mul_assoc, map_mul, map_mul, map_mul, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        hreal τ.1, map_ofNat]
      have e : (2 : ℂ) * ((τ.1 sE).re : ℂ) * ((‖τ.1 p‖ ^ 2 : ℝ) : ℂ) =
          ((2 * (τ.1 sE).re * ‖τ.1 p‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.ofReal_re, Complex.ofReal_re]
      ring
    rw [h5, h7, Finset.sum_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h6
    refine mul_left_cancel₀ (four_ne_zero) ?_
    rw [mul_zero, ← h6, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, ξ y₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hξ (LinearMap.ext hc)
  obtain ⟨v₀, rfl⟩ := Ha.y_onto y₀
  have hp0 : (pairE ξ (Ha.y v₀) : E) ≠ 0 := fun h0 => hy₀ (by
    have := trace_mul_pairE ξ (1 : 𝓞 E) (Ha.y v₀)
    rw [h0, mul_zero, map_zero, one_smul] at this
    exact_mod_cast this.symm)
  have hs0 : sE ≠ 0 := fun h0 => by
    have e1 := a.be_pos (Ha.y v₀) (fun h => hy₀ (by rw [h, map_zero]))
    have e2 := hs.2 (Ha.y v₀) (Ha.y v₀)
    rw [h0] at e2
    simp only [mul_zero, zero_mul, map_zero] at e2
    have : a.be (Ha.y v₀) (Ha.y v₀) = 0 := by exact_mod_cast e2.symm
    omega
  have hfin := eq_zero_of_sum_sq (U.X k) (fun τ => ‖τ.1 (pairE ξ (Ha.y v₀))‖ ^ 2 *
      ((τ.1 sE).re ^ 2 * M τ * w.im - (τ.1 sE).re)) (fun b => by
    rw [← key (b • v₀)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_smul, pairE_smul, map_mul, norm_mul]
    ring) τ₀
  have hs1 : (τ₀.1 sE).re ≠ 0 := fun h0 => by
    have := hreal τ₀.1
    rw [h0] at this
    exact hs0 ((map_eq_zero τ₀.1).1 (by simpa using this))
  have hq := (mul_eq_zero.1 hfin).resolve_left
    (pow_ne_zero _ (norm_ne_zero_iff.2 ((map_ne_zero τ₀.1).2 hp0)))
  have hq' : M τ₀ * (w.im * (τ₀.1 sE).re) = 1 := by
    apply mul_left_cancel₀ hs1
    linear_combination hq
  change 1 / M τ₀ = _
  rw [one_div]
  exact (eq_inv_of_mul_eq_one_right hq').symm

end GlobalTheory.ArcQ.IsoTime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLe
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb lieFac lieFac_pos toC relab rdU laU IsUnf ModelsOf
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArchCM

theorem herm_sum_le {g m : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (w : Fin m → (Fin g → ℂ)) {b : ℝ}
    (hw : ∀ k, (hermForm Hm (w k) (w k)).re ≤ b) :
    (hermForm Hm (∑ k, w k) (∑ k, w k)).re ≤ (m : ℝ) ^ 2 * b := by
  have h0 : ∀ z, 0 ≤ (hermForm Hm z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz, hermForm]
    · exact (hpos z hz).le
  have h1 : ∀ i j, (hermForm Hm (w i) (w j)).re + (hermForm Hm (w j) (w i)).re ≤ 2 * b := fun i j => by
    have := h0 (w i - w j)
    have e1 := hw i
    have e2 := hw j
    simp only [hermForm, star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, Complex.sub_re] at *
    linarith
  have h2 : (hermForm Hm (∑ k, w k) (∑ k, w k)).re = ∑ i, ∑ j, (hermForm Hm (w i) (w j)).re := by
    simp only [hermForm, star_sum, Matrix.mulVec_sum, sum_dotProduct, dotProduct_sum, Complex.re_sum]
    exact Finset.sum_comm
  have h3 : 2 * (hermForm Hm (∑ k, w k) (∑ k, w k)).re =
      ∑ i, ∑ j, ((hermForm Hm (w i) (w j)).re + (hermForm Hm (w j) (w i)).re) := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => (hermForm Hm (w j) (w i)).re), ← h2]
    ring
  have h4 : ∑ i, ∑ j, ((hermForm Hm (w i) (w j)).re + (hermForm Hm (w j) (w i)).re) ≤
      ∑ _i : Fin m, ∑ _j : Fin m, 2 * b := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
  nlinarith

theorem herm_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z : Fin g → ℂ) :
    (hermForm Hm (a • z) (a • z)).re = ‖a‖ ^ 2 * (hermForm Hm z z).re := by
  simp only [hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    Complex.star_def]
  rw [← _root_.mul_assoc, mul_comm _ a, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

theorem herm_single {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    hermForm Hm (Pi.single j 1) (Pi.single j 1) = Hm j j := by
  simp [hermForm, ← Pi.single_star]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem le_of_invBl {f : (ArcLt Dw → ℂ) → ℝ} (hf : Continuous f) (ρ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ)
    (hρ : ∀ τ k, 0 < ρ τ k) {B : ℝ} (h : ∀ x, InvBl x → (∀ v, ‖x v‖ ≤ ρ v.1 v.2.2) → f x ≤ B)
    (x : ArcLt Dw → ℂ) (hx : ∀ v, ‖x v‖ ≤ ρ v.1 v.2.2) : f x ≤ B := by
  classical
  let y : ArcLt Dw → ℂ := fun v => Matrix.diagonal (fun k => (ρ v.1 k : ℂ)) v.2.1 v.2.2
  have hy : ∀ v, ‖y v‖ ≤ ρ v.1 v.2.2 := fun v => by
    simp only [y, Matrix.diagonal_apply]
    split_ifs with hv
    · rw [hv, Complex.norm_real, Real.norm_of_nonneg (hρ _ _).le]
    · simpa using (hρ _ _).le
  let Q : ∀ τ : E →+* ℂ, Polynomial ℂ := fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) =>
    Polynomial.C (x ⟨τ, (i, k)⟩) + Polynomial.X * Polynomial.C (y ⟨τ, (i, k)⟩ - x ⟨τ, (i, k)⟩)).det
  have hQ : ∀ τ (t : ℂ), (Q τ).eval t = (Matrix.of fun i k : Fin (Dw.mult τ) =>
      x ⟨τ, (i, k)⟩ + t * (y ⟨τ, (i, k)⟩ - x ⟨τ, (i, k)⟩)).det := fun τ t => by
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i k
    simp [mul_comm]
  have hQ0 : ∀ τ, Q τ ≠ 0 := fun τ h0 => by
    have := hQ τ 1
    rw [h0, Polynomial.eval_zero] at this
    have e : (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ + 1 * (y ⟨τ, (i, k)⟩ - x ⟨τ, (i, k)⟩)) =
        Matrix.diagonal fun k => (ρ τ k : ℂ) := by
      ext i k
      simp [y]
    rw [e, Matrix.det_diagonal] at this
    exact Finset.prod_ne_zero_iff.2 (fun k _ => Complex.ofReal_ne_zero.2 (hρ τ k).ne') this.symm
  have hc : Continuous fun t : ℝ => f fun v => x v + (t : ℂ) * (y v - x v) := hf.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at ht
  refine le_of_tendsto ht ?_
  have e1 : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ τ, (Q τ).eval (t : ℂ) ≠ 0 := by
    refine Filter.eventually_all.2 fun τ => ?_
    have hfin : {t : ℝ | (Q τ).IsRoot (t : ℂ)}.Finite :=
      (Polynomial.finite_setOf_isRoot (hQ0 τ)).preimage Complex.ofReal_injective.injOn
    exact ((nhdsGT_le_nhdsNE 0).trans (nhdsNE_le_cofinite 0)) hfin.compl_mem_cofinite
  filter_upwards [e1, Ioo_mem_nhdsGT (zero_lt_one (α := ℝ))] with t h1 h2
  refine h _ (fun τ => ?_) fun v => ?_
  · rw [← hQ]; exact h1 τ
  · have e : x v + (t : ℂ) * (y v - x v) = ((1 - t : ℝ) : ℂ) * x v + (t : ℂ) * y v := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 h2.2.le),
      Real.norm_of_nonneg h2.1.le]
    nlinarith [hx v, hy v, h2.1, h2.2]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem cfOf_le {K₁ : Type} [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (em : K₁ →+* ℂ) (F : Rul Xo c)
    (ρ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (hρ : ∀ τ k, 0 < ρ τ k) {B : ℝ}
    (h : ∀ x, InvBl x → (∀ v, ‖x v‖ ≤ ρ v.1 v.2.2) → ‖ajAt d em F x‖ ≤ B) :
    ‖em (cfOf d.yF d.μ d.jj F)‖ * ∏ v : ArcLt Dw, ρ v.1 v.2.2 ^ d.μ v ≤ B := by
  classical
  set P := arcNum (evR Xo c F d.yF) with hP
  let G : MvPolynomial (ArcLt Dw) ℂ := ∑ m ∈ P.support, MvPolynomial.monomial m (em ((P.coeff m).coeff d.jj))
  have hG : ∀ x, MvPolynomial.eval x G = ajAt d em F x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_sum, MvPolynomial.eval_monomial, ajAt, Finsupp.prod, hP]
  have hc : G.coeff d.μ = em (cfOf d.yF d.μ d.jj F) := by
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', cfOf, ← hP]
    split_ifs with hm
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hm]; simp
  rw [← hc]
  refine coeff_cauchy_bound _ G (fun v => ρ v.1 v.2.2) B d.μ (fun v => hρ _ _) fun z hz => ?_
  exact le_of_invBl (f := fun x => ‖MvPolynomial.eval x G‖) (MvPolynomial.continuous_eval G).norm ρ hρ
    (fun x h1 h2 => by rw [hG]; exact h x h1 h2) z hz

omit [IsCMField E] in
theorem one_le_rdE : 1 ≤ rdE E := by
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (NumberField.discr_ne_zero E)
  unfold dE
  exact_mod_cast this

theorem two_mul_fdeg {r : ℕ} (X : Data E r) : 2 * fdeg E = Module.finrank ℚ E := by
  have h := IsoTime.trace_cm X 1
  have h2 : Algebra.trace ℚ E 1 = Module.finrank ℚ E := by
    simpa using Algebra.trace_algebraMap (R := ℚ) (S := E) (x := 1)
  rw [h2] at h
  simp only [map_one, Complex.one_re, Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi, nsmul_eq_mul] at h
  have : ((2 * fdeg E : ℕ) : ℝ) = (Module.finrank ℚ E : ℕ) := by push_cast at h ⊢; linarith
  exact_mod_cast this

theorem sqrt_discr {r : ℕ} (X : Data E r) : Real.sqrt |((NumberField.discr E : ℤ) : ℝ)| = rdE E ^ fdeg E := by
  have h := two_mul_fdeg X
  have hp : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  rw [rdE, dE, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow]
  congr 1
  rw [← h] at hp ⊢
  push_cast at hp ⊢
  have : (fdeg E : ℝ) ≠ 0 := by intro h0; rw [h0] at hp; simp at hp
  field_simp

theorem const_le (r : ℕ) {La c₁ T C : ℝ} (hLa : 1 ≤ La) (hT : 0 < T) (hC : 0 < C) (hCT : C ≤ T ^ 2 * rdE E ^ fdeg E)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (h0 : ∀ τ i, 0 ≤ h τ i)
    (hh : ∀ τ i, h τ i ≤ (r * (La * Real.sqrt (max 1 c₁))) ^ 2) :
    (C * (max 1 c₁) ^ fdeg E) ^ ((n : ℝ) / 2) * ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), h τ i ^ ((a (τ, (i : ℕ)) : ℝ) / 2) ≤
      T ^ n * Real.exp (archP E r La c₁ * ((absA Dw a : ℝ) + (fdeg E : ℝ) * n)) := by
  have hM : 1 ≤ max 1 c₁ := le_max_left _ _
  have hrd := one_le_rdE (E := E)
  have l1 := Real.log_nonneg hM
  have l2 := Real.log_nonneg hLa
  have l3 := Real.log_nonneg hrd
  have l4 := Real.log_natCast_nonneg r
  set e := Real.exp (archP E r La c₁) with he
  have he0 : 0 < e := Real.exp_pos _
  have hsq : ∀ (u v : ℝ) (k : ℕ), 0 ≤ u → 0 ≤ v → u ≤ v ^ 2 → u ^ ((k : ℝ) / 2) ≤ v ^ k := fun u v k hu hv huv => by
    refine (Real.rpow_le_rpow hu huv (by positivity)).trans (le_of_eq ?_)
    rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have e1 : r * (La * Real.sqrt (max 1 c₁)) ≤ e := by
    have a1 : Real.sqrt (max 1 c₁) = Real.exp (Real.log (max 1 c₁) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
      congr 1; ring
    calc r * (La * Real.sqrt (max 1 c₁))
        ≤ Real.exp (Real.log r) * (Real.exp (Real.log La) * Real.exp (Real.log (max 1 c₁) / 2)) := by
          rw [a1]
          gcongr <;> exact Real.le_exp_log _
      _ ≤ e := by
          rw [← Real.exp_add, ← Real.exp_add, he, archP]
          exact Real.exp_le_exp.2 (by linarith)
  have e2 : rdE E * max 1 c₁ ≤ e ^ 2 := by
    calc rdE E * max 1 c₁ ≤ Real.exp (Real.log (rdE E)) * Real.exp (Real.log (max 1 c₁)) := by
          gcongr <;> exact Real.le_exp_log _
      _ ≤ e ^ 2 := by
          rw [← Real.exp_add, he, ← Real.exp_nat_mul, archP]
          exact Real.exp_le_exp.2 (by push_cast; linarith)
  have b1 : (C * (max 1 c₁) ^ fdeg E) ^ ((n : ℝ) / 2) ≤ (T * e ^ fdeg E) ^ n := by
    refine hsq _ _ _ (by positivity) (by positivity) ?_
    calc C * (max 1 c₁) ^ fdeg E ≤ T ^ 2 * rdE E ^ fdeg E * (max 1 c₁) ^ fdeg E := by gcongr
      _ = T ^ 2 * (rdE E * max 1 c₁) ^ fdeg E := by rw [mul_pow, _root_.mul_assoc]
      _ ≤ T ^ 2 * (e ^ 2) ^ fdeg E := by gcongr
      _ = _ := by ring
  have b2 : ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), h τ i ^ ((a (τ, (i : ℕ)) : ℝ) / 2) ≤ e ^ absA Dw a := by
    rw [absA, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (h0 τ i) _) fun τ _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (h0 τ i) _) fun i _ => ?_
    exact hsq _ _ _ (h0 τ i) he0.le ((hh τ i).trans (by gcongr))
  refine (mul_le_mul b1 b2 (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg (h0 τ i) _) (by positivity)).trans (le_of_eq ?_)
  have : archP E r La c₁ * ((absA Dw a : ℝ) + (fdeg E : ℝ) * n) =
      ((absA Dw a + fdeg E * n : ℕ) : ℝ) * archP E r La c₁ := by push_cast; ring
  rw [this, Real.exp_nat_mul, ← he]
  ring

theorem num_le {A u K e e' J S Lf N B : ℝ} (hid : A * u = K * (e * u * J)) (hu : u ≠ 0) (hJ : J ≤ S / Lf / N)
    (hK : K / (Lf * N) ≤ B) (he : e ≤ e') (he0 : 0 ≤ e) (hK0 : 0 ≤ K) (hJ0 : 0 ≤ J) (hS : 0 ≤ S) : A ≤ S * e' * B := by
  have h1 : A = K * (e * J) := mul_right_cancel₀ hu (by rw [hid]; ring)
  have he' := he0.trans he
  calc A = K * (e * J) := h1
    _ ≤ K * (e' * (S / Lf / N)) := by gcongr
    _ = S * e' * (K / (Lf * N)) := by rw [div_div]; ring
    _ ≤ _ := by gcongr

theorem line_pos {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)}
    {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {th : a.D₀.P.L.Sec} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}
    (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ) :
    0 < s.Tl.n em ∧ ∀ τ k, 0 < (s.line τ k).n em := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3, -⟩ := s.good
  refine ⟨h3.2 em, fun τ k => ?_⟩
  unfold CMIn.line
  cases s.kind τ k with
  | none => exact zero_lt_one
  | some m =>
    have h := s.L_good.2.2.2 m
    simp only [Option.elim]
    split at h
    · rw [h]; exact (h1 _).1.2 em
    · rw [h]; exact (h2 _).1.2 em

theorem norm_cfOf_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (xi S : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → 1 ≤ La → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xi) → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, 0 ≤ S → (∀ k, ∀ y ∈ (U.X k).dom, lieFac Dw xi a' * (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S) → ‖em (cfOf d.yF d.μ d.jj F)‖ * (s.valLine d.μ n).n em ≤ S * Real.exp (4 * Real.pi + GlobalTheory.ArcCM.archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s em r U xi S a' n hstd hLa hgood hunf
    hxi hdom htv F hF hS0 hS
  obtain ⟨hover, ⟨y₀, hy₀, hc⟩, hpush⟩ := hstd
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  letI : Algebra c.F ℂ⸨X⸩ := (ArcId.cstL.comp (em.comp (algebraMap c.F K₁))).toAlgebra
  obtain ⟨Uw⟩ := GlobalTheory.T.nonempty_unifWitnessData_of_isUnf E H Dw l Xo c _ r U hunf
  have hth : ThNZ d.th := s.th_nz
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ ℂ _
    (d.a.restrict (c.V d.Wp).subtype) em em.injective ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) rfl
  obtain ⟨hW, hlet, htan, hthx, hnz⟩ := hbc a₁ p hp
  obtain ⟨W₁, hW₁⟩ := hW d.χ d.W
  choose e₁ he₁ using fun τ k => (hlet (d.e τ k)).exists
  obtain ⟨th₁, hth₁⟩ := (hthx d.th).exists
  have hover₁ : (spMap (PowerSeries.map em) ≫ d.χ) ≫ d.Y.s = spMap (PowerSeries.C (R := ℂ)) ≫
      spMap ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) := by
    rw [Category.assoc, hover, ArcId.sp_comp, ArcId.sp_comp, ArcId.sp_comp]
    congr 1
    exact RingHom.ext fun x => PowerSeries.map_C _ _
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ d.Y (em.comp (algebraMap c.F K₁)) a₁ _ W₁ Uw.g _ Uw.F hgood
    ((GlobalTheory.Relab.relab_good E H l c _ hgood).2.2.2 Dw Uw.g Uw.e) (GlobalTheory.ArcInTest.exists_values c d.Wp) hover₁
    (ArcId.generic_mem d em)
  let f : a₁.D₀.X ≃ₗ[𝓞 E] d.a.D₀.X := { p.xe with map_smul' := hp.2.1 }
  have hrk := f.finrank_eq.trans s.rk
  have hξ : s.ξ.comp (f.toLinearMap.restrictScalars ℤ) ≠ 0 := fun h => s.ξ_ne (LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := f.surjective y
    exact LinearMap.congr_fun h y)
  have hβ := ArcId.betaAt_comp f s.ξ hp.2.2.1 s.beta
  have hw : Ha.T < (((Ha.T + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize ((Ha.T + 1 : ℝ) : ℂ) * Complex.I = w at hw
  obtain ⟨k, ξ', sE, C, hiso, hsE, -, -, hC, hCle, hmain⟩ := GlobalTheory.T.laurentCoeff_sectionValue_arc_eq_fourierJacobi h1 h2 E H Dw l Xo c _ r U Uw _ _ d.Y a₁ _ W₁
    Ha th₁ _ s.ν₀ d.jj a' n hev hgood hunf (fun _ => rfl) hover₁ (mono_spMap_subtype _) hpush (hnz _ _ hth₁ hth) hrk hξ hβ
    hdom htv w hw
  obtain ⟨v₁, v₂, -, v₄⟩ := GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent h1.globalFns E H Dw l Xo c _ _ _ d.Y a₁ _ W₁ _ _ Uw.F Ha
  choose z₁ hz₁ using fun τ i => (v₁ (e₁ τ i) (htan _ _ (he₁ τ i) (s.tan τ i))).exists
  have hN : NormOne Ha := GlobalTheory.T.normalisedTrivialisation_normOne_complexReading hK E H Dw l Xo c _ _ _ d.Y a₁ _ W₁ _ _ Uw.F Ha n' s.n_pos
    ((GlobalTheory.T.isTauCanonical_iff_of_isPullDeg_tauBimult hK K₁ ℂ em _ _ p n' em.injective d.a.bimult a₁.bimult).1 s.tau)
  have hCT := hCle _ (((GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms hK E H Dw l c K₁ d.a d.e d.th d.jj n' La c₁ s em).2.2.2 _ p).1 th₁ hth₁)
  rw [sqrt_discr (U.X k)] at hCT
  obtain ⟨hT, hl⟩ := line_pos s em
  have hL := lieFac_pos Dw xi a'
  have hM : 0 < max 1 c₁ := lt_max_of_lt_left zero_lt_one
  have hep : 0 < (max 1 c₁)⁻¹ := inv_pos.2 hM
  have hS' : ∀ y ∈ (U.X k).dom, (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S / lieFac Dw xi a' := fun y hy =>
    (le_div_iff₀' hL).2 (hS k y hy)
  have hb : (U.X k).IsBddSec (laU U a' n k) (rdU U F k) := ⟨hunf.2.2.2.2.1 a' n hdom F hF k, _, hS'⟩
  have htr : (max 1 c₁)⁻¹ * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ 1 := by
    have e1 := IsoTime.trace_cm (U.X k) s.ν₀
    have e2 := s.tr
    rw [← Finset.mul_sum] at e1
    rw [inv_mul_le_iff₀ hM]
    have := le_max_right 1 c₁
    linarith
  have hjj : 2 * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re * (τ.1 sE).re = d.jj := by
    rw [ArcCoeff.two_sum_eq_trace (U.X k) hβ.1 hsE.1, (hβ.2 sE hsE).1, Rat.cast_intCast]
  have key := cfOf_le d em F (fun τ i => ((s.line τ i).n em)⁻¹) (fun τ i => inv_pos.2 (hl τ i))
    (B := S * Real.exp (4 * Real.pi) * (s.Tl.n em ^ n *
      Real.exp (archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)))) fun x hx hxρ => by
    choose e₂ he₂ using fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) => (v₂ (∑ j, x ⟨τ, (i, j)⟩ • z₁ τ j)).exists
    obtain ⟨-, y, hy, hval⟩ := ArcId.exists_frPt_at h1 h2 hev d em (fun _ => rfl) hy₀ hc hth hp hW₁ he₁ hth₁
      (hnz _ _ hth₁ hth) hx (fun τ i => (v₄ _ _ _ _ _ (hz₁ τ)).2 (he₂ τ i)) a' n
    obtain ⟨fr, κ, L, gm, hLgm, hEgm, hLz, ht, hκ, hFj⟩ := hmain e₂ _ y hy he₂
    have htt := IsoTime.tt_eq_im_mul E H Dw l Xo c _ r U Uw _ _ d.Y a₁ _ W₁ Ha k _ ξ' sE w fr L gm hgood hunf hN hw hrk hξ
      hsE hLgm hEgm ht
    obtain ⟨hx'', htep, hfl, hbd⟩ := arch_bound_flow E H Dw l Xo c _ r U Uw k ξ' fr C _ xi κ a' n hgood hunf hiso hC hep
      hdom.2 (hxi k) hκ
    obtain ⟨-, -, -, -, Hm, hH⟩ := Uw.period k ⟨_, hx''⟩
    have hH' : IsRiem Uw.F (Uw.ik k) (Uw.Pm k ⟨_, hx''⟩) Hm := hH
    have hlen := fun τ i => GlobalTheory.T.letter_squaredLength_le_flow_height hK E H Dw l Xo c K₁ d.a d.e d.th d.jj n' La c₁ s em _ r U Uw _ _ d.Y a₁ p _ W₁
      Ha k ξ' fr ⟨_, hx''⟩ _ w L gm _ Hm rfl hgood hunf hp hLa hep hiso hw hLgm hEgm ht rfl htep hH' τ i _ _ (he₁ τ i)
      (hz₁ τ i)
    rw [inv_inv, max_eq_right (le_max_left 1 c₁)] at hlen
    have hdiag : ∀ τ (i : Fin (Dw.mult τ)), Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re ≤
        (r * (La * Real.sqrt (max 1 c₁))) ^ 2 := fun τ i => by
      have hm : (Dw.mult τ : ℝ) ≤ r := by
        have : Dw.mult τ ≤ r := by
          rw [hunf.1]
          unfold Datum.mult
          split_ifs <;> omega
        exact_mod_cast this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← herm_single Hm, ← hLz, map_sum]
      have := herm_sum_le hH'.2.1 (fun j => L (x ⟨τ, (i, j)⟩ • z₁ τ j))
        (b := (La * Real.sqrt (max 1 c₁)) ^ 2 / Real.pi) fun j => by
          rw [le_div_iff₀' Real.pi_pos, map_smul, herm_smul, mul_left_comm]
          have e1 : ‖x ⟨τ, (i, j)⟩‖ ≤ ((s.line τ j).n em)⁻¹ := hxρ ⟨τ, (i, j)⟩
          have e2 := (hl τ j).ne'
          calc _ ≤ ‖x ⟨τ, (i, j)⟩‖ ^ 2 * (La * Real.sqrt (max 1 c₁) * (s.line τ j).n em) ^ 2 :=
                mul_le_mul_of_nonneg_left (hlen τ j) (by positivity)
            _ ≤ (((s.line τ j).n em)⁻¹) ^ 2 * (La * Real.sqrt (max 1 c₁) * (s.line τ j).n em) ^ 2 := by gcongr
            _ = _ := by field_simp
      rw [← mul_div_assoc, le_div_iff₀' Real.pi_pos] at this
      refine this.trans ?_
      rw [mul_pow (r : ℝ)]
      gcongr
    have hκb := hbd Hm hH'
    rw [inv_inv, ← Fintype.card_coe, QuadraticCoefficientForms.card_Psi] at hκb
    replace hκb := hκb.trans (const_le r hLa hT hC hCT a' n _ (fun τ i => mul_nonneg Real.pi_pos.le (by
      rw [← herm_single Hm]
      exact (hH'.2.1 _ (by simp)).le)) hdiag)
    have hcau := FlowCoefficientBounds.fj_bound (U.X k) _ _ _ hS' hiso (fun τ => (τ.1 s.ν₀).re) hx''
    have hnf := FlowCoefficientBounds.nfac_pos (U.X k) hx'' (laU U a' n k)
    have hid := congrArg norm (hFj F hF hb)
    rw [norm_mul, norm_mul, hfl _ _ hb] at hid
    have hexp : Real.exp (4 * Real.pi * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re * ((max 1 c₁)⁻¹ - (U.X k).tt ξ' fr.1 τ)) =
        Real.exp (4 * Real.pi * ((max 1 c₁)⁻¹ * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re)) * ‖eTwoPi w ^ d.jj‖ := by
      rw [norm_zpow, eTwoPi, Complex.norm_exp, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_add, ← hjj]
      congr 1
      simp only [htt, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    have hne : ‖eTwoPi w ^ d.jj‖ ≠ 0 := norm_ne_zero_iff.2 (zpow_ne_zero _ (Complex.exp_ne_zero _))
    have hE : Real.exp (4 * Real.pi * ((max 1 c₁)⁻¹ * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re)) ≤ Real.exp (4 * Real.pi) :=
      Real.exp_le_exp.2 (mul_le_of_le_one_right (by positivity) htr)
    rw [hval F hF, map_one, one_pow, _root_.one_mul]
    rw [hexp] at hid
    exact num_le hid hne ((le_div_iff₀ hnf).2 hcau) hκb hE (Real.exp_pos _).le (norm_nonneg _) (norm_nonneg _) hS0
  refine le_of_eq_of_le ?_ ((div_le_div_of_nonneg_right key (pow_pos hT n).le).trans (le_of_eq ?_))
  · simp only [CMIn.valLine, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow, inv_pow, Finset.prod_inv_distrib]
    ring
  · rw [Real.exp_add]
    field_simp

end GlobalTheory.ArchCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb lieFac lieFac_pos toC relab rdU laU IsUnf ModelsOf
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cmArcCoefficientFunctional_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (xi S : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → 1 ≤ La → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xi) → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, 0 ≤ S → (∀ k, ∀ y ∈ (U.X k).dom, lieFac Dw xi a' * (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S) → ‖em (cfOf d.yF d.μ d.jj F)‖ * (s.valLine d.μ n).n em ≤ S * Real.exp (4 * Real.pi + GlobalTheory.ArcCM.archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)) := by
  first | exact @GlobalTheory.ArchCM.norm_cfOf_le | exact GlobalTheory.ArchCM.norm_cfOf_le | (intros; apply GlobalTheory.ArchCM.norm_cfOf_le <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueHomExtensionSemiAbelianDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem evR_frBor_of_isDomain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsDomain S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  let φ : S →ₐ[c.F] FractionRing S := IsScalarTower.toAlgHom c.F S (FractionRing S)
  have hφ : Function.Injective φ := IsFractionRing.injective S (FractionRing S)
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (FractionRing S)ˣ := fun i => Units.map (φ : S →* FractionRing S) (t i)
  have hb : FrBor t' z z' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c (FractionRing S)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := hL.wt a n F hF _ t' z z' (hL.test _ _) (hL.test _ _) hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  apply hφ
  rw [hw, map_mul]
  congr 1
  simp [wchar, t']

theorem evR_natural_weight_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∀ (S : Type) [CommRing S] [Algebra c.F S] [IsReduced S], (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c F z = φ (evR Xo c F y)) ∧ (IsDomain S → (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y) ∧ ∀ (s : S) (y y' : FrPt Xo c S), FrChg (fun _ => 1) s y y' → evR Xo c F y' = s ^ n * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c hL a n F hF S _ _ _
  refine ⟨fun T _ _ φ y z h => GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S T φ y z h,
    fun hD => ⟨fun t y y' h => evR_frBor_of_isDomain hL hF t y y' h, fun s y y' h => ?_⟩⟩
  obtain ⟨u, rfl⟩ := ((GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [evR_frBor_of_isDomain hL hF t y y' hb]
  congr 1
  simp [wchar, t, ex, Fintype.prod_option]

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_eval_natural_weight_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∀ (S : Type) [CommRing S] [Algebra c.F S] [IsReduced S], (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c F z = φ (evR Xo c F y)) ∧ (IsDomain S → (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y) ∧ ∀ (s : S) (y y' : FrPt Xo c S), FrChg (fun _ => 1) s y y' → evR Xo c F y' = s ^ n * evR Xo c F y) := by
  first | exact @GlobalTheory.ArcQ.evR_natural_weight_scaling | exact GlobalTheory.ArcQ.evR_natural_weight_scaling | (intros; apply GlobalTheory.ArcQ.evR_natural_weight_scaling <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nonempty_unfWit_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → Nonempty (UnfWit U) := by
  intro E _ _ _ H Dw l Xo c σ r U h
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := h
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnfStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_unifWitnessData_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → Nonempty (UnfWit U) := by
  first | exact @GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf | exact GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf | (intros; apply GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix ComplexConjugate

namespace GlobalTheory.RiemMaj

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def pc (x : Frame X.Ψ r) (v : Fin r → E) (t : X.Ψ × Fin r) : ℂ :=
  if (t.2 : ℕ) < X.p0 then hermC t.1.1 X.Gm (col (mat x t.1) t.2) (Data.emb t.1.1 v)
  else ((mat x t.1)⁻¹ *ᵥ Data.emb t.1.1 v) t.2

theorem re_xi (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
  have := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at this
  linarith

theorem norm_dmin_ortho {y : Frame X.Ψ r} (ho : X.IsOrtho y) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = 1 := by
  unfold dmin lminor
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, sgn]
  split_ifs <;> simp

theorem hermForm_diag {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) (s : X.Ψ → ℝ) (p q : X.Ψ × Fin r → ℂ) :
    hermForm (Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) (fun j => p (idx j)) (fun j => q (idx j)) =
      ∑ τ, (s τ : ℂ) * ∑ a, p (τ, a) * conj (q (τ, a)) := by
  have : hermForm (Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) (fun j => p (idx j)) (fun j => q (idx j)) =
      ∑ t : X.Ψ × Fin r, (s t.1 : ℂ) * (p t * conj (q t)) := by
    rw [hermForm, dotProduct]
    refine Fintype.sum_equiv idx _ _ fun k => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply]
    simp only [RCLike.star_def]
    ring
  rw [this, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

theorem im_diag {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {y : Frame X.Ψ r} (ho : X.IsOrtho y) (v w : Fin r → E) :
    (hermForm (Matrix.diagonal fun j => ((-2 * ((idx j).1.1 X.ξ0).im : ℝ) : ℂ)) (fun j => pc X y v (idx j))
      (fun j => pc X y w (idx j))).im = ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v w) : ℚ) : ℝ) := by
  rw [hermForm_diag X idx (fun τ => -2 * (τ.1 X.ξ0).im), UnitFrame.trace_eq_sum_re X.Ψ X.cmType, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pc]
  rw [Complex.im_ofReal_mul, UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat y τ) (ho τ)]
  have h3 : τ.1 (herm X.Gm v w) = hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w) := by
    simp [FD.hermC, FD.herm, FD.Data.emb, FD.cc, IsCMField.complexEmbedding_complexConj]
  rw [map_mul, map_neg, h3, Complex.mul_re, Complex.neg_re, Complex.neg_im, re_xi]
  ring

theorem maj_eq {y : Frame X.Ψ r} (hdet : ∀ τ, (mat y τ).det ≠ 0) (ho : X.IsOrtho y) (v : Fin r → E) (τ : X.Ψ) :
    (∑ a, pc X y v (τ, a) * conj (pc X y v (τ, a))).re = X.maj y τ (Data.emb τ.1 v) := by
  set u := (mat y τ)⁻¹ *ᵥ Data.emb τ.1 v with hu
  have h1 : Data.emb τ.1 v = mat y τ *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet τ)), Matrix.one_mulVec]
  conv_rhs => rw [h1]
  rw [UnipMove.GraphH.maj_ortho X ho, OrthonormalChartBounds.nsq, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  congr 1
  simp only [pc]
  split_ifs with ha
  · have hcol : col (mat y τ) a = mat y τ *ᵥ Pi.single a 1 := by
      ext k; simp [FD.col]
    rw [hcol, h1, UnitFrame.hermC_mulVec, ho τ]
    simp [Matrix.mulVec_diagonal, FD.sgn, ha]
  · rfl

theorem core {x : Frame X.Ψ r} (hx : x ∈ X.dom) {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {L : Type}
    (φ : L → Fin r → E) (P : L → Fin g → ℂ) (hP : ∀ a j, P a j = pc X x (φ a) (idx j))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (him : ∀ a b, (hermForm Hm (P a) (P b)).im = ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a) (φ b)) : ℚ) : ℝ)) :
    (∀ a, (hermForm Hm (P a) (P a)).re = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (φ a))) ∧
    (0 < r → X.κ0 = 2 * X.ξ0) ∧
    ∀ j, X.c (idx j).1 * (if ((idx j).2 : ℕ) < X.p0 then
      ‖dmin X.Gm x (idx j).1 (idx j).2.succ / dmin X.Gm x (idx j).1 (idx j).2.castSucc‖⁻¹
      else ‖dmin X.Gm x (idx j).1 (idx j).2.succ / dmin X.Gm x (idx j).1 (idx j).2.castSucc‖) ≤ (Hm j j).re := by
  classical
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  set b := FrameDegreeData.bOf X x
  have hy : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb
  set N := PerBor.moveMat X.p0 idx b with hN
  have hmove : ∀ a, (fun j => pc X (rmul x b) (φ a) (idx j)) = N *ᵥ P a := fun a =>
    PerBor.moveMat_mulVec X.p0 idx hb X.Gm x (φ a) _ _ (hP a) (fun _ => rfl)
  let s : X.Ψ → ℝ := fun τ => -2 * (τ.1 X.ξ0).im
  have key : Hm = Nᵀ * ((Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) * N.map (starRingEnd ℂ)) := by
    refine UnitDet.eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [him, ← UnitDet.hermForm_mulVec, ← hmove, ← hmove]
    exact (im_diag X idx ho _ _).symm
  have hdiag : ∀ j, (Hm j j).re = ∑ k, s (idx k).1 * ‖N k j‖ ^ 2 := by
    intro j
    rw [key, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.map_apply, mul_left_comm, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hκ : 0 < r → X.κ0 = 2 * X.ξ0 := by
    intro hr
    refine X.κ0_xi.resolve_right fun h => ?_
    have hs : ∀ τ, s τ < 0 := fun τ => by
      have := X.κ0_sign τ
      rw [h, map_neg, map_mul, map_ofNat] at this
      simp at this
      simp only [s]
      linarith
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ⟩ : Nonempty X.Ψ := by
      by_cases h0 : τ0 ∈ X.Ψ
      · exact ⟨⟨_, h0⟩⟩
      · by_contra hn
        exact h0 ((X.cmType τ0).2 fun h' => hn ⟨⟨_, h'⟩⟩)
    let j := idx.symm (τ, ⟨0, hr⟩)
    have h1 := hpos (Pi.single j 1) (by simp)
    have h2 : hermForm Hm (Pi.single j 1) (Pi.single j 1) = Hm j j := by simp [hermForm]
    rw [h2, hdiag] at h1
    exact absurd h1 (not_lt.2 (Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonpos_of_nonneg (hs _).le (sq_nonneg _)))
  have hsc : 0 < r → ∀ τ, s τ = X.c τ := by
    intro hr τ
    have := X.κ0_sign τ
    rw [hκ hr, map_mul, map_ofNat] at this
    simp at this
    simp only [s, Data.c]
    rw [← Complex.abs_im_eq_norm.mpr (re_xi X τ.1), abs_of_neg (by linarith)]
    ring
  refine ⟨fun a => ?_, hκ, fun j => ?_⟩
  · rw [key, ← UnitDet.hermForm_mulVec, ← hmove, hermForm_diag X idx s, Complex.re_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Complex.re_ofReal_mul, maj_eq X (fun τ => (hy τ).1) ho, MajInv.maj_rmul X hx hb]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : X.maj x τ (Data.emb τ.1 (φ a)) = 0 := by
        rw [← MajInv.maj_rmul X hx hb, ← maj_eq X (fun τ => (hy τ).1) ho]
        simp
      rw [this, mul_zero, mul_zero]
    · rw [hsc hr]
  · have hr : 0 < r := (idx j).2.pos
    have hc : ∀ τ, 0 ≤ X.c τ := fun τ => by unfold Data.c; positivity
    rw [hdiag]
    simp only [hsc hr]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun k => X.c (idx k).1 * ‖N k j‖ ^ 2)
      (fun k _ => mul_nonneg (hc _) (sq_nonneg _)) (Finset.mem_univ j))
    congr 1
    have h1 := FrameDegreeData.ratio_rmul X x hx hb (idx j).1 (idx j).2
    rw [norm_div, norm_dmin_ortho X ho, norm_dmin_ortho X ho, div_one] at h1
    rw [hN, PerBor.moveMat_diag _ _ hb]
    split_ifs
    · exact (eq_inv_of_mul_eq_one_left h1.symm).symm
    · rw [norm_inv, inv_pow]
      exact eq_inv_of_mul_eq_one_right h1.symm

end Core

theorem riemann_eq_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → (∀ v, (hermForm Hm (Uw.Pm k x v) (Uw.Pm k x v)).re = ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k v : Fin r → E))) ∧ (0 < r → (U.X k).κ0 = 2 * (U.X k).ξ0) ∧ ∀ (xi : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → (lieFac Dw xi a' * (U.X k).nfac (laU U a' 0 k) x.1)⁻¹ ≤ ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k x Hm hG hU hR
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper : ∀ v s, perFr (U.X k) x.1 v (relab c σ s.1) s.2 = pc (U.X k) x.1 v (f s) := by
    intro v s
    have h := hf s
    generalize f s = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    unfold pc
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by simp)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by dsimp only; omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ s.1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  obtain ⟨h1, h2, h3⟩ := core (U.X k) x.2 (Uw.e.trans f) (fun a => (Uw.φ k a : Fin r → E)) (Uw.Pm k x)
    (fun a j => by rw [Uw.Pm_eq, hper]; rfl) (Uw.period k x).2.2.2.1 Hm hR.2.1
    (fun a b => by rw [hR.2.2, ← Uw.iso]; simp)
  refine ⟨h1, h2, fun xi a' hxi => ?_⟩
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hxi0 : 0 < xi := by
    rw [← hxi τ0]
    exact norm_pos_iff.2 ((map_ne_zero τ0).2 (U.X k).ξ0_ne)
  have hpi : 0 < 2 * Real.pi * xi := by positivity
  have e1 : (lieFac Dw xi a')⁻¹ =
      ∏ s : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (2 * Real.pi * xi) ^ ((a' (s.1, (s.2 : ℕ)) : ℝ) / 2) := by
    rw [← Real.rpow_sum_of_pos hpi, Real.rpow_def_of_pos hpi, lieFac, ← Real.exp_neg, ← Finset.sum_div,
      Fintype.sum_sigma]
    congr 1
    ring
  rw [mul_inv, e1, Data.nfac, ← Fintype.prod_prod_type', ← f.prod_comp, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Fintype.prod_sigma']
  refine Finset.prod_le_prod₀ (fun s _ => by positivity) fun s _ => ?_
  have h4 := h3 (Uw.e.symm s)
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h4
  have hinv := Function.leftInverse_invFun hbij.1 s.1
  have hc : (U.X k).c (f s).1 = 2 * xi := by rw [Data.c, hxi]
  rw [hc] at h4
  set ρ := ‖dmin (U.X k).Gm x.1 (f s).1 (f s).2.succ / dmin (U.X k).Gm x.1 (f s).1 (f s).2.castSucc‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have e2 : (ρ ^ (-(laU U a' 0 k (f s).1 (f s).2 : ℝ) / 2))⁻¹ =
      (if ((f s).2 : ℕ) < (U.X k).p0 then ρ⁻¹ else ρ) ^ ((a' (s.1, (s.2 : ℕ)) : ℝ) / 2) := by
    unfold laU
    rcases hf s with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_pos (by omega), if_neg (by omega), b, hinv, show ((f s).2 : ℕ) - (U.X k).p0 = s.2 by omega,
        neg_div, Real.rpow_neg hρ0, inv_inv]
      simp
    · have t : conjEmb (f s).1.1 = relab c σ s.1 := by
        rw [b]; exact ComplexEmbedding.involutive_conjugate E _
      rw [if_neg (by omega), if_pos (by omega), t, hinv,
        show (U.X k).p0 - 1 - ((f s).2 : ℕ) = s.2 by omega, Real.inv_rpow hρ0]
      simp
  have hρ1 : 0 ≤ (if ((f s).2 : ℕ) < (U.X k).p0 then ρ⁻¹ else ρ) := by split_ifs <;> positivity
  rw [e2, ← Real.mul_rpow hpi.le hρ1]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  have := mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
  calc _ = _ := by ring
    _ ≤ _ := this

end GlobalTheory.RiemMaj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorantStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_frame_periods_eq_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → (∀ v, (hermForm Hm (Uw.Pm k x v) (Uw.Pm k x v)).re = ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k v : Fin r → E))) ∧ (0 < r → (U.X k).κ0 = 2 * (U.X k).ξ0) ∧ ∀ (xi : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → (lieFac Dw xi a' * (U.X k).nfac (laU U a' 0 k) x.1)⁻¹ ≤ ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  first | exact @GlobalTheory.RiemMaj.riemann_eq_majorant | exact GlobalTheory.RiemMaj.riemann_eq_majorant | (intros; apply GlobalTheory.RiemMaj.riemann_eq_majorant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem holArc_nilpotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ nn : (Fu.Di Ha.i).La →ₗ[𝓞 E] (Fu.Di Ha.i).La, (∀ v, Ha.N v = Ha.P₀ (nn v)) ∧ (∀ v v', -(Fu.Di Ha.i).EF (nn v) v' = a.be (Ha.y v) (Ha.y v')) ∧ (∀ v, Ha.y (nn v) = 0) ∧ (∀ v, Ha.y v = 0 → nn v = 0) ∧ (∀ t, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF t v' = 0) → Ha.y t = 0) ∧ ∀ ξ : Module.Dual ℤ a.D₀.X, ∃! t, ∀ v', -(Fu.Di Ha.i).EF t v' = ξ (Ha.y v') := by
  intro E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha
  letI := GlobalTheory.TorusExt.gtGroup a.D₀ ℂ
  have hadj := (Fu.Di Ha.i).adj
  have hb := (Fu.Di Ha.i).unimod
  have hle : ∀ t, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF t v' = 0) → Ha.y t = 0 := fun t ht => ((Ha.riemann t).1 ht).1
  let n := GlobalTheory.KerPerp.nilTo (bar := fun x => H.bar x) hadj hb Ha.y_onto a.be_adj
  have hn : ∀ v v', -(Fu.Di Ha.i).EF (n v) v' = a.be (Ha.y v) (Ha.y v') :=
    GlobalTheory.KerPerp.neg_apply_nilTo (bar := fun x => H.bar x) hadj hb Ha.y_onto a.be_adj
  refine ⟨(Submodule.subtype _).comp n, fun v => ?_, hn, fun v => hle _ (n v).2, fun v hv => ?_, hle, fun ξ => ?_⟩
  · let ex : (Fin g → ℂ) →+ Out.GtPtF a.D₀ ℂ :=
      AddMonoidHom.mk' Ha.ex₀ fun z z' => (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 (Ha.add z z')
    have hO : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
    have hfin := (Fu.Di Ha.i).fin
    have hL : Countable (Fu.Di Ha.i).La := Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
    rw [← sub_eq_zero]
    refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (Set.countable_range Ha.P₀) fun s => ?_
    obtain ⟨x, hx, hx'⟩ := ((Ha.riemann (n v)).1 (n v).2).2 s
    have hxe : x = fun z => eTwoPi (s * a.be (Ha.y v) z) := funext fun z => by
      obtain ⟨v', rfl⟩ := Ha.y_onto z
      rw [hx', ← hn]
      congr 1
      push_cast
      ring
    subst hxe
    have he : ex (s • Ha.N v) = ex (s • Ha.P₀ (n v)) :=
      GlobalTheory.TorusExt.IsTorusPtF.unique ((GlobalTheory.TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (Ha.shift s v))
        ((GlobalTheory.TorusExt.isTorusPtF_iff_isTorusPt _ _).2 hx)
    have h0 : ex (s • (Ha.N v - Ha.P₀ (n v))) = 0 := by rw [smul_sub, map_sub, he, sub_self]
    obtain ⟨u, -, hu⟩ := (Ha.ker _).1 ((GlobalTheory.TorusExt.isZero_iff_eq _).2 h0)
    exact ⟨u, hu.symm⟩
  · exact GlobalTheory.KerPerp.nil_eq_zero (nn := fun v => (n v : (Fu.Di Ha.i).La)) hb.1 hn hv
  · obtain ⟨t, -, ht⟩ := GlobalTheory.KerPerp.exists_of_dual (bar := fun x => H.bar x) (hadj := hadj) (y := Ha.y) hb.2 ξ
    exact ⟨t, ht, fun t' ht' => hb.1 (LinearMap.ext fun v => neg_injective ((ht' v).trans (ht v).symm))⟩

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem _root_.GlobalTheory.ArcQ.pairE_properties : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X), (∀ (a : 𝓞 E) x, _root_.GlobalTheory.ArcQ.pairE ξ (a • x) = (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x) ∧ (∀ x y, _root_.GlobalTheory.ArcQ.pairE ξ (x + y) = _root_.GlobalTheory.ArcQ.pairE (E := E) ξ x + _root_.GlobalTheory.ArcQ.pairE ξ y) ∧ (∀ x, Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x) = ξ x) ∧ (∀ x, IsIntegral ℤ ((NumberField.discr E : E) * _root_.GlobalTheory.ArcQ.pairE ξ x)) ∧ ∀ (K : Type) [Field K] (τK : E →+* K) x, _root_.GlobalTheory.ArcQ.xiVal τK ξ x = τK (_root_.GlobalTheory.ArcQ.pairE ξ x) := by
  intro E _ _ X _ _ ξ
  classical
  set b := RingOfIntegers.basis E with hbdef
  have hB := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hB (integralBasis E) with hd
  have hP : ∀ x, _root_.GlobalTheory.ArcQ.pairE ξ x = ∑ i, d i * (ξ (b i • x) : E) := fun x => rfl
  have hexp : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = ∑ k, (b.repr y k : E) * integralBasis E k := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    simp [integralBasis_apply, zsmul_eq_mul, b]
  have hdual : ∀ i k, Algebra.trace ℚ E (d i * integralBasis E k) = if k = i then 1 else 0 := by
    intro i k
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left hB _ i k
  have hL : ∀ (y : 𝓞 E) i, Algebra.trace ℚ E (d i * algebraMap (𝓞 E) E y) = (b.repr y i : ℚ) := by
    intro y i
    have e : ∀ k, d i * ((b.repr y k : E) * integralBasis E k) =
        (b.repr y k : ℚ) • (d i * integralBasis E k) := by
      intro k
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hexp y, Finset.mul_sum, map_sum]
    simp_rw [e, map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hC : ∀ x (y : 𝓞 E), Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E y) =
      (ξ (y • x) : ℚ) := by
    intro x y
    have e : ∀ i, d i * (ξ (b i • x) : E) * algebraMap (𝓞 E) E y =
        (ξ (b i • x) : ℚ) • (d i * algebraMap (𝓞 E) E y) := by
      intro i
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, Finset.sum_mul, map_sum]
    simp_rw [e, map_smul, hL, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_smul, map_sum, smul_assoc, map_zsmul, smul_eq_mul, Int.cast_sum,
      Int.cast_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have huniq : ∀ y y' : E, (∀ k, Algebra.trace ℚ E (y * integralBasis E k) =
      Algebra.trace ℚ E (y' * integralBasis E k)) → y = y' := by
    intro y y' h
    rw [← d.sum_repr y, ← d.sum_repr y']
    simp_rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    apply huniq
    intro k
    have e : (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x * integralBasis E k =
        _root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E (b k * a) := by
      rw [integralBasis_apply, map_mul]
      show (algebraMap (𝓞 E) E a) * _ * _ = _
      ring
    rw [e, hC, integralBasis_apply, hC, mul_smul]
  · intro x y
    simp only [hP, smul_add, map_add (f := _), Int.cast_add, mul_add, Finset.sum_add_distrib]
  · intro x
    have := hC x 1
    simpa using this
  · intro x
    rw [hP, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    have hdi : IsIntegral ℤ ((NumberField.discr E : E) * d i) := by
      have h := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
        (1 : Submodule (𝓞 E) E) (b := integralBasis E)
        (fun k => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
        (a := 1) (x := d i) (Submodule.one_le.1 le_rfl) (by
          rw [Submodule.mem_traceDual]
          intro a ha
          obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
          rw [Algebra.traceForm_apply, hL]
          exact ⟨b.repr y i, rfl⟩)
      rw [← coe_discr, Algebra.smul_def, mul_one] at h
      simpa using h
    have hξ : IsIntegral ℤ ((ξ (b i • x) : ℤ) : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ξ (b i • x)))
    rw [← mul_assoc]
    exact hdi.mul hξ
  · intro K _ τK x
    show ∑ i, τK (d i) * (ξ (b i • x) : K) = τK (_root_.GlobalTheory.ArcQ.pairE ξ x)
    rw [hP]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_intCast]

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

section Val

variable {A : Type} [CommRing A] {X Y : Scheme.{0}}

variable {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}

theorem valR_of_corr (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (e : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (h : LB.Gen.Corr L φ ε φ' ε t t')
    (x : Sp A ⟶ Y) (j : K → L.ι) :
    valR x (LB.wchart L φ j) (t.s j).val = valR x (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  rw [TorusCoord.gen_eq_of_corr hL ht ht' h]

theorem top_le_wchart_iff {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    ⊤ ≤ LB.wchart L (fun k => h ≫ φ k) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j :=
  ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
    fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩

theorem valR_pullGen (φ : K → (Y ⟶ X)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Sp A ⟶ Y) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j).val =
      valR h (LB.wchart L φ j) (t.s j).val := by
  by_cases H : ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j
  · have H' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := (top_le_wchart_iff φ h j).2 H
    refine (HolHom.valR_res (𝟙 (Sp A)) _ _ H').trans ?_
    exact (HolHom.valR_comp (𝟙 (Sp A)) h _ _).symm.trans (by rw [Category.id_comp]; rfl)
  · have H' : ¬ ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun H' => H ((top_le_wchart_iff φ h j).1 H')
    exact (dif_neg H').trans (Eq.symm (show valR h (LB.wchart L φ j) (t.s j).val = 0 from dif_neg H))

end Val

section Pull

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

theorem gtφT_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) :
    Out.DegPre.gtφT D T' b' χ = fun k => h ≫ Out.DegPre.gtφT D T b χ k := by
  funext k
  rw [TorusCoord.gtφT_eq, ← Category.id_comp (D.Oφ b' χ k)]
  exact ((TorusCoord.comp_eq_of_left b b' h (𝟙 _) (by rw [Category.id_comp, e])).1 χ k).symm

theorem top_le_wchart_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D T' b' χ) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D T b χ) j := by
  rw [gtφT_pull e, top_le_wchart_iff]

theorem valR_of_isPull {A : Type} [CommRing A] {p : Sp A ⟶ Sp R} {T : Over (Sp R)} {g : Out.GtPt D T}
    {g' : Out.GtPt D (Over.mk p)} {h : Sp A ⟶ T.left} (H : Out.GtPt.IsPull (T' := Over.mk p) h g g') (χ : D.X)
    (j : Fin 4 → D.P.L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart D.P.L (Out.DegPre.gtφT D (Over.mk p) g'.b χ) j) ((g'.s χ).s j).val =
      valR h (LB.wchart D.P.L (Out.DegPre.gtφT D T g.b χ) j) ((g.s χ).s j).val :=
  (valR_of_corr D.P.isLB (gtφT_pull H.1 χ) (g'.isGen χ) (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) (H.2 χ) _ j).trans
    (valR_pullGen _ _ h j)

end Pull

section Ex

variable [Algebra (FractionRing ℂ) ℂ] {D : Out.DegPre ℂ} {g : ℕ} {ex : (Fin g → ℂ) → Out.GtPtF D ℂ}

theorem b_add (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (z z' : Fin g → ℂ) :
    (ex (z + z')).b = (ex z).b * (ex z').b := (h z z').1

theorem b_zero (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) : (ex 0).b = 1 := by
  have := b_add h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem b_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (n : ℕ) (z : Fin g → ℂ) :
    (ex ((n : ℂ) • z)).b = (ex z).b ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, b_zero h]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, b_add h, ih, pow_succ]

theorem top_le_wchart_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) {n : ℕ} {b₀ : D.P.A ⟶ D.P.A}
    (hb : b₀ = 𝟙 D.P.A ^ n) (z : Fin g → ℂ) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b χ) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A b₀ χ) j :=
  top_le_wchart_pull (T' := Out.TF (R := ℂ) ℂ) (h := (ex z).b.left) (by
    rw [b_nsmul h, hb, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]) χ j

theorem tf_hom [IsScalarTower ℂ (FractionRing ℂ) ℂ] : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

def IsRatio (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (n : ℕ) (s₀ : Out.GtPt D D.P.A) (u : D.X → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ x z j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j →
    chiVal (ex ((n : ℂ) • z)) x j = u x z * valAt' (show Sp ℂ ⟶ _ from (ex z).b.left)
      (LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A s₀.b x) j) ((s₀.s x).s j).val

end Ex

end GlobalTheory.AbelianLetters
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Specialise

open GlobalTheory.Points GlobalTheory.AmpleSpan

section Coords

variable {A : Type} [CommRing A] {X Y : Scheme.{0}} {H : LB X} {ι : Type*} {t : ι → LB.Sec H}
  {x : Sp A ⟶ X} {c : ι → A}

def HasCoords (x : Sp A ⟶ X) (t : ι → LB.Sec H) (c : ι → A) : Prop :=
  ∃ k, ⊤ ≤ x ⁻¹ᵁ H.U k ∧ ∃ u : Aˣ, ∀ l, valR x (H.U k) ((t l).f k) = c l * u

theorem le_preimage_inf (x : Sp A ⟶ X) {U V : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem valR_compat (s : LB.Sec H) (x : Sp A ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j) (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valR x (H.U j) (s.f j) = valR x (H.U j ⊓ H.U k) (H.g j k).val * valR x (H.U k) (s.f k) := by
  have h := le_preimage_inf x hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem HasCoords.chart (h : HasCoords x t c) {j : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j) :
    ∃ u : Aˣ, ∀ l, valR x (H.U j) ((t l).f j) = c l * u := by
  obtain ⟨k, hk, u, hu⟩ := h
  have hg : IsUnit (valR x (H.U j ⊓ H.U k) (H.g j k).val) := by
    rw [valR_eq x _ (le_preimage_inf x hj hk)]
    exact (Units.isUnit _).map _
  refine ⟨hg.unit * u, fun l => ?_⟩
  rw [valR_compat (t l) x hj hk, hu, Units.val_mul, IsUnit.unit_spec, mul_left_comm]

theorem HasCoords.mul_unit (h : HasCoords x t c) {a : A} (ha : IsUnit a) : HasCoords x t fun l => c l * a := by
  obtain ⟨k, hk, u, hu⟩ := h
  obtain ⟨a, rfl⟩ := ha
  exact ⟨k, hk, a⁻¹ * u, fun l => by rw [hu, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]⟩

theorem HasCoords.le_nonzeroLocus (h : HasCoords x t c) {l : ι} (hl : IsUnit (c l)) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t l) := by
  obtain ⟨k, hk, u, hu⟩ := h
  refine le_preimage_mono x (le_iSup (fun k => X.basicOpen ((t l).f k)) k) ?_
  rw [le_preimage_basicOpen_iff x hk, hu]
  exact hl.mul u.isUnit

theorem valR_isRatio {s s₀ : LB.Sec H} {ρ : Γ(X, nonzeroLocus s₀)} (hρ : IsRatio s s₀ ρ) (x : Sp A ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s₀) {k : H.ι} (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valR x (H.U k) (s.f k) = valR x (nonzeroLocus s₀) ρ * valR x (H.U k) (s₀.f k) := by
  have h := le_preimage_inf x hx hk
  have e := congrArg (valR x (nonzeroLocus s₀ ⊓ H.U k)) (hρ k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h, valR_res x _ h] at e

theorem HasCoords.valR_ratio (h : HasCoords x t c) {l m : ι} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t m))
    {ρ : Γ(X, nonzeroLocus (t m))} (hρ : IsRatio (t l) (t m) ρ) : valR x (nonzeroLocus (t m)) ρ * c m = c l := by
  obtain ⟨k, hk, u, hu⟩ := h
  have e := valR_isRatio hρ x hx hk
  rw [hu, hu, ← mul_assoc] at e
  exact (u.mul_left_inj.1 e).symm

theorem exists_chart_isUnit [IsLocalRing A] {s : LB.Sec H} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s) :
    ∃ k, ⊤ ≤ x ⁻¹ᵁ H.U k ∧ IsUnit (valR x (H.U k) (s.f k)) := by
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ((le_preimage_iff x _).1 hx)
  have hk' := (le_preimage_iff x _).2 hk
  have hU := le_preimage_mono x (X.basicOpen_le _) hk'
  exact ⟨k, hU, (le_preimage_basicOpen_iff x hU _).1 hk'⟩

theorem HasCoords.le_nonzeroLocus_iff [IsLocalRing A] (h : HasCoords x t c) (l : ι) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t l) ↔ IsUnit (c l) := by
  refine ⟨fun hx => ?_, h.le_nonzeroLocus⟩
  obtain ⟨k, hk, hu⟩ := exists_chart_isUnit hx
  obtain ⟨u, e⟩ := h.chart hk
  rw [e] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem HasCoords.exists_isUnit [IsLocalRing A] (h : HasCoords x t c) (hcov : ⨆ l, nonzeroLocus (t l) = ⊤) :
    ∃ l, IsUnit (c l) := by
  obtain ⟨l, hl⟩ := exists_le_preimage_of_iSup_eq_top x hcov
  exact ⟨l, (h.le_nonzeroLocus_iff l).1 hl⟩

theorem hasCoords_ratio [IsLocalRing A] {m : ι} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t m))
    {ρ : ι → Γ(X, nonzeroLocus (t m))} (hρ : ∀ l, IsRatio (t l) (t m) (ρ l)) :
    HasCoords x t fun l => valR x (nonzeroLocus (t m)) (ρ l) := by
  obtain ⟨k, hk, hu⟩ := exists_chart_isUnit hx
  exact ⟨k, hk, hu.unit, fun l => valR_isRatio (hρ l) x hx hk⟩

theorem valR_eval₂Hom (f : X ⟶ Y) (x : Sp A ⟶ X) {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) (ρ : ι → Γ(X, U))
    (q : MvPolynomial ι Γ(Y, ⊤)) :
    valR x U (MvPolynomial.eval₂Hom (f.appLE ⊤ U le_top).hom ρ q) =
      MvPolynomial.eval₂Hom (valMap (x ≫ f) ⊤ (le_preimage_top _)).hom (fun l => valR x U (ρ l)) q := by
  rw [valR_eq x U hx, MvPolynomial.map_eval₂Hom, ← appLE_valMap x f (U := ⊤) le_top hx]
  simp only [valR_eq x U hx]
  rfl

end Coords

section Embedded

variable {A : Type} [CommRing A] {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {ι : Type} {t : ι → LB.Sec H}

theorem HasCoords.ext (ht : EmbedsBy f t) {x x' : Sp A ⟶ X} (hf : x ≫ f = x' ≫ f) {c : ι → A}
    (h : HasCoords x t c) (h' : HasCoords x' t c) {m : ι} (hm : IsUnit (c m)) : x = x' := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus hm
  have hx' := h'.le_nonzeroLocus hm
  refine ext_of_valR hD hx hx' fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  rw [valR_eval₂Hom f x hx, valR_eval₂Hom f x' hx']
  have e : (fun l => valR x _ (ρ l)) = fun l => valR x' _ (ρ l) := funext fun l =>
    hm.mul_right_cancel ((h.valR_ratio hx (hρ l)).trans (h'.valR_ratio hx' (hρ l)).symm)
  rw [e]
  simp only [hf]

theorem HasCoords.ext_of_isLocalRing [IsLocalRing A] (ht : EmbedsBy f t) {x x' : Sp A ⟶ X} (hf : x ≫ f = x' ≫ f)
    {c : ι → A} (h : HasCoords x t c) (h' : HasCoords x' t c) : x = x' := by
  obtain ⟨m, hm⟩ := h.exists_isUnit ht.1
  exact h.ext ht hf h' hm

variable {K : Type} [Field K] {j : A →+* K}

theorem isDominant_spMap (hj : Function.Injective j) : IsDominant (spMap j) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩

theorem ext_of_spMap_comp [IsSeparated f] (hj : Function.Injective j) {ξ ξ' : Sp A ⟶ X} (hf : ξ ≫ f = ξ' ≫ f)
    (h : spMap j ≫ ξ = spMap j ≫ ξ') : ξ = ξ' := by
  have := isDominant_spMap hj
  have : IsDomain A := hj.isDomain j
  exact ext_of_isDominant_of_isSeparated f hf (spMap j) h

theorem exists_lift_of_valR_mem (hj : Function.Injective j) {D : X.Opens} (hD : IsAffineOpen D) (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ D) (h : ∀ g, valR x D g ∈ j.range) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ D ∧ spMap j ≫ ξ = x := by
  choose φ hφ using h
  simp only [valR_eq x D hx] at hφ
  let ψ : Γ(X, D) →+* A := ⟨⟨⟨φ, hj (by simp [hφ])⟩, fun a b => hj (by simp [hφ])⟩, hj (by simp [hφ]),
    fun a b => hj (by simp [hφ])⟩
  refine ⟨_, le_preimage_specMap_fromSpec hD (CommRingCat.ofHom ψ), ?_⟩
  rw [← specMap_valMap_fromSpec hD x hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hφ)

theorem exists_lift [Y.IsSeparated] (ht : EmbedsBy f t) (hj : Function.Injective j) {b : Sp A ⟶ Y} {x : Sp K ⟶ X}
    (hb : x ≫ f = spMap j ≫ b) {c : ι → A} (h : HasCoords x t fun l => j (c l)) {m : ι} (hm : IsUnit (c m)) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus (t m) ∧ ξ ≫ f = b ∧ spMap j ≫ ξ = x := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus (hm.map j)
  obtain ⟨ξ, hξ, e⟩ := exists_lift_of_valR_mem hj hD x hx fun g => by
    obtain ⟨q, rfl⟩ := hsurj g
    rw [valR_eval₂Hom f x hx]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← valR_eq, hb, valR_spMap_comp j b ⊤ (le_preimage_top _)]
      exact ⟨_, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine mul_mem hp ⟨c l * hm.unit⁻¹.val, (hm.map j).mul_right_cancel ?_⟩
      rw [h.valR_ratio hx (hρ l), ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
  refine ⟨ξ, hξ, ext_of_spMap_comp (f := terminal.from Y) hj (terminal.hom_ext _ _) ?_, e⟩
  rw [← Category.assoc, e, hb]

end Embedded

section Rings

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K}

instance ker_isPrime (ev : R →+* C) : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev

end Rings

section Relation

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {X S : Scheme.{0}}

variable {hi : Function.Injective i} {ev : R →+* C} {p : X ⟶ S} {b : Sp R ⟶ S} {x : Sp K ⟶ X} {y : Sp C ⟶ X}

end Relation

section Existence

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {X S : Scheme.{0}} {p : X ⟶ S}
  {H : LB X} {ι : Type} {t : ι → LB.Sec H} {b : Sp R ⟶ S} {x : Sp K ⟶ X} {r : ι → R}

end Existence

section Group

open MonObj

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {S : Scheme.{0}} {A : Over S}
  {hi : Function.Injective i} {ev : R →+* C} {b : Sp R ⟶ S} {sK : Sp K ⟶ S} {sC : Sp C ⟶ S}

end Group

end GlobalTheory.Specialise
end
end

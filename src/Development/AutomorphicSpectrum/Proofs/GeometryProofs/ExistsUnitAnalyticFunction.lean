module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AnalyticTypeDefinition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FcHoloDetDifferentiableAt
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcHolo_det_differentiableAt {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype n] [DecidableEq n] (M : E → Matrix n n ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) x) :
    DifferentiableAt ℂ (fun b => (M b).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ s : Finset n, DifferentiableAt ℂ (fun b => ∏ i ∈ s, M b (σ i) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).fun_mul ih
  exact key _

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesAll
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesAll
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ), (∀ i, LinearIndependent (𝓞 E) (e i)) → ∃ Φ : CFn Xo c, ∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i) :=
  @PositivityTheory.Xgn.analytic_type_definition

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesAllStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_eigen_frames_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ), (∀ i, LinearIndependent (𝓞 E) (e i)) → ∃ Φ : CFn Xo c, ∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anDef | exact GlobalTheory.CompanionTheory.Ar.Flat.anDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anDef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameTwo
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameTwo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix GlobalTheory.CompanionTheory.Ar.LinFlat
open scoped ComplexOrder

theorem det_rows_mul_det_rows {p q : ℕ} (A C : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (F : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (hAF : A * Fᵀ = 0) (hAC : A * Cᵀ = 1) :
    (fromRows (Fᵀ)ᴴ A).det * (fromRows F C).det = ((Fᵀ)ᴴ * Fᵀ).det := by
  have h : fromRows (Fᵀ)ᴴ A * (fromRows F C)ᵀ = fromBlocks ((Fᵀ)ᴴ * Fᵀ) ((Fᵀ)ᴴ * Cᵀ) 0 1 := by
    rw [transpose_fromRows, fromRows_mul_fromCols, hAF, hAC]
  rw [← det_transpose (fromRows F C), ← det_mul, h, det_fromBlocks_zero₂₁]
  simp

theorem norm_core {p q g : ℕ} (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (U U' : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (hS : S.det ≠ 0)
    (hV : LinearIndependent ℂ V) (hW : LinearIndependent ℂ W)
    (hU : ∀ n, U n ∈ Submodule.span ℂ (Set.range V))
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hB : ∀ n, U' n = ∑ j, B j n • W j) (hFm : ∀ j n, ∑ m, Fm j m * S m n = B j n)
    (hC : ∀ a, ∑ m, C a m • U m = V a)
    (hR : ∀ m n, hermForm Hm (U m) (U n) - star (hermForm Hm (U' m) (U' n)) = 2 * Complex.I * S m n)
    (Γ : Matrix (Fin p) (Fin p) ℂ) (Δ : Matrix (Fin q) (Fin q) ℂ)
    (hΓ : ∀ a b, Γ a b = Real.pi * hermForm Hm (V a) (V b))
    (hΔ : ∀ a b, Δ a b = Real.pi * hermForm Hm (W a) (W b)) :
    ‖Γ.det‖ = ‖(fromRows C Fm).det‖ ^ 2 *
      ((2 * Real.pi) ^ p * (2 * Real.pi)⁻¹ ^ q * ‖S.det‖) * ‖Δ.det‖ := by
  choose a ha using fun n => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hU n)
  let A : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ := Matrix.of fun i n => a n i
  have hA : ∀ n, ∑ i, A i n • V i = U n := ha
  clear_value A
  set H₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun i j => hermForm Hm (V i) (V j) with hH₁
  set H₂ : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun i j => hermForm Hm (W i) (W j) with hH₂
  have pd₁ : H₁.PosDef := gram_posDef Hm hH hpos V hV
  have pd₂ : H₂.PosDef := gram_posDef Hm hH hpos W hW
  have hrel : Aᵀ * H₁ * A.map star - (Bᵀ * H₂ * B.map star)ᵀ = (2 * Complex.I) • S := by
    ext m n
    rw [Matrix.sub_apply, Matrix.transpose_apply, gram_expand, gram_expand, hA, hA, ← hB, ← hB,
      ← star_hermForm hH (U' m) (U' n), hR m n]
    simp
  let e : Fin q ⊕ Fin p ≃ Fin p ⊕ Fin q := Equiv.sumComm _ _
  have hrel' : (A.submatrix id e)ᵀ * H₁ * (A.submatrix id e).map star -
      ((B.submatrix id e)ᵀ * H₂ * (B.submatrix id e).map star)ᵀ =
      (2 * Complex.I) • S.submatrix e e := by
    ext m n
    have := congrFun (congrFun hrel (e m)) (e n)
    simpa [Matrix.mul_apply] using this
  have hdet : (S.submatrix e e).det ≠ 0 := by rwa [Matrix.det_submatrix_equiv_self]
  obtain ⟨t₁, -, -, t₄⟩ := GlobalTheory.T.riemann_form_period_determinant p q (A.submatrix id e) (B.submatrix id e)
    (S.submatrix e e) H₁ H₂ pd₁ pd₂ hdet hrel'
  have hFS : Fm * S = B := by
    ext j n
    rw [Matrix.mul_apply, hFm]
  have hN : ((S.submatrix e e)ᵀ)⁻¹ * (B.submatrix id e)ᵀ = (Fm.submatrix id e)ᵀ := by
    have h1 : B.submatrix id e = Fm.submatrix id e * S.submatrix e e := by
      rw [Matrix.submatrix_mul_equiv, hFS]
    have hu : IsUnit ((S.submatrix e e)ᵀ).det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
    rw [h1, Matrix.transpose_mul, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [hN] at t₁ t₄
  have hCA : C * Aᵀ = 1 := by
    ext i k
    have hexp : ∑ m, C i m • U m = ∑ k, (C * Aᵀ) i k • V k := by
      simp_rw [← hA, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_apply, Finset.sum_smul]
      rfl
    have := coef_unique hV (fun k => (C * Aᵀ) i k) (fun k => (1 : Matrix _ _ ℂ) i k)
      (by rw [← hexp, hC i]; simp [Matrix.one_apply])
    exact congrFun this k
  have hAC : A.submatrix id e * (C.submatrix id e)ᵀ = 1 := by
    have h1 : C.submatrix id e * (A.submatrix id e)ᵀ = 1 := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hCA]
      simp
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul] using this
  have hG : (fromRows (Fm.submatrix id e) (C.submatrix id e)).det = (fromRows C Fm).det := by
    have : fromRows (Fm.submatrix id e) (C.submatrix id e) = (fromRows C Fm).submatrix e e := by
      ext (i | i) n <;> simp [e]
    rw [this, Matrix.det_submatrix_equiv_self]
  have hmul := det_rows_mul_det_rows _ _ _ t₁ hAC
  rw [hG] at hmul
  set d := (fromRows C Fm).det with hd
  set X := (((Fm.submatrix id e)ᵀ)ᴴ * (Fm.submatrix id e)ᵀ).det with hX
  set M := (fromRows ((Fm.submatrix id e)ᵀ)ᴴ (A.submatrix id e)).det with hM
  have hSd : ‖(S.submatrix e e).det‖ = ‖S.det‖ := by rw [Matrix.det_submatrix_equiv_self]
  rw [hSd] at t₄
  have p₁ : 0 < H₁.det := pd₁.det_pos
  have p₂ : 0 < H₂.det := pd₂.det_pos
  have r₁ : 0 < H₁.det.re := (Complex.pos_iff.mp p₁).1
  have r₂ : 0 < H₂.det.re := (Complex.pos_iff.mp p₂).1
  have n₁ : ‖H₁.det‖ = H₁.det.re := by
    rw [← Complex.abs_re_eq_norm.mpr (Complex.pos_iff.mp p₁).2.symm, abs_of_pos r₁]
  have n₂ : ‖H₂.det‖ = H₂.det.re := by
    rw [← Complex.abs_re_eq_norm.mpr (Complex.pos_iff.mp p₂).2.symm, abs_of_pos r₂]
  have hSp : 0 < ‖S.det‖ := norm_pos_iff.mpr hS
  have hc : 0 < (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by positivity
  have hXne : X ≠ 0 := by
    intro h0
    rw [h0, div_zero, norm_zero] at t₄
    have h00 : (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re = 0 := by rw [← t₄]; simp
    exact hc.ne' h00
  have hdne : d ≠ 0 := fun h0 => hXne (by rw [← hmul, h0, mul_zero])
  have hq : M / X = d⁻¹ := by
    have hMne : M ≠ 0 := fun h0 => hXne (by rw [← hmul, h0, zero_mul])
    rw [← hmul]
    field_simp
  have hΓ' : Γ = (Real.pi : ℂ) • H₁ := by ext a b; simp [hΓ, hH₁]
  have hΔ' : Δ = (Real.pi : ℂ) • H₂ := by ext a b; simp [hΔ, hH₂]
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [hΓ', hΔ', Matrix.det_smul, Matrix.det_smul, norm_mul, norm_mul, norm_pow, norm_pow, hpi, n₁, n₂]
  simp only [Fintype.card_fin]
  rw [hq, norm_inv] at t₄
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have t₅ : H₁.det.re = ‖d‖ ^ 2 * (2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re) := by
    rw [← t₄]; field_simp
  rw [t₅, mul_pow, inv_pow, inv_pow, mul_pow]
  have := Real.pi_pos
  field_simp

theorem hodgeNorm_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La), LinearIndependent (𝓞 E) e → ∃ t : ℝ, 0 < t ∧ ∀ (ρ : ℂ) (Φ : CFn Xo c), IsFlatAn Set.univ τ τ' σ Φ FU i e ρ → ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ), IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖ρ‖ ^ 2 * t * ‖Δ.det‖ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ i e he
  let S : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))
  have hSne : ∀ P : (FU.Di i).La →+ (Fin g → ℂ), IsPeriod (FU.Di i) ty P → S.det ≠ 0 := by
    intro P hP
    obtain ⟨Hm, hHh, -, hHi⟩ := id hP.2.2.2.2
    obtain ⟨-, -, hd⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
    have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
      rw [(FU.sig i).1, (FU.sig i).2]; simp
    have := hd 0 _ e hcard he
    have h2 : S = (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  by_cases hS0 : S.det = 0
  · refine ⟨1, one_pos, ?_⟩
    intro ρ Φ _ P y v w Γ Δ hP
    exact absurd hS0 (hSne P hP)
  refine ⟨(2 * Real.pi) ^ D.p * (2 * Real.pi)⁻¹ ^ D.q * ‖S.det‖, ?_, ?_⟩
  · have := norm_pos_iff.mpr hS0
    have := Real.pi_pos
    positivity
  intro ρ Φ hΦ P y v w Γ Δ hP hy hfr hΓ hΔ
  obtain ⟨⟨V₀, W₀, Fm, B, d⟩, ⟨k1, k2, k3, k4, -, ⟨C, k6⟩, k7⟩, -⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hty hrt hτ i e P y v w he hP hy hfr
  simp only at k1 k2 k3 k4 k6 k7
  have hflat : Φ y v w * (Matrix.fromRows C Fm).det = ρ :=
    hΦ P y v w V₀ W₀ C Fm B hP hy hfr k1 k2 k6 k3 k4
  obtain ⟨-, -, hv, hw⟩ := id hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W, hWd, hWl, -⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  have eV : V₀ = V := funext fun a => (hVd a _).1 (k1 a)
  have eW : W₀ = W := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
  have hΓ' := (GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hHh hHi (under y) hy D.p v V₀ Γ k1).1 hΓ
  have hΔ' := (GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hHh hHi (under y) hy D.q w W₀ Δ k2).1 hΔ
  have hlin : IsLinearMap ℂ (tyPart ty τ') := by
    constructor
    · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
    · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp
  have hC : ∀ a, ∑ m, C a m • tyPart ty τ' (P (e m)) = V₀ a := by
    intro a
    rw [← k6 a]
    have := map_sum (hlin.mk' _) (fun m => C a m • P (e m)) Finset.univ
    simpa [hlin.map_smul] using this.symm
  have key := norm_core V₀ W₀ (fun n => tyPart ty τ' (P (e n)))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n))) S Hm hHh hHp hS0 hVl hWl
    (fun n => hVs _) C Fm B k3 k4 hC (fun m n => hs τ' _ _) Γ Δ hΓ' hΔ'
  rw [key, ← hflat, norm_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameTwoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_eigen_frame_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La), LinearIndependent (𝓞 E) e → ∃ t : ℝ, 0 < t ∧ ∀ (ρ : ℂ) (Φ : CFn Xo c), IsFlatAn Set.univ τ τ' σ Φ FU i e ρ → ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ), IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖ρ‖ ^ 2 * t * ‖Δ.det‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeNorm_flat | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeNorm_flat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeNorm_flat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesTwo
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesTwo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.AnHol

variable {m : ℕ}

theorem inv_differentiableAt {n : ℕ} (M : (Fin m → ℂ) → Matrix (Fin n) (Fin n) ℂ) (b₀ : Fin m → ℂ)
    (hM : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) b₀) (h0 : (M b₀).det ≠ 0) (i j : Fin n) :
    DifferentiableAt ℂ (fun b => (M b)⁻¹ i j) b₀ := by
  have hd := fcHolo_det_differentiableAt M b₀ hM
  refine GlobalTheory.HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (M b)⁻¹) M b₀ hM ?_ i j
  filter_upwards [hd.continuousAt.eventually_ne h0] with b hb
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hb)

theorem exists_rightInverse_of_li {r g : ℕ} (X : Fin r → Fin g → ℂ) (hX : LinearIndependent ℂ X) :
    ∃ N : Matrix (Fin g) (Fin r) ℂ, Matrix.of X * N = 1 := by
  classical
  have hr : (Matrix.of X).rank = r := by
    simpa using LinearIndependent.rank_matrix (M := Matrix.of X) hX
  have hs : Function.Surjective (Matrix.of X).mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hr
  choose c hc using fun a : Fin r => hs (Pi.single a 1)
  refine ⟨Matrix.of fun k a => c a k, ?_⟩
  ext a b
  have := congrFun (hc b) a
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem coef_differentiableAt {r g : ℕ} {κ : Type*}
    (X : (Fin m → ℂ) → Fin r → Fin g → ℂ) (Y : (Fin m → ℂ) → κ → Fin g → ℂ)
    (A : (Fin m → ℂ) → Matrix (Fin r) κ ℂ) (b₀ : Fin m → ℂ)
    (hX : ∀ i, DifferentiableAt ℂ (fun b => X b i) b₀) (hY : ∀ n, DifferentiableAt ℂ (fun b => Y b n) b₀)
    (hli : LinearIndependent ℂ (X b₀))
    (hA : ∀ᶠ b in 𝓝 b₀, ∀ n, Y b n = ∑ i, A b i n • X b i) (i : Fin r) (n : κ) :
    DifferentiableAt ℂ (fun b => A b i n) b₀ := by
  classical
  obtain ⟨N, hN⟩ := exists_rightInverse_of_li (X b₀) hli
  let G : (Fin m → ℂ) → Matrix (Fin r) (Fin r) ℂ := fun b => Matrix.of (X b) * N
  have hG : ∀ i j, DifferentiableAt ℂ (fun b => G b i j) b₀ := fun i j => by
    simp only [G, Matrix.mul_apply, Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_pi.1 (hX i) k).mul_const _
  have hG0 : (G b₀).det ≠ 0 := by simp [G, hN]
  have hdet := (fcHolo_det_differentiableAt G b₀ hG).continuousAt.eventually_ne hG0
  have hZ : ∀ j, DifferentiableAt ℂ (fun b => ∑ k, Y b n k * N k j) b₀ := fun j =>
    DifferentiableAt.fun_sum fun k _ => (differentiableAt_pi.1 (hY n) k).mul_const _
  have hI := inv_differentiableAt G b₀ hG hG0
  have hR : DifferentiableAt ℂ (fun b => ∑ j, (∑ k, Y b n k * N k j) * (G b)⁻¹ j i) b₀ :=
    DifferentiableAt.fun_sum fun j _ => (hZ j).mul (hI j i)
  refine hR.congr_of_eventuallyEq ?_
  filter_upwards [hA, hdet] with b hb hd
  have e1 : ∀ j, ∑ k, Y b n k * N k j = ∑ i', A b i' n * G b i' j := fun j => by
    simp only [hb n, G, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : G b * (G b)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)
  simp only [e1, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_assoc, ← Finset.mul_sum]
  have e3 : ∀ i', ∑ j, G b i' j * (G b)⁻¹ j i = (1 : Matrix (Fin r) (Fin r) ℂ) i' i := fun i' => by
    rw [← e2, Matrix.mul_apply]
  simp [e3, Matrix.one_apply]

theorem tyPart_differentiableAt {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ)
    (f : (Fin m → ℂ) → Fin g → ℂ) (b₀ : Fin m → ℂ) (hf : DifferentiableAt ℂ f b₀) :
    DifferentiableAt ℂ (fun b => tyPart ty τ (f b)) b₀ := by
  refine differentiableAt_pi.2 fun k => ?_
  by_cases h : ty k = τ
  · simpa [tyPart, h] using differentiableAt_pi.1 hf k
  · simp [tyPart, h]

theorem tyPart_sum_smul {E : Type} [Field E] {g : ℕ} {κ : Type*} [Fintype κ] (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ)
    (c : κ → ℂ) (z : κ → Fin g → ℂ) : tyPart ty τ (∑ m, c m • z m) = ∑ m, c m • tyPart ty τ (z m) := by
  funext k
  by_cases h : ty k = τ
  · simp [tyPart, h, Finset.sum_apply]
  · simp [tyPart, h, Finset.sum_apply]

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    GlobalTheory.CompanionTheory.Ar.dualMap φ = Chart.dualMapR φ := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, Chart.dualMapR]

end GlobalTheory.CompanionTheory.Ar.Flat.AnHol

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.AnHol in
theorem anHol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ) (Φ : CFn Xo c), (∀ i, LinearIndependent (𝓞 E) (e i)) → (∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i)) → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ)) (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B → (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) → (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧ (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧ ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) → DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ e ρ Φ he hflat R _ x vR wR m B ψ v w hB hψ hfr b₀ hb₀
  classical
  refine DifferentiableAt.differentiableWithinAt ?_
  have hev : ∀ t, DifferentiableAt ℂ (fun b => ψ b t) b₀ := fun t => (hψ t).differentiableAt (hB.mem_nhds hb₀)
  have h₁ : IsHolTo B (fun b => spMap (ψ b)) := GlobalTheory.ThetaValueCont.isHolTo_spMap hB ψ hψ
  have h₂ : IsHolTo B (fun b => spMap (ψ b) ≫ under x) :=
    GlobalTheory.HolHom.isHolTo_of_holAt hB fun z hz => (GlobalTheory.HolHom.holAt_of_isHolTo h₁ hz).comp _
  have hov : ∀ b ∈ B, (spMap (ψ b) ≫ under x) ≫ Xo.s =
      spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := fun b hb => by
    have h := (hfr b hb).1.1
    have h' := congrArg (· ≫ spMap (IntermediateField.inclusion c.le).toRingHom) h
    simp only [Category.assoc] at h'
    simp only [under, Category.assoc]
    rw [pullback.condition, h']
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ :=
    FU.lift m B (fun b => spMap (ψ b) ≫ under x) hB hov h₂ b₀ hb₀
  have hun : ∀ b ∈ B', under (spMap (ψ b) ≫ x) = FU.u i (P b) := fun b hb => by
    rw [hu b hb]; simp only [under, Category.assoc]
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a =
      ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  choose! xx hxx using fun b (hb : b ∈ B') =>
    (GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hty hrt hτ i (e i) (P b) _ (v b) (w b) (he i) (hP.1 b hb)
      (hun b hb) (hfr b (hsub hb)).1).exists
  have hVW : ∀ b ∈ B', LinearIndependent ℂ (xx b).1 ∧
      (∀ z, tyPart ty τ' z ∈ Submodule.span ℂ (Set.range (xx b).1)) ∧ LinearIndependent ℂ (xx b).2.1 := by
    intro b hb
    obtain ⟨-, -, hv, hw⟩ := (hfr b (hsub hb)).1
    obtain ⟨V, hVd, hVl, hVs⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i (P b) _
      (σ.comp (tauIn c τ)) τ' D.p (v b) (hP.1 b hb) (hun b hb) hτ hv
    obtain ⟨W, hWd, hWl, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i (P b) _
      _ (ComplexEmbedding.conjugate τ') D.q (w b) (hP.1 b hb) (hun b hb) hc hw
    have eV : (xx b).1 = V := funext fun a => (hVd a _).1 ((hxx b hb).1 a)
    have eW : (xx b).2.1 = W := funext fun a => (hWd a _).1 ((hxx b hb).2.1 a)
    rw [eV, eW]
    exact ⟨hVl, hVs, hWl⟩
  have hnb : ∀ᶠ b in 𝓝 b₀, b ∈ B' := hB'.mem_nhds hb'

  have hVd : ∀ a, DifferentiableAt ℂ (fun b => (xx b).1 a) b₀ := fun a =>
    GlobalTheory.HolFrameMatrix.differentiableAt_coord FU i (vR a).left ψ hB' hP (fun b => (xx b).1 a) (fun b hb => by
      have := (hxx b hb).1 a
      rw [(hfr b (hsub hb)).2.1 a, AnHol.dualMap_eq] at this
      exact this) hb' hev
  have hWd : ∀ a, DifferentiableAt ℂ (fun b => (xx b).2.1 a) b₀ := fun a =>
    GlobalTheory.HolFrameMatrix.differentiableAt_coord FU i (wR a).left ψ hB' hP (fun b => (xx b).2.1 a) (fun b hb => by
      have := (hxx b hb).2.1 a
      rw [(hfr b (hsub hb)).2.2 a, AnHol.dualMap_eq] at this
      exact this) hb' hev
  have hPd : ∀ n, DifferentiableAt ℂ (fun b => P b (e i n)) b₀ := fun n =>
    (hP.2 (e i n)).differentiableAt (hB'.mem_nhds hb')

  have hBd : ∀ j n, DifferentiableAt ℂ (fun b => (xx b).2.2.2.1 j n) b₀ := fun j n =>
    AnHol.coef_differentiableAt (fun b => (xx b).2.1)
      (fun b n => tyPart ty (ComplexEmbedding.conjugate τ') (P b (e i n))) (fun b => (xx b).2.2.2.1) b₀ hWd
      (fun n => AnHol.tyPart_differentiableAt ty _ _ b₀ (hPd n)) (hVW b₀ hb').2.2
      (by filter_upwards [hnb] with b hb n using (hxx b hb).2.2.1 n) j n
  obtain ⟨Hm, hHh, -, hHi⟩ := id (hP.1 b₀ hb').2.2.2.2
  obtain ⟨-, -, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty (P b₀) Hm (hP.1 b₀ hb') hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  let S : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m n => τ' (sesq (FU.Di i) (e i m) (e i n))
  have hS : S.det ≠ 0 := by
    have := hd 0 _ (e i) hcard (he i)
    have h2 : S = (Matrix.of fun m n => sesq (FU.Di i) (e i m) (e i n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hS
  have hFe : ∀ b ∈ B', (xx b).2.2.1 = (xx b).2.2.2.1 * S⁻¹ := fun b hb => by
    have : (xx b).2.2.1 * S = (xx b).2.2.2.1 := by
      ext j n
      rw [Matrix.mul_apply]
      exact (hxx b hb).2.2.2.1 j n
    rw [← this, Matrix.mul_nonsing_inv_cancel_right _ _ hSu]
  have hFd : ∀ j n, DifferentiableAt ℂ (fun b => (xx b).2.2.1 j n) b₀ := fun j n => by
    have : DifferentiableAt ℂ (fun b => ((xx b).2.2.2.1 * S⁻¹) j n) b₀ := by
      simp only [Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => (hBd j k).mul_const _
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hnb] with b hb
    rw [hFe b hb]

  choose! A hA using fun b (hb : b ∈ B') (n : Fin D.p ⊕ Fin D.q) =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 ((hVW b hb).2.1 (P b (e i n)))
  let Am : (Fin m → ℂ) → Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ := fun b => Matrix.of fun k n => A b n k
  have hAd : ∀ k n, DifferentiableAt ℂ (fun b => Am b k n) b₀ := fun k n =>
    AnHol.coef_differentiableAt (fun b => (xx b).1) (fun b n => tyPart ty τ' (P b (e i n))) Am b₀ hVd
      (fun n => AnHol.tyPart_differentiableAt ty _ _ b₀ (hPd n)) (hVW b₀ hb').1
      (by filter_upwards [hnb] with b hb n using (hA b hb n).symm) k n
  have hexp : ∀ b ∈ B', ∀ (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ) (a : Fin D.p),
      tyPart ty τ' (∑ m, C a m • P b (e i m)) = ∑ k, (Am b * C.transpose) k a • (xx b).1 k := by
    intro b hb C a
    rw [AnHol.tyPart_sum_smul]
    simp_rw [← hA b hb, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Am, mul_comm]
  obtain ⟨C₀, hC₀⟩ := (hxx b₀ hb').2.2.2.2.2.1
  have hM0 : Am b₀ * C₀.transpose = 1 := by
    ext k a
    have h1 := hexp b₀ hb' C₀ a
    rw [hC₀ a] at h1
    have h2 := Fintype.linearIndependent_iff.1 (hVW b₀ hb').1
      (fun k => (Am b₀ * C₀.transpose) k a - (1 : Matrix (Fin D.p) (Fin D.p) ℂ) k a)
      (by simp [sub_smul, Finset.sum_sub_distrib, ← h1, Matrix.one_apply]) k
    exact sub_eq_zero.1 h2
  let M : (Fin m → ℂ) → Matrix (Fin D.p) (Fin D.p) ℂ := fun b => Am b * C₀.transpose
  have hMd : ∀ k a, DifferentiableAt ℂ (fun b => M b k a) b₀ := fun k a => by
    simp only [M, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun n _ => (hAd k n).mul_const _
  have hM0' : (M b₀).det ≠ 0 := by simp [M, hM0]
  have hMe := (fcHolo_det_differentiableAt M b₀ hMd).continuousAt.eventually_ne hM0'
  have hMi := AnHol.inv_differentiableAt M b₀ hMd hM0'
  let Cb : (Fin m → ℂ) → Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ := fun b => (C₀.transpose * (M b)⁻¹).transpose
  have hCd : ∀ a n, DifferentiableAt ℂ (fun b => Cb b a n) b₀ := fun a n => by
    simp only [Cb, Matrix.transpose_apply, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (hMi k a).const_mul _
  have hlift : ∀ᶠ b in 𝓝 b₀, b ∈ B' ∧ ∀ a, tyPart ty τ' (∑ m, Cb b a m • P b (e i m)) = (xx b).1 a := by
    filter_upwards [hnb, hMe] with b hb hdet
    refine ⟨hb, fun a => ?_⟩
    have h1 : Am b * (Cb b).transpose = 1 := by
      simp only [Cb, Matrix.transpose_transpose]
      rw [← Matrix.mul_assoc]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [hexp b hb, h1]
    simp [Matrix.one_apply]

  let Dt : (Fin m → ℂ) → ℂ := fun b => (Matrix.fromRows (Cb b) (xx b).2.2.1).det
  have hDd : DifferentiableAt ℂ Dt b₀ := by
    refine fcHolo_det_differentiableAt (fun b => Matrix.fromRows (Cb b) (xx b).2.2.1) b₀ fun r n => ?_
    rcases r with r | r
    · simpa using hCd r n
    · simpa using hFd r n
  have hDe : ∀ᶠ b in 𝓝 b₀, b ∈ B' ∧ Dt b = (xx b).2.2.2.2 := by
    filter_upwards [hlift] with b hb
    exact ⟨hb.1, (hxx b hb.1).2.2.2.2.2.2 _ hb.2⟩
  have hD0 : Dt b₀ ≠ 0 := by
    rw [hDe.self_of_nhds.2]
    exact (hxx b₀ hb').2.2.2.2.1
  have hq : DifferentiableAt ℂ (fun b => ρ i / Dt b) b₀ := by
    simp only [div_eq_mul_inv]
    exact hDd.fun_inv hD0 |>.const_mul _
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hlift, hDe] with b hb hb'
  have hne : Dt b ≠ 0 := by
    rw [hb'.2]
    exact (hxx b hb.1).2.2.2.2.1
  have hfl := hflat i (P b) _ (v b) (w b) (xx b).1 (xx b).2.1 (Cb b) (xx b).2.2.1 (xx b).2.2.2.1 (hP.1 b hb.1)
    (hun b hb.1) (hfr b (hsub hb.1)).1 (hxx b hb.1).1 (hxx b hb.1).2.1 hb.2 (hxx b hb.1).2.2.1
    (hxx b hb.1).2.2.2.1
  rw [eq_div_iff hne]
  exact hfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesTwoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_eigen_frames_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ) (Φ : CFn Xo c), (∀ i, LinearIndependent (𝓞 E) (e i)) → (∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i)) → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ)) (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B → (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) → (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧ (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧ ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) → DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anHol | exact GlobalTheory.CompanionTheory.Ar.Flat.anHol | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anHol <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

open Matrix

variable {p q : ℕ} {g : ℕ}

theorem det_fromRows_mul_top (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows (A * C) F).det = A.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows (A * C) F = Matrix.fromBlocks A 0 0 1 * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_fromRows_mul_bot (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows C (B * F)).det = B.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows C (B * F) = Matrix.fromBlocks 1 0 0 B * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_chg (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Pe Tc : Fin p ⊕ Fin q → Fin g → ℂ)
    (S : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ) (V V' : Fin p → Fin g → ℂ) (W W' : Fin q → Fin g → ℂ)
    (Fm Fm' B₀ B' : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d d' : ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ)
    (hV : ∀ a, V' a = ∑ b, A a b • V b) (hW : ∀ j, W' j = ∑ k, B j k • W k)
    (hWi : LinearIndependent ℂ W) (hWi' : LinearIndependent ℂ W')
    (k3 : ∀ n, Tc n = ∑ j, B₀ j n • W j) (l3 : ∀ n, Tc n = ∑ j, B' j n • W' j)
    (l4 : ∀ j n, ∑ m, Fm' j m * S m n = B' j n) (hd' : d' ≠ 0)
    (k6 : ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • Pe m) = V a)
    (l7 : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V' a) →
      (Matrix.fromRows C Fm').det = d')
    (hu : ∀ (F₂ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d₂ : ℂ), (∀ j n, ∑ m, F₂ j m * S m n = B₀ j n) → d₂ ≠ 0 →
      (∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
        (Matrix.fromRows C F₂).det = d₂) → d₂ = d) :
    d * A.det = d' * B.det := by
  have lift : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
      ∀ a, T (∑ m, (A * C) a m • Pe m) = V' a := by
    intro C hC a
    have : ∑ m, (A * C) a m • Pe m = ∑ b, A a b • ∑ m, C b m • Pe m := by
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      exact Finset.sum_comm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, hV a]
    exact Finset.sum_congr rfl fun b _ => by rw [map_smul, hC b]
  obtain ⟨C₀, hC₀⟩ := k6
  have hA : A.det ≠ 0 := by
    intro h0
    have := l7 _ (lift C₀ hC₀)
    rw [det_fromRows_mul_top, h0, zero_mul] at this
    exact hd' this.symm
  have hB : B.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hc
    have hz : ∑ j, c j • W' j = 0 := by
      simp only [hW, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_smul]
      have := congrFun hcB k
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    funext j
    exact Fintype.linearIndependent_iff.1 hWi' c hz j
  have hB₀ : ∀ k n, B₀ k n = ∑ j, B j k * B' j n := by
    intro k n
    have hz : ∑ k, (B₀ k n - ∑ j, B j k * B' j n) • W k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← k3 n]
      rw [sub_eq_zero, l3 n]
      simp only [hW, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hWi _ hz k)
  have hfin := hu (Bᵀ * Fm') (B.det * d' / A.det) ?_ (div_ne_zero (mul_ne_zero hB hd') hA) ?_
  · rw [← hfin]; field_simp
  · intro j n
    rw [hB₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, ← l4]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, _root_.mul_assoc]
  · intro C hC
    have h1 := l7 _ (lift C hC)
    rw [det_fromRows_mul_top] at h1
    rw [det_fromRows_mul_bot, Matrix.det_transpose, ← h1]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l}

theorem isDerivAt0_of_isComb {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty)
    (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Sp ℂ ⟶ Xo.X)
    (hx : x = FU.u i P) {n : ℕ} (a : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) (V : Fin n → Fin g → ℂ)
    (hV : ∀ k, IsDerivAt0 (fun z => (FU.ex i P z).left) (V k) (v k).left) (h : IsComb a v w) :
    IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, a k • V k) w.left := by
  subst hx
  exact (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV a w.left).1
    ((EigDir.isComb_iff_isCombAt _ a v w).1 h)

theorem tauIn_conj {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ}
    (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) (a : 𝓞 E) :
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
  have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
    apply Subtype.ext
    show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
  rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem isLinearMap_tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty τ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem chg_of_isFlatAn {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hT : IsTypeFn H D.p D.q ty) (hrt : τ' (H.rt : E) = H.rt0) (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E))
    (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (he : LinearIndependent (𝓞 E) e)
    (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (y : Sp ℂ ⟶ Xo.XF c)
    (hy : under y = FU.u i P) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (A : Matrix (Fin D.p) (Fin D.p) ℂ) (Bm : Matrix (Fin D.q) (Fin D.q) ℂ)
    (hf : IsFramed Set.univ τ σ y v w) (hf' : IsFramed Set.univ τ σ y v' w')
    (hA : ∀ a, IsComb (A a) v (v' a)) (hB : ∀ j, IsComb (Bm j) w (w' j))
    (Φ : CFn Xo c) (ρ : ℂ) (hΦ : IsFlatAn Set.univ τ τ' σ Φ FU i e ρ) :
    Φ y v' w' * A.det = Φ y v w * Bm.det := by
  obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, hu⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v w he hP hy hf
  obtain ⟨⟨V', W', Fm', B', d'⟩, ⟨l1, l2, l3, l4, l5, ⟨C', hC'⟩, l7⟩, -⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v' w' he hP hy hf'
  have f1 : Φ y v w * d = ρ := by
    have := hΦ P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rwa [k7 C hC] at this
  have f2 : Φ y v' w' * d' = ρ := by
    have := hΦ P y v' w' V' W' C' Fm' B' hP hy hf' l1 l2 hC' l3 l4
    rwa [l7 C' hC'] at this
  obtain ⟨V₀, hV₀, -, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ τ' D.p v' hP hy hτ hf'.2.2.1
  obtain ⟨W₀, hW₀, hWi, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w hP hy (tauIn_conj hτ) hf.2.2.2
  obtain ⟨W₁, hW₁, hWi', -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w' hP hy (tauIn_conj hτ) hf'.2.2.2
  have eW : W = W₀ := funext fun j => (hW₀ j _).1 (k2 j)
  have eW' : W' = W₁ := funext fun j => (hW₁ j _).1 (l2 j)
  have hV : ∀ a, V' a = ∑ b, A a b • V b := fun a =>
    ((hV₀ a _).1 (l1 a)).trans ((hV₀ a _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ v _ V k1 (hA a))).symm
  have hW : ∀ j, W' j = ∑ k, Bm j k • W k := fun j =>
    ((hW₁ j _).1 (l2 j)).trans ((hW₁ j _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ w _ W k2 (hB j))).symm
  have key := det_chg ((isLinearMap_tyPart ty τ').mk' _) (fun m => P (e m))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)))
    (fun m n => τ' (sesq (FU.Di i) (e m) (e n))) V V' W W' Fm Fm' B₀ B' d d' A Bm hV hW
    (eW ▸ hWi) (eW' ▸ hWi') k3 l3 l4 l5 ⟨C, hC⟩ l7
    (fun F₂ d₂ h4 h5 h7 => congrArg (fun x => x.2.2.2.2) (hu (V, W, F₂, B₀, d₂) ⟨k1, k2, k3, h4, h5, ⟨C, hC⟩, h7⟩))
  apply mul_right_cancel₀ (mul_ne_zero k5 l5)
  linear_combination (A.det * d) * f2 - (Bm.det * d') * f1 + ρ * key

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hT hrt hτ
  have hrank : ∀ i, ∃ e : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e := by
    intro i
    have hr : D.p + D.q ≤ Module.finrank (𝓞 E) (FU.Di i).La := by
      rw [(FU.Di i).rank, (FU.sig i).1, (FU.sig i).2]
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hr
    exact ⟨f ∘ finSumFinEquiv, hf.comp _ finSumFinEquiv.injective⟩
  choose e he using hrank
  choose t ht hN using fun i => GlobalTheory.T.uniformised_eigen_frame_two E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) (he i)
  let ρ : Fin FU.n → ℂ := fun i => (((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)
  have hs : ∀ i, Real.sqrt (t i) ≠ 0 := fun i => (Real.sqrt_pos.2 (ht i)).ne'
  have hρ : ∀ i, ρ i ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (inv_ne_zero (hs i))
  have hρt : ∀ i, ‖ρ i‖ ^ 2 * t i = 1 := by
    intro i
    have h1 : ‖ρ i‖ = (Real.sqrt (t i))⁻¹ := by
      show ‖(((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rw [h1, inv_pow, Real.sq_sqrt (ht i).le, inv_mul_cancel₀ (ht i).ne']
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.uniformised_eigen_frames_all E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ he
  have hloc : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ →
      ∃ (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P := by
    intro y hy
    obtain ⟨i, P, hP, hu⟩ := FU.onto (under y) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
      simp only [spMap, ← Spec.map_comp]
      rfl)
    exact ⟨i, P, hP, hu.symm⟩
  refine ⟨Φ, { ne := ?_, chg := ?_, norm := ?_, hol := ?_ }, fun i => ⟨e i, ρ i, hρ i, he i, hΦ i⟩⟩
  · intro y v w hf h0
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, -⟩ :=
      GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) P y v w (he i) hP hy hf
    have := hΦ i P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rw [h0, zero_mul] at this
    exact hρ i this.symm
  · intro y v w v' w' A B hf hf' hA hB
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    exact Unit.chg_of_isFlatAn FU hT hrt hτ i (e i) (he i) P hP y hy v v' w w' A B hf hf' hA hB Φ (ρ i) (hΦ i)
  · intro y v w Γ Δ hf hΓ hΔ
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    have := hN i (ρ i) Φ (hΦ i) P y v w Γ Δ hP hy hf hΓ hΔ
    rw [this, hρt i, _root_.one_mul]
  · intro R _ x vR wR m B ψ v w h1 h2 h3
    exact GlobalTheory.T.uniformised_eigen_frames_two E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ Φ he hΦ R x vR wR m B ψ v w h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunctionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_analytic_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anUnit | exact GlobalTheory.CompanionTheory.Ar.Flat.anUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anUnit <;> assumption)
end

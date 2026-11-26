module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormSumSmul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrame
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

open scoped Matrix

namespace GlobalTheory.ArcGenBound

open Matrix

theorem affine_pos {T a b c : ℝ} (h : ∀ x s : ℝ, T < s → 0 < a + x * b + s * c) : b = 0 ∧ 0 ≤ c := by
  have h1 := h 0 (T + 1) (by linarith)
  constructor
  · by_contra hb
    have := h (-(a + (T + 1) * c) / b) (T + 1) (by linarith)
    rw [div_mul_cancel₀ _ hb] at this
    linarith
  · by_contra hc
    have hc' : 0 < -c := by linarith [not_le.1 hc]
    have hd : 0 < (a + (T + 1) * c) / (-c) := div_pos (by linarith) hc'
    have := h 0 (T + 1 + (a + (T + 1) * c) / (-c)) (by linarith)
    have e := div_mul_cancel₀ (a + (T + 1) * c) hc'.ne'
    nlinarith

theorem det_im_lower_bound {g : ℕ} (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (T : ℝ) (A B : Matrix (Fin g) (Fin g) ℂ)
    (haff : ∀ w, τ w = A + w • B) (hpos : ∀ w : ℂ, T < w.im → ((τ w).map Complex.im).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, T + 1 < w.im → C ≤ ((τ w).map Complex.im).det := by
  have hq : ∀ (w : ℂ) (v : Fin g → ℝ), v ⬝ᵥ ((τ w).map Complex.im) *ᵥ v = v ⬝ᵥ (A.map Complex.im) *ᵥ v +
      w.re * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + w.im * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := by
    intro w v
    have e : (τ w).map Complex.im = A.map Complex.im + w.re • B.map Complex.im + w.im • B.map Complex.re := by
      ext i j
      simp [haff, add_assoc]
    rw [e]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h0 : T < (⟨0, T + 1⟩ : ℂ).im := by simp
  refine ⟨((τ ⟨0, T + 1⟩).map Complex.im).det, (hpos _ h0).det_pos, fun w hw => ?_⟩
  have hw' : T < w.im := by linarith
  have hD : ((τ w).map Complex.im - (τ ⟨0, T + 1⟩).map Complex.im).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hpos w hw').isHermitian.sub (hpos _ h0).isHermitian) fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hp : ∀ x s : ℝ, T < s → 0 < v ⬝ᵥ (A.map Complex.im) *ᵥ v +
        x * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + s * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := fun x s hs => by
      have := (hpos ⟨x, s⟩ hs).dotProduct_mulVec_pos hv
      rwa [star_trivial, hq] at this
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hq, hq]
    obtain ⟨hb, hc⟩ := affine_pos hp
    have := mul_nonneg (sub_pos.2 hw).le hc
    rw [hb]
    dsimp only
    linarith
  have := GlobalTheory.ClassFin.gramLB_det_mono (hpos _ h0) hD
  rwa [add_sub_cancel] at this

end GlobalTheory.ArcGenBound


open GlobalTheory.ArcGenBound in
theorem GlobalTheory.ArcGenBound.gen_ratio_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z _ _ _
  have haff : ∀ w, Θ.τ w = Matrix.of (fun i k => (Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) i) +
      w • Matrix.of (fun i k => (Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) i) := by
    intro w
    ext i k
    have e := congrFun (Θ.per w k).2 i
    rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e
    simpa [Matrix.transpose_apply] using e.symm
  obtain ⟨C, hC, hdet⟩ := det_im_lower_bound Θ.τ Ha.T _ _ haff (fun w hw => (Θ.pos w hw).2)
  refine ⟨Ha.T + 1, Real.sqrt (‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ Uw.g * C))⁻¹), ?_⟩
  intro w hw yw hA k x t hx hb
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨hLie, hGen⟩ := hA
  have V1 := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W Uw.g _ Uw.F Ha th Θ w yw hw' hLie.1 hGen
  have V2 := Uw.norm k x hx
  obtain ⟨G, -, -, hchg⟩ := (GlobalTheory.Frames.frBor_iff_frChg _ _ _).1 hb
  have hs := (GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 E H Dw l Xo c
    σ Uw.g _ Uw.F (Uw.ik k) Ha.i (Uw.Pm k x) (Ha.Pw w) (U.un k x) yw G (t none : CAt σ) 1 _ (Uw.period k x)
    (Ha.period w hw') (Uw.lie k x).1 hLie.1 hchg V2 V1).2
  rw [mul_one] at hs
  apply Real.le_sqrt_of_sq_le
  change ‖toC (t none : CAt σ)‖ ^ 2 ≤ _
  rw [← hs]
  have hd := hdet w hw
  have h2 : (0 : ℝ) < 2 ^ Uw.g := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (Real.sqrt_pos.2 (mul_pos h2 hC)) (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd h2.le))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrameStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_generator_ratio_bounded_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  first | exact @GlobalTheory.ArcGenBound.gen_ratio_bounded | exact GlobalTheory.ArcGenBound.gen_ratio_bounded | (intros; apply GlobalTheory.ArcGenBound.gen_ratio_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLe
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ArcLieBound

theorem inv_form_le {g : ℕ} {Y₀ Y G₀ G : Matrix (Fin g) (Fin g) ℝ} (h₀ : Y₀.PosDef) (hG₀ : G₀ * Y₀ = 1)
    (hG : G * Y = 1) (hle : ∀ x, x ⬝ᵥ Y₀ *ᵥ x ≤ x ⬝ᵥ Y *ᵥ x) (a : Fin g → ℝ) : a ⬝ᵥ G *ᵥ a ≤ a ⬝ᵥ G₀ *ᵥ a := by
  have e : Y *ᵥ (G *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hG, Matrix.one_mulVec]
  have e₀ : Y₀ *ᵥ (G₀ *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hG₀, Matrix.one_mulVec]
  set x := G *ᵥ a
  set x₀ := G₀ *ᵥ a
  have hs : Y₀ᵀ = Y₀ := by simpa using h₀.1.eq
  have h1 := h₀.posSemidef.dotProduct_mulVec_nonneg (x₀ - x)
  have h2 : x₀ ⬝ᵥ Y₀ *ᵥ x = x ⬝ᵥ a := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, e₀, dotProduct_comm]
  have h3 := hle x
  rw [e] at h3
  rw [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h2, e₀] at h1
  rw [dotProduct_comm a, dotProduct_comm a]
  linarith

theorem re_hermForm_sum {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p : Fin g → Fin g → ℂ)
    (h1 : ∀ k l, (hermForm Hm (p k) (p l)).im = 0) (u : Fin g → ℂ) :
    (hermForm Hm (∑ j, u j • p j) (∑ j, u j • p j)).re =
      (fun j => (u j).re) ⬝ᵥ (Matrix.of fun k l => (hermForm Hm (p k) (p l)).re) *ᵥ (fun j => (u j).re) +
      (fun j => (u j).im) ⬝ᵥ (Matrix.of fun k l => (hermForm Hm (p k) (p l)).re) *ᵥ (fun j => (u j).im) := by
  have e : ∀ z, hermForm Hm (∑ j, u j • p j) z = ∑ j, u j * hermForm Hm (p j) z := fun z => by
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [e, Complex.re_sum, dotProduct, dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LatticeCovolumeL2.hermForm_sum_smul]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, h1, Complex.conj_re, Complex.conj_im]
  ring

theorem eq_sum {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (p : Fin g → Fin g → ℂ)
    (hp : ∀ k, h *ᵥ (p k) = Pi.single k 1) (v : Fin g → ℂ) : v = ∑ j, (h *ᵥ v) j • p j := by
  have hs : Function.Surjective (Matrix.toLin' h) := fun v =>
    ⟨∑ j, v j • p j, by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
      ext i
      simp [Pi.single_apply]⟩
  apply LinearMap.injective_iff_surjective.2 hs
  simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
  ext i
  simp [Pi.single_apply]

theorem diag_le {g : ℕ} (d : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z, z ≠ 0 → 0 < (hermForm (Matrix.diagonal fun j => (d j : ℂ)) (M *ᵥ z) (M *ᵥ z)).re)
    (z : Fin g → ℂ) (a : Fin g) :
    0 < d a ∧ d a * ‖(M *ᵥ z) a‖ ^ 2 ≤ (hermForm (Matrix.diagonal fun j => (d j : ℂ)) (M *ᵥ z) (M *ᵥ z)).re := by
  have e : ∀ v : Fin g → ℂ, (hermForm (Matrix.diagonal fun j => (d j : ℂ)) v v).re = ∑ j, d j * ‖v j‖ ^ 2 := by
    intro v
    rw [hermForm, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def, mul_left_comm, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hinj : Function.Injective (Matrix.toLin' M) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h0
    have := hpos v h0
    rw [Matrix.toLin'_apply] at hv
    simp [hv, hermForm] at this
  have hd : ∀ j, 0 < d j := fun j => by
    obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj (Pi.single j 1)
    rw [Matrix.toLin'_apply] at hv
    have := hpos v (by
      rintro rfl
      simpa using congrFun hv j)
    rw [hv, e, Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      simp [hb]
    · simp
  refine ⟨hd a, ?_⟩
  rw [e]
  exact Finset.single_le_sum (f := fun j => d j * ‖(M *ᵥ z) j‖ ^ 2)
    (fun k _ => mul_nonneg (hd k).le (sq_nonneg _)) (Finset.mem_univ a)

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} [Algebra (FractionRing ℂ) ℂ]
  [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)}
  {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} {Ha : HolArc Y σ a χ W Fu}
  {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th)

theorem exists_im_tau : ∃ A N : Matrix (Fin g) (Fin g) ℝ, ∀ w : ℂ, (Θ.τ w).map Complex.im = A + w.im • N := by
  obtain ⟨nn, h1, h2, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hreal : ∀ v j, ((Θ.h *ᵥ Ha.N v) j).im = 0 := by
    intro v j
    obtain ⟨u, hu⟩ := Θ.bas.surjective (nn v)
    have hu0 := ((Θ.orth u).1 fun v' hv' => by
      have := h2 v v'
      rwa [hv', map_zero, neg_eq_zero, ← hu] at this).1
    have hs : u = ∑ k, u (.inl k) • Pi.single (.inl k) 1 := by
      ext (i | i)
      · simp [Pi.single_apply]
      · simp [hu0]
    have hp : ∀ k, Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inl k) 1)) = Pi.single k 1 := fun k => by
      have := (Θ.per 0 k).1
      rwa [Ha.Pw_eq, zero_smul, add_zero] at this
    rw [h1, ← hu, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
    simp [Pi.single_apply]
  refine ⟨Matrix.of fun j k => ((Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) j).im,
    Matrix.of fun j k => ((Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) j).re, fun w => ?_⟩
  ext j k
  have := congrFun (Θ.per w k).2 j
  rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [show Θ.τ w j k = _ from this.symm]
  simp [hreal]

theorem im_tau_mono {w₀ w : ℂ} (hw : w₀.im ≤ w.im) (x : Fin g → ℝ) :
    x ⬝ᵥ (Θ.τ w₀).map Complex.im *ᵥ x ≤ x ⬝ᵥ (Θ.τ w).map Complex.im *ᵥ x := by
  obtain ⟨A, N, h⟩ := exists_im_tau Θ
  have e : ∀ w : ℂ, x ⬝ᵥ (Θ.τ w).map Complex.im *ᵥ x = x ⬝ᵥ A *ᵥ x + w.im * x ⬝ᵥ N *ᵥ x := fun w => by
    rw [h, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hN : 0 ≤ x ⬝ᵥ N *ᵥ x := by
    by_contra hn
    have hn' : 0 < -(x ⬝ᵥ N *ᵥ x) := by linarith
    set s : ℝ := max (Ha.T + 1) ((x ⬝ᵥ A *ᵥ x + 1) / -(x ⬝ᵥ N *ᵥ x))
    have h1 := (Θ.pos (s * Complex.I) (by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero]
      exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _))).2.posSemidef.dotProduct_mulVec_nonneg x
    rw [star_trivial, e] at h1
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
      add_zero] at h1
    have h2 : x ⬝ᵥ A *ᵥ x + 1 ≤ s * -(x ⬝ᵥ N *ᵥ x) := (div_le_iff₀ hn').1 (le_max_right _ _)
    linarith
  rw [e, e]
  have := mul_le_mul_of_nonneg_right hw hN
  linarith


omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem exists_riem_inv {w : ℂ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hR : IsRiem Fu Ha.i (Ha.Pw w) Hm) :
    ∃ G : Matrix (Fin g) (Fin g) ℝ, G * (Θ.τ w).map Complex.im = 1 ∧ ∀ v, (hermForm Hm v v).re =
      (fun j => ((Θ.h *ᵥ v) j).re) ⬝ᵥ G *ᵥ (fun j => ((Θ.h *ᵥ v) j).re) +
      (fun j => ((Θ.h *ᵥ v) j).im) ⬝ᵥ G *ᵥ (fun j => ((Θ.h *ᵥ v) j).im) := by
  let p : Fin g → Fin g → ℂ := fun j => Ha.Pw w (Θ.bas (Pi.single (.inl j) 1))
  let q : Fin g → Fin g → ℂ := fun j => Ha.Pw w (Θ.bas (Pi.single (.inr j) 1))
  have h1 : ∀ i j, (hermForm Hm (p i) (p j)).im = 0 := fun i j => by simp [p, hR.2.2, Θ.sympl, omegaStd]
  refine ⟨_, LatticeCovolumeL2.riem_inv Hm (Θ.τ w) p q
    (LatticeCovolumeL2.cols Θ.h (Θ.τ w) _ _ (fun i => (Θ.per w i).1) (fun i => (Θ.per w i).2)) h1 (fun i j => by
      simp only [p, q, hR.2.2, Θ.sympl, omegaStd]
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]), fun v => ?_⟩
  rw [← re_hermForm_sum Hm p h1, ← eq_sum Θ.h p (fun i => (Θ.per w i).1)]


include Θ in
theorem riem_anti {w₀ w : ℂ} (h₀ : Ha.T < w₀.im) (hw : w₀.im ≤ w.im) {H₀ Hm : Matrix (Fin g) (Fin g) ℂ}
    (hR₀ : IsRiem Fu Ha.i (Ha.Pw w₀) H₀) (hR : IsRiem Fu Ha.i (Ha.Pw w) Hm) (v : Fin g → ℂ) :
    (hermForm Hm v v).re ≤ (hermForm H₀ v v).re := by
  obtain ⟨G₀, a₀, b₀⟩ := exists_riem_inv Θ hR₀
  obtain ⟨G, a₁, b₁⟩ := exists_riem_inv Θ hR
  rw [b₀, b₁]
  exact add_le_add (inv_form_le (Θ.pos w₀ h₀).2 a₀ a₁ (im_tau_mono Θ hw) _)
    (inv_form_le (Θ.pos w₀ h₀).2 a₀ a₁ (im_tau_mono Θ hw) _)

end ThetaShiftProofs


open GlobalTheory.FrameNormLie GlobalTheory.FrameNorm in
set_option maxHeartbeats 1000000 in
theorem point_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}
    {U : Formalism.L2.PjFree.Unf Xo c σ r} (Uw : UnfWit U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x : (U.X k).dom) (hx : IsUnitFr (U.X k) x.1) (i₀ : Fin Uw.F.n)
    (P' : (Uw.F.Di i₀).La →+ (Fin Uw.g → ℂ))
    (p' : IsPeriod (Uw.F.Di i₀) (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) P') (y : FrPt Xo c (CAt σ))
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (hy : AnLie Uw.F i₀ P' y z) (t : Ix Dw → (CAt σ)ˣ)
    (hB : FrBor t (U.un k x) y) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (hR : IsRiem Uw.F i₀ P' Hm)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    ∃ ρ : E →+* ℂ, 0 < 2 * (ρ (-(U.X k).ξ0)).im ∧
      2 * (ρ (-(U.X k).ξ0)).im * ‖Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ)‖ ^ 2 ≤
        (hermForm Hm (z τ i) (z τ i)).re := by
  classical
  obtain ⟨g, e, F, ik, φ, hEF, Pm, hPm, hper0, hlie, hnorm⟩ := Uw
  dsimp only at *
  have hr := hU.1
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  have hP := hPm k x
  have p := hper0 k x
  obtain ⟨hPx, hv⟩ := hlie k x
  set P := Pm k x
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (U.X k).Ψ × Fin r, ∀ j,
      (Formalism.L2.PjFree.relab c σ (e j).1 ∈ (U.X k).Ψ ∧ (idx j).1.1 = Formalism.L2.PjFree.relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (Formalism.L2.PjFree.relab c σ (e j).1 ∉ (U.X k).Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  have hper : ∀ (x : Frame (U.X k).Ψ r) v j, Formalism.L2.PjFree.perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (e j).1)
      (e j).2 = perVec (U.X k) idx x v j := by
    intro x v j
    unfold perVec
    have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (Formalism.L2.PjFree.relab c σ (e j).1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ b ∈ Bor (U.X k).Ψ r, Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ))
      (PerBor.moveMat (U.X k).p0 idx b) := by
    intro b hb j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · rw [if_neg (by omega)] at h2
      exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by simp only; omega⟩
    · rw [if_neg (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      exact ⟨hbij.1 (by rw [← hcc (Formalism.L2.PjFree.relab c σ (e j).1), ← b1, ← h1, b2, hcc]), by simp only; omega⟩
  obtain ⟨T, hT, hT1, hTf⟩ := exists_tri_unit (U.X k) idx hinj hs x.1 x.2 hx
  have hPv : ∀ a, P a = perVec (U.X k) idx x.1 (φ k a : Fin r → E) := fun a => funext fun j =>
    (hP a j).trans (hper _ _ _)
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ g _ F i₀ (ik k) P' P p' p
    (by rw [← hPx, ← hy.1, hB.1])
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  obtain ⟨cf, hcf1, hcf2, hcf3⟩ := hB.2.1 τ i
  have hcol : A *ᵥ z τ i = (∑ j, (show ℂ from cf j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k x).u τ) _ (hv τ) cf
      (y.u τ i)).1 (hPx ▸ hcf3)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F _ P' p' _ P h.toLinearMap p hex _ _).1 (hy.2 τ i)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ p'.2.2.2.1
    ((T * A)ᵀ * (Matrix.diagonal (diagXi (U.X k) idx) * (T * A).map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [← UnitDet.hermForm_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hAv, hAv, ← hh, ← hh, hPv, hPv, hTf, ← hEF, hiso, hR.2.2]
      simp)
  have hval : ((T * A) *ᵥ z τ i) (e.symm ⟨τ, i⟩) =
      T (e.symm ⟨τ, i⟩) (e.symm ⟨τ, i⟩) * Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
    rw [← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, hcf1, mul_comm]
      rfl
    · intro j _ hj
      rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul, mul_eq_zero]
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · right
        by_contra hne
        have := (hT _ _ hne).2
        beta_reduce at this
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
        exact absurd hlt (not_lt.2 this)
      · exact Or.inl (hcf2 j hlt)
    · simp
  obtain ⟨h1, h2⟩ := diag_le (fun j => 2 * ((idx j).1.1 (-(U.X k).ξ0)).im) (T * A) (fun v hv => by
    rw [UnitDet.hermForm_mulVec]
    exact lt_of_lt_of_eq (hR.2.1 v hv) (by rw [← key]; rfl)) (z τ i) (e.symm ⟨τ, i⟩)
  rw [hval, norm_mul, hT1, one_mul, UnitDet.hermForm_mulVec] at h2
  exact ⟨_, h1, h2.trans (le_of_eq (by rw [← key]; rfl))⟩

theorem norm_diag_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ∀ j, ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z hσ hU _
  set w₀ : ℂ := ((Ha.T + 1 : ℝ) : ℂ) * Complex.I with hw₀
  have e₀ : w₀.im = Ha.T + 1 := by simp [hw₀]
  have h₀ : Ha.T < w₀.im := by rw [e₀]; exact lt_add_one _
  obtain ⟨H₀, hR₀⟩ := (Ha.period w₀ h₀).2.2.2.2
  obtain ⟨B, hB⟩ := (Set.finite_range fun s : U.Comp × (E →+* ℂ) × (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    (hermForm H₀ (z s.2.2.1 s.2.2.2) (z s.2.2.1 s.2.2.2)).re / (2 * (s.2.1 (-(U.X s.1).ξ0)).im)).bddAbove
  refine ⟨Ha.T + 1, Real.sqrt B, fun w hw yw hy k x t hx hb j => ?_⟩
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨Hm, hR⟩ := (Ha.period w hw').2.2.2.2
  obtain ⟨τ, i⟩ := j
  obtain ⟨ρ, h1, h2⟩ := point_bound Uw hσ hU k x hx Ha.i _ (Ha.period w hw') yw z hy.1 t hb Hm hR τ i
  refine Real.le_sqrt_of_sq_le (le_trans ?_ (hB ⟨(k, ρ, ⟨τ, i⟩), rfl⟩))
  rw [le_div_iff₀' h1]
  exact h2.trans (riem_anti Θ h₀ (by rw [e₀]; exact hw.le) hR₀ hR _)

end GlobalTheory.ArcLieBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ∀ j, ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ ≤ B := by
  first | exact @GlobalTheory.ArcLieBound.norm_diag_le | exact GlobalTheory.ArcLieBound.norm_diag_le | (intros; apply GlobalTheory.ArcLieBound.norm_diag_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArc
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArcBdd

theorem norm_prod_pow_le {ι : Type} [Fintype ι] (f : ι → ℂ) (e : ι → ℕ) (B : ℝ) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖∏ i, f i ^ e i‖ ≤ B ^ (∑ i, e i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hf i) _

theorem pnorm_unitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (hx : GlobalTheory.FrameNorm.IsUnitFr X x) :
    X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, hx τ i.succ, hx τ i.castSucc, div_one]
  simp only [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem holSub_bdd {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : (k : Comp) → Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X)
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) :
    ∃ C : ℝ, ∀ x ∈ (X k).dom, (X k).pnorm (la k) (P k) x ≤ C := by
  unfold Formalism.L2.PjFree.holSub at hP
  induction hP using Submodule.span_induction with
  | mem P hP => exact (hP k).1.2
  | zero => exact ⟨0, fun x _ => by
      have := Formalism.L2.Pj.pnorm_zero (X k) (la k) x
      simpa using this.le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨C1, h1⟩ := hP
    obtain ⟨C2, h2⟩ := hQ
    exact ⟨C1 + C2, fun x hx => (Formalism.L2.Pj.pnorm_add_le (X k) (la k) (P k) (Q k) x).trans (add_le_add (h1 x hx) (h2 x hx))⟩
  | smul s P _ hP =>
    obtain ⟨C1, h1⟩ := hP
    exact ⟨‖s‖ * C1, fun x hx => by
      have := Formalism.L2.Pj.pnorm_smul (X k) (la k) s (P k) x
      simp only [Pi.smul_apply] at this ⊢
      rw [this]
      exact mul_le_mul_of_nonneg_left (h1 x hx) (norm_nonneg _)⟩

theorem cusp_bounded_at_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Formalism.L2.PjFree.GoodEmb c σ → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ M : ℝ, ∀ (k : (U σ).Comp) (x : ((U σ).X k).dom), GlobalTheory.FrameNorm.IsUnitFr ((U σ).X k) x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x))‖ ≤ M := by
  intro E _ _ _ H Dw l Xo c r U σ a' n F hG hF
  haveI := (U σ).fin
  have hF' : Formalism.L2.PjFree.rdU (U σ) F ∈ Formalism.L2.PjFree.holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) := by
    unfold Formalism.L2.PjFree.cusp at hF
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hF
    have := hF.2 σ
    rw [Submodule.mem_iInf] at this
    exact Submodule.mem_comap.mp (this hG)
  choose C hC using holSub_bdd (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) _ hF'
  refine ⟨∑ k, max (C k) 0, fun k x hx => ?_⟩
  have h1 := hC k x.1 x.2
  rw [pnorm_unitFr _ _ _ _ hx] at h1
  have h2 : Formalism.L2.PjFree.rdU (U σ) F k x.1 = Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) := by
    simp [Formalism.L2.PjFree.rdU, x.2]
  rw [← h2]
  refine h1.trans ((le_max_left (C k) 0).trans ?_)
  exact Finset.single_le_sum (f := fun k => max (C k) 0) (fun k _ => le_max_right _ _) (Finset.mem_univ k)

theorem cusp_values_bounded_on_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c r U σ Uw _ _ O _ β Y a χ W Ha th Θ z hU hG hz a' n F hD hF
  obtain ⟨T1, B1, h1⟩ := GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨T2, B2, h2⟩ := GlobalTheory.T.arc_generator_ratio_bounded_unit_frame E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨M, hM⟩ := cusp_bounded_at_unitFr E H Dw l Xo c r U σ a' n F hG hF
  have hev : GlobalTheory.Reg.EvLaws Xo c := by
    have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    obtain ⟨-, -, hwd, hwt, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
    have hbc : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
      GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
    exact ⟨hwd, GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c, hwt, hbc⟩
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  set B := max 1 (max B1 B2)
  refine ⟨max T1 T2, max M 0 * B ^ (∑ i, ex Dw a' n i), ?_⟩
  intro w hw yw hyw
  obtain ⟨k, x, t, hux, hb⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hG (hU σ hG)).2 yw
  have hsc := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a' n F (Formalism.L2.PjFree.cusp_le_sec Xo c U a' n hF) (CAt σ)).2 inferInstance).1 t _ _ hb
  have ht : ∀ i, ‖Formalism.L2.PjFree.toC (t i : CAt σ)‖ ≤ B := by
    intro i
    rcases i with _ | j
    · exact (h2 w (lt_of_le_of_lt (le_max_right _ _) hw) yw hyw k x t hux hb).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h1 w (lt_of_le_of_lt (le_max_left _ _) hw) yw hyw k x t hux hb j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hw' : ‖Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t)‖ ≤ B ^ (∑ i, ex Dw a' n i) :=
    norm_prod_pow_le (fun i => Formalism.L2.PjFree.toC (t i : CAt σ)) (ex Dw a' n) B ht
  rw [hsc]
  change ‖(Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t) * Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) : ℂ)‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hM k x hux).trans (le_max_left _ _)) hw' (norm_nonneg _) (le_max_right _ _)

end GlobalTheory.ArcBdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArcStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_values_bounded_on_holomorphicArc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  first | exact @GlobalTheory.ArcBdd.cusp_values_bounded_on_arc | exact GlobalTheory.ArcBdd.cusp_values_bounded_on_arc | (intros; apply GlobalTheory.ArcBdd.cusp_values_bounded_on_arc <;> assumption)
end

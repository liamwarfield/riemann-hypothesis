module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPointGenerato
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLeOneAlmostAllAny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelationBaseChangeFieldZpow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameRelBCZ

open _root_.Formalism.L2.LamCM GlobalTheory.Frames GlobalTheory.LamT.FieldPoly

theorem relation_baseChange_field_zpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ (S : Type) [Field S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S)
        (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S) (s : Sˣ),
        (∀ b, (Y b).det ≠ 0) → FrMap φ y₀ z → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : S) z z' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F z' =
          ((s ^ e none : Sˣ) : S) * Formalism.L2.LamCM.evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k F hF G hG S _ _ φ z z' Y s hY hz hz'
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  haveI : Infinite K := inferInstance
  obtain ⟨P, N, hP⟩ := GlobalTheory.FrameDenseZ.exists_poly_div_det_secZ E H Dw l Xo c K y₀ e F hF

  have hevK : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      evalFr (∏ b, blockDetPoly K Dw.mult b ^ n b) X = ∏ b, (X b).det ^ n b := fun n X => by
    simp only [← evalFr_blockDetPoly Dw.mult _ X]
    simp only [evalFr, map_prod, map_pow]
  have hevS : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S),
      evalFr (MvPolynomial.map φ.toRingHom (∏ b, blockDetPoly K Dw.mult b ^ n b)) X = ∏ b, (X b).det ^ n b :=
    fun n X => by
    simp only [← evalFr_map_blockDetPoly φ.toRingHom Dw.mult _ X]
    simp only [evalFr, map_prod, map_pow]

  have hid : (∏ b, blockDetPoly K Dw.mult b ^ N) * G = (∏ b, blockDetPoly K Dw.mult b ^ k b) * P := by
    by_contra hne
    obtain ⟨X, hX, hX0⟩ := GlobalTheory.FrameDenseZ.exists_frame_evalFr_ne_zero Dw.mult _ (sub_ne_zero.2 hne)
    obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
      (fun b => by rw [Matrix.det_transpose]; exact (hX b).isUnit)
    rw [Units.val_one] at hy'
    have h1 := hG y' X hX hy'
    have h2 := hP K (AlgHom.id c.F K) y₀ y' X (fun b => (hX b).isUnit)
      (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y₀).2.1 hy'
    rw [show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at h2
    apply hX0
    have e1 : evalFr ((∏ b, blockDetPoly K Dw.mult b ^ N) * G - (∏ b, blockDetPoly K Dw.mult b ^ k b) * P) X
        = evalFr (∏ b, blockDetPoly K Dw.mult b ^ N) X * evalFr G X
          - evalFr (∏ b, blockDetPoly K Dw.mult b ^ k b) X * evalFr P X := by
      simp only [evalFr, map_mul, map_sub]
    rw [e1, hevK, hevK, ← h1, ← h2, Finset.prod_pow]
    ring

  have hidS : (∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y
      = (∏ b, (Y b).det ^ k b) * evalFr (MvPolynomial.map φ.toRingHom P) Y := by
    have h := congrArg (fun Q => evalFr (MvPolynomial.map φ.toRingHom Q) Y) hid
    rw [← hevS, ← hevS]
    simpa only [evalFr, map_mul] using h

  have hYt : ∀ b, IsUnit ((Y b).transpose.det) := fun b => by
    rw [Matrix.det_transpose]; exact (hY b).isUnit
  obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) 1 hYt
  obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun _ => 1) s (fun _ => by simp)
  have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
  have e' : z2 = z' := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) s hYt).unique h3 hz'
  subst e'
  let t : Formalism.L2.Pj.Ix Dw → Sˣ := fun i => match i with
    | none => s
    | some _ => 1
  have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S z1 z2 z2).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF S t z1 z2 hb
  have ht1 : ((∏ i, t i ^ e i : Sˣ) : S) = ((s ^ e none : Sˣ) : S) := by
    simp [Fintype.prod_option, t]
  rw [ht1] at hw
  have hv := hP S φ z z1 Y (fun b => (hY b).isUnit) hz h1
  rw [hw]
  have hu : (∏ b, (Y b).det ^ N) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)
  apply mul_left_cancel₀ hu
  have hre : (∏ b, (Y b).det ^ N) * (((s ^ e none : Sˣ) : S) * evalFr (MvPolynomial.map φ.toRingHom G) Y) =
      ((s ^ e none : Sˣ) : S) * ((∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y) := by ring
  rw [hre, hidS, ← hv, Finset.prod_pow]
  ring

end GlobalTheory.FrameRelBCZ

namespace GlobalTheory.FrameHomZ

open _root_.Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly GlobalTheory.FrameHom

theorem frPoly_secZ_degree_eq_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ μ, AddMonoidAlgebra.coeff G μ ≠ 0 →
        (μ.degree : ℤ) = ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k F hF G hG μ hμ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]
  have hDp : (∏ b, blockDetPoly K Dw.mult b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  refine degree_eq_of_scaling_zpow G _ hDp _ (fun x hx => ?_) μ hμ
  let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K :=
    fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
  have hX : ∀ b, (X b).det ≠ 0 := fun b => by
    have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact hx
    exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
  have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  let t : Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some _ => Units.mk0 2 h2
  have hb : FrBor t z₁ z₂ := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => ?_, h₂⟩
    · simp [T, Matrix.transpose_apply, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
    · simp [T, t]
  have e₁ := hG z₁ X hX h₁
  have e₂ := hG z₂ (fun b' => X b' * T b')
    (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
  have e₃ := evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
  have p₁ : ((∏ i, t i ^ e i : Kˣ) : K) = (2 : K) ^ (∑ b, ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
    rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
    simp only [t, one_zpow, Units.val_one, _root_.one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← prod_zpow_eq_zpow_sum h2]
    exact Finset.prod_congr rfl fun b _ => prod_zpow_eq_zpow_sum h2 _ _
  have p₂ : (∏ b, (X b * T b).det ^ k b) = (2 : K) ^ (∑ b, (Dw.mult b : ℤ) * (k b : ℤ)) * ∏ b, (X b).det ^ k b := by
    rw [← prod_zpow_eq_zpow_sum h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Matrix.det_mul]
    simp only [T, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((Dw.mult b : ℤ) * (k b : ℤ)) = ((Dw.mult b * k b : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    ring
  have p₃ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
    unfold evalFr
    congr 2
    funext v
    simp [X, T, Matrix.mul_diagonal, mul_comm]
  have p₄ : evalFr G X = MvPolynomial.eval x G := rfl
  rw [← p₃, ← e₂, p₂, e₃, p₁, ← p₄, ← e₁, Finset.sum_add_distrib, zpow_add₀ h2]
  ring

end GlobalTheory.FrameHomZ

namespace GlobalTheory.FrameCoeffLocZ

theorem coeff_mul_prod_zpow_mem_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → a ≠ 0 → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → GlobalTheory.LamT.SecInt T M.m1 M.m2 y'.s →
        ∀ cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr,
          (∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
        ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, ∃ w : T.V, iK (AddMonoidAlgebra.coeff G μ) * (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v) * a ^ e none =
          (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k p T iK hT hiK M
  intro φ yT y' g a hφ hyT hy' ha hg hL hS cl hcl F hF hv G hG μ
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  have hτ : (∏ b, (g b).det ^ k b) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hg b).ne_zero
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hφ, hz.2.2.2.1]
  have main : ∃ w : T.V, AddMonoidAlgebra.coeff (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G) μ * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
      (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
    refine Formalism.L2.LamCM.coeff_integral_local T.V T.Fr _ Dw.mult (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G) (fun b => (g b)⁻¹) cl _
      inferInstance hT hτ (fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero) hcl ?_ μ
    intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
    have hinj : Function.Injective (algebraMap T.V W) := by
      intro x y h
      apply IsFractionRing.injective T.V T.Fr
      apply fW.injective
      rw [hfW, hfW, h]
    haveI : CharZero W := charZero_of_injective_ringHom hinj
    let T' : Formalism.L2.Pj.CDVR := ⟨W⟩
    let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
    have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
      (FractionRing.algEquiv W KW).symm.commutes w
    let i : T.Fr →+* T'.Fr := κ.comp fW
    have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
      ext x
      show _ = κ (fW _)
      rw [hfW, hκ]
      rfl
    letI := (i.comp io).toAlgebra
    let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
    obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
    obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
    have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g a hy' hyW).1 hy''
    have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
      rw [Matrix.det_transpose]; exact hX b
    have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
      have := (hXt b).map (algebraMap T'.V T'.Fr)
      rwa [RingHom.map_det] at this
    obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
    have hint := GlobalTheory.LamT.LocClause.integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
      (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
    obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
    have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
      rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hg b)]
      simp
    have hYX' : ∀ b, ((Y b).map κ).transpose =
        ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
      rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
      congr 1
      ext j k
      exact hκ _
    have hdet : ∀ b, ((Y b).map κ).det = algebraMap T'.V T'.Fr (X b).det * i (g b).det := fun b => by
      rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
      congr 1
      · rw [← Matrix.det_transpose (X b)]; exact (RingHom.map_det _ _).symm
      · exact (RingHom.map_det i (g b)).symm
    have hYd : ∀ b, ((Y b).map κ).det ≠ 0 := fun b => by
      rw [hdet b]
      exact mul_ne_zero ((hX b).map (algebraMap T'.V T'.Fr)).ne_zero ((map_ne_zero i).2 (hg b).ne_zero)
    have hsn : (iA a : T'.Fr) ≠ 0 := (map_ne_zero iA).2 ha
    have hc' : GlobalTheory.Frames.FrChg (fun b => ((Y b).map κ).transpose) ((Units.mk0 (iA a) hsn : T'.Frˣ) : T'.Fr) yW w := by
      have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c T'.Fr yW y'' w).2 _ _ _ _ hc hw
      simpa [hYX'] using c2
    have hbc := GlobalTheory.FrameRelBCZ.relation_baseChange_field_zpow E H Dw l Xo c z.K z.y e k F hF G hG T'.Fr (iA.comp φ) yW w (fun b => (Y b).map κ)
      (Units.mk0 (iA a) hsn) hYd (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW) hc'
    refine ⟨(∏ b, (X b).det ^ k b) * w₀, κ.injective ?_⟩
    have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G)) =
        MvPolynomial.C ((iA a) ^ e none) * MvPolynomial.map (iA.comp φ).toRingHom G := by
      rw [map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_map,
        MvPolynomial.map_map, ← hφ, map_zpow₀, map_zpow₀]
      rfl
    have hu : ((Units.mk0 (iA a) hsn ^ e none : T'.Frˣ) : T'.Fr) = (iA a) ^ e none := by simp
    rw [GlobalTheory.LamT.LocClause.map_evalFr, hP, Formalism.L2.LamCM.evalFr_C_mul, ← hu, ← hbc, ← hw₀]
    simp only [hdet, map_mul, map_prod, map_pow, hκ, Finset.prod_mul_distrib, mul_pow]
    show _ = (∏ b, i (g b).det ^ k b) * _
    ring
  obtain ⟨w, hw⟩ := main
  exact ⟨w, by rw [← hw, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]; ring⟩

end GlobalTheory.FrameCoeffLocZ
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffDenomZ


open GlobalTheory.LamT GlobalTheory.CoeffDenom in
theorem exists_clear_coeff_at_prime_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k p
  classical
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  choose c0 hc0 using fun (b : E →+* ℂ) (j : Fin (Dw.mult b)) =>
    LocClause.exists_isLocGen p (z.ℓ (z.e ⟨b, j⟩)).I
  let cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr := fun b j => iK (c0 b j)
  have hcl : ∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i =>
    GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i _ (hc0 b j)
  have hloc := GlobalTheory.FrameCoeffLocZ.coeff_mul_prod_zpow_mem_det E H Dw l Xo c z f La hz e k p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg
    hL hS cl hcl

  let D : ℤ := ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩))
  let S : Finset (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := Formalism.L2.LamCM.FrVar Dw.mult) D.toNat).toFinset
  let τ : T.Fr := ∏ b, (g b).det ^ k b
  let yμ : (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) → T.Fr := fun μ =>
    τ * (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v)⁻¹ * ((s : T.Fr) ^ e none)⁻¹
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T.V) (S.image yμ)

  obtain ⟨ϖ, hϖp, hϖ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hϖv : p.valuation z.K (ϖ : z.K) < 1 := (p.valuation_lt_one_iff_mem ϖ).2 hϖp
  obtain ⟨π, hπ⟩ := (hiK (ϖ : z.K)).2 (p.valuation_le_one ϖ)
  have hϖK : (ϖ : z.K) ≠ 0 := fun h => hϖ0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hπ
    exact hϖK hπ
  have hπu : ¬ IsUnit π := by
    rintro ⟨u, rfl⟩
    have h1 : iK ((ϖ : z.K)⁻¹) ∈ Set.range (algebraMap T.V T.Fr) := by
      refine ⟨((u⁻¹ : T.Vˣ) : T.V), ?_⟩
      rw [map_inv₀, ← hπ]
      exact map_units_inv (algebraMap T.V T.Fr) u
    have h2 := (hiK _).1 h1
    rw [map_inv₀] at h2
    have h0 : p.valuation z.K (ϖ : z.K) ≠ 0 := (Valuation.ne_zero_iff _).2 hϖK
    have h4 : (1 : _) ≤ p.valuation z.K (ϖ : z.K) :=
      calc (1 : _) = p.valuation z.K (ϖ : z.K) * (p.valuation z.K (ϖ : z.K))⁻¹ := (mul_inv_cancel₀ h0).symm
        _ ≤ p.valuation z.K (ϖ : z.K) * 1 := by gcongr
        _ = p.valuation z.K (ϖ : z.K) := mul_one _
    exact absurd hϖv (not_lt.2 h4)
  obtain ⟨N, t, hNt⟩ := dvd_pow_of_ne_zero_of_not_isUnit (nonZeroDivisors.ne_zero d.2) hπ0 hπu
  refine ⟨ϖ ^ N, pow_ne_zero _ hϖ0, ?_⟩
  intro F hF hv G hG μ
  by_cases hμ : AddMonoidAlgebra.coeff G μ = 0
  · simp [hμ]
  have hG1 := hG
  have hdeg := GlobalTheory.FrameHomZ.frPoly_secZ_degree_eq_any E H Dw l Xo c z.K z.y e k F hF G hG1 μ hμ
  have hμS : μ ∈ S := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  obtain ⟨w, hw⟩ := hloc F hF hv G hG1 μ
  obtain ⟨r, hr⟩ := hd (yμ μ) (Finset.mem_image_of_mem yμ hμS)
  apply (hiK _).1
  have hP : (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ((map_ne_zero iK).2 (hc0 v.1 v.2.2).1)
  have hc : iK (AddMonoidAlgebra.coeff G μ) = yμ μ * algebraMap T.V T.Fr w := by
    have hsn : ((s : T.Fr) ^ e none) ≠ 0 := zpow_ne_zero _ s.ne_zero
    have e0 : yμ μ * algebraMap T.V T.Fr w = (τ * algebraMap T.V T.Fr w) *
        ((∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v)⁻¹ * ((s : T.Fr) ^ e none)⁻¹) := by
      simp only [yμ]; ring
    rw [e0, ← hw]
    field_simp
  rw [Algebra.smul_def] at hr
  have e1 : (((ϖ ^ N : 𝓞 z.K)) : z.K) = (ϖ : z.K) ^ N := by simp
  refine ⟨t * r * w, ?_⟩
  rw [map_mul iK, e1, map_pow, ← hπ, ← map_pow, hNt, hc]
  simp only [map_mul]
  rw [hr]
  ring

end GlobalTheory.CoeffDenomZ

namespace GlobalTheory.CoeffIntZ

theorem coeff_valuation_le_one_almost_all_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  have hfinT := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors z.Tl.I)
  refine ⟨S₁ ∪ hfin.toFinset ∪ hfinT.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  have hp1 : p ∉ S₁ := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hp2 : ∀ j, FractionalIdeal.count z.K p (z.ℓ j).I = 0 := by
    intro j
    by_contra h
    exact hp (Finset.mem_union_left _ (Finset.mem_union_right _
      (hfin.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨j, h⟩))))
  have hp3 : FractionalIdeal.count z.K p z.Tl.I = 0 := by
    by_contra h
    exact hp (Finset.mem_union_right _ (hfinT.mem_toFinset.mpr h))
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.FrameCoeffLocZ.coeff_mul_prod_zpow_mem_det E H Dw l Xo c z f La hz e k p T iK hT hiK M φ yT y' g s rfl
    hyT hy' s.ne_zero hg hL hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G hG μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw

  have hgenT : Formalism.L2.LamCM.IsLocGen p (1 : z.K) z.Tl.I := by
    refine ⟨one_ne_zero, ?_⟩
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
    simpa using hp3.symm
  obtain ⟨u, hu⟩ := GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hS 1 hgenT
  rw [map_one, _root_.one_mul] at hu
  have hsn : ((s : T.Fr) ^ e none) ≠ 0 := zpow_ne_zero _ s.ne_zero
  have hsinv : ((s : T.Fr) ^ e none)⁻¹ ∈ (algebraMap T.V T.Fr).range := by
    refine ⟨((u ^ (-e none) : T.Vˣ) : T.V), ?_⟩
    have h1 : algebraMap T.V T.Fr ((u ^ (-e none) : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (u ^ (-e none)) : T.Frˣ) : T.Fr) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val, hu, zpow_neg]
    rfl
  have hc : iK (AddMonoidAlgebra.coeff G μ) = (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w * ((s : T.Fr) ^ e none)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hsn).2 hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hc]
  exact Subring.mul_mem _ (Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)) hsinv

end GlobalTheory.CoeffIntZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPointGenerato
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatFull.CMIntZ

theorem exists_coeff_denom_intWt_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.CoeffIntZ.coeff_valuation_le_one_almost_all_any E H Dw l Xo c z f La hz e k
  choose x hx0 hx using GlobalTheory.CoeffDenomZ.exists_clear_coeff_at_prime_any E H Dw l Xo c z f La hz e k
  refine ⟨∏ p ∈ S, x p, Finset.prod_ne_zero_iff.2 fun p _ => hx0 p, fun F hF hv G hG μ => ?_⟩
  have hint : ∀ r : 𝓞 z.K, ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K), p.valuation z.K (r : z.K) ≤ 1 :=
    fun r p => p.valuation_le_one r
  have hv1 : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
      p.valuation z.K (((∏ q ∈ S, x q : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
    intro p
    by_cases hp : p ∈ S
    · rw [← Finset.mul_prod_erase S x hp]
      have e1 : (((x p * ∏ q ∈ S.erase p, x q : 𝓞 z.K)) : z.K) * AddMonoidAlgebra.coeff G μ =
          ((∏ q ∈ S.erase p, x q : 𝓞 z.K) : z.K) * (((x p : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) := by
        push_cast; ring
      rw [e1, map_mul]
      exact mul_le_one' (hint _ p) (hx p F hF hv G hG μ)
    · rw [map_mul]
      exact mul_le_one' (hint _ p) (hS p hp F hF hv G hG μ)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one z.K _ hv1
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

end GlobalTheory.LatFull.CMIntZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPointGeneratoStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  first | exact @GlobalTheory.LatFull.CMIntZ.exists_coeff_denom_intWt_any | exact GlobalTheory.LatFull.CMIntZ.exists_coeff_denom_intWt_any | (intros; apply GlobalTheory.LatFull.CMIntZ.exists_coeff_denom_intWt_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousSecZGenFix
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FieldPolyZ

open GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT _root_.Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly

theorem exists_isHomogeneous_secZ_genFix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ)
    (k : (E →+* ℂ) → ℕ) (a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ),
    (∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ)) →
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∃ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      G.IsHomogeneous (∑ b, ∑ i, a b i) ∧
      ∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
        (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k a hea F hF
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_of_natural E H Dw l Xo c K y₀ F hF.1
  have hrefl : FrMap (AlgHom.id c.F K) y₀ y₀ := GlobalTheory.Frames.frMapUniq_refl y₀
  set M : ℕ := ∑ b, k b with hM
  have hkM : ∀ b, k b ≤ M := fun b =>
    Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  set P' : MvPolynomial (FrVar Dw.mult) K := (∏ b, FieldPoly.blockDetPoly K Dw.mult b) ^ M * P with hP'
  have hevD : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, FieldPoly.blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← FieldPoly.evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]

  have hA : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' →
      (∏ b, (Y b).det) ^ (M + N) * evR Xo c F z' = evalFr P' Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y₀ z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rw [h2] at h1
    have h3 : evalFr P' Y = evalFr (∏ b, FieldPoly.blockDetPoly K Dw.mult b) Y ^ M * evalFr P Y := by
      simp only [hP', evalFr, map_mul, map_pow]
    rw [h3, hevD, ← h1, pow_add, mul_assoc]

  have hB : ∀ (z₁ z₂ : FrPt Xo c K) (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (T b).BlockTriangular id) → (∀ b, (T b).det ≠ 0) → FrChg (fun b => (T b).transpose) 1 z₁ z₂ →
      (∏ b, ∏ i, T b i i ^ k b) * evR Xo c F z₂ = (∏ b, ∏ i, T b i i ^ a b i) * evR Xo c F z₁ := by
    intro z₁ z₂ T hT hd h
    have hne : ∀ b i, T b i i ≠ 0 := by
      intro b i
      have h1 := hd b
      rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
      exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
    let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
      | none => 1
      | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
    have hb : FrBor t z₁ z₂ := by
      refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
        ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
      exact hT τ hij
    have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
    have key : ∀ b i, T b i i ^ k b * ((Units.mk0 (T b i i) (hne b i) ^ e (some ⟨b, i⟩) : Kˣ) : K) =
        T b i i ^ a b i := by
      intro b i
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne b i),
        ← hea b i, add_comm]
    have hc : (∏ b, ∏ i, T b i i ^ k b) * ((∏ o, t o ^ e o : Kˣ) : K) = ∏ b, ∏ i, T b i i ^ a b i := by
      rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
      simp only [t, one_zpow, Units.val_one, _root_.one_mul]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact key b i
    rw [hw, ← _root_.mul_assoc, hc]

  have hP'tr : ∀ (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (b : E →+* ℂ)
      (t : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
      evalFr P' (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + (M + N - k b))) * evalFr P' X := by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hA z₁ X hX h₁
    have e₂ := hA z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := hB z₁ z₂ T hTtri hTd h₂
    have p₁ : ∀ f : (E →+* ℂ) → ℕ, (∏ b', ∏ i, T b' i i ^ f b') = ∏ i, t i i ^ f b := by
      intro f
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₁' : (∏ b', ∏ i, T b' i i ^ a b' i) = ∏ i, t i i ^ a b i := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [p₁ k, p₁'] at e₃
    have hti : ∀ i, t i i ≠ 0 := by
      intro i
      have h1 := ht
      rw [Matrix.det_of_isUpperTriangular htri] at h1
      exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
    have hk0 : (∏ i, t i i ^ k b) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hti i)
    have hL : (∏ i, t i i ^ k b) * ∏ i, t i i ^ (a b i + (M + N - k b)) =
        (∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← pow_add]
      congr 1
      have := hkM b
      omega
    rw [hup, ← e₂, ← e₁, p₂]
    apply mul_left_cancel₀ hk0
    calc (∏ i, t i i ^ k b) * (((∏ b', (X b').det) * ∏ i, t i i) ^ (M + N) * evR Xo c F z₂)
        = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ k b) * evR Xo c F z₂) := by
          ring
      _ = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ a b i) * evR Xo c F z₁) := by
          rw [e₃]
      _ = ((∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i) * ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁) := by
          ring
      _ = (∏ i, t i i ^ k b) * ((∏ i, t i i ^ (a b i + (M + N - k b))) *
            ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁)) := by
          rw [← hL]; ring

  obtain ⟨G, hG⟩ := FieldPoly.exists_eq_prod_blockDetPoly_pow_mul K (E →+* ℂ) Dw.mult a _ (fun b => M + N - k b) rfl P'
    (fun X b t hX ht htri => hP'tr X b t hX ht htri)
  have hGY : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' →
      (∏ b, (Y b).det ^ k b) * evR Xo c F z' = evalFr G Y := by
    intro z' Y hY h
    have h1 := hA z' Y hY h
    have h2 : evalFr P' Y = (∏ b, (Y b).det ^ (M + N - k b)) * evalFr G Y := by
      rw [hG]
      simp only [← FieldPoly.evalFr_blockDetPoly Dw.mult _ Y]
      simp only [evalFr, map_mul, map_prod, map_pow]
    have hne : (∏ b, (Y b).det ^ (M + N - k b)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)
    apply mul_left_cancel₀ hne
    rw [← h2, ← h1, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [← pow_add]
    congr 1
    have := hkM b
    omega

  have hGhom : G.IsHomogeneous (∑ b, ∑ i, a b i) := by
    refine isHomogeneous_of_scaling G (∏ b, FieldPoly.blockDetPoly K Dw.mult b) (fun h0 => ?_) _ (fun x hx => ?_)
    · have h1 := hevD fun _ => 1
      rw [h0] at h1
      simp [evalFr] at h1
    · let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
      let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
      have hX : ∀ b, (X b).det ≠ 0 := fun b => by
        have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hevD X]; exact hx
        exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
      have hTtri : ∀ b, (T b).BlockTriangular id := fun b => Matrix.blockTriangular_diagonal _
      have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
      obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
        (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
      obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
        (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
      rw [Units.val_one] at h₁ h₂
      have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
      simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
      have e₁ := hGY z₁ X hX h₁
      have e₂ := hGY z₂ (fun b' => X b' * T b')
        (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
      have e₃ := hB z₁ z₂ T hTtri hTd h₂
      have p₁ : (∏ b, ∏ i, T b i i ^ a b i) = 2 ^ (∑ b, ∑ i, a b i) := by
        simp only [T, Matrix.diagonal_apply_eq, Finset.prod_pow_eq_pow_sum]
      have p₂ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
        simp [evalFr, X, T, Matrix.mul_diagonal, mul_comm]
      have p₃ : (∏ b, (X b * T b).det ^ k b) = (∏ b, (X b).det ^ k b) * ∏ b, ∏ i, T b i i ^ k b := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [Matrix.det_mul, mul_pow, Matrix.det_of_isUpperTriangular (hTtri b), Finset.prod_pow]
      have e₁' : MvPolynomial.eval x G = (∏ b, (X b).det ^ k b) * evR Xo c F z₁ := by
        rw [e₁]; rfl
      rw [← p₂, ← e₂, p₃, _root_.mul_assoc, e₃, p₁, e₁']
      ring
  exact ⟨G, hGhom, hGY⟩

theorem exists_frChg_one_evR_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ y' : FrPt Xo c K)
    (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (s : Kˣ),
    (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : K) y₀ y' →
    ∃ w₀ : FrPt Xo c K, GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ w₀ ∧
      ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e,
        evR Xo c F y' = (((s ^ e none : Kˣ)) : K) * evR Xo c F w₀ := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ y' Y s hY h
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K w₀ (fun _ => 1) s (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have ew : w₁ = y' := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) s hYt).unique ?_ h
    simpa using c1
  subst ew
  rw [Units.val_one] at hw₀
  refine ⟨w₀, hw₀, fun e F hF => ?_⟩
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => o.elim s (fun _ => 1)
  have hb : FrBor t w₀ w₁ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K w₀ w₁ w₁).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], hw₁⟩
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t w₀ w₁ hb
  have ht1 : (∏ i, t i ^ e i : Kˣ) = s ^ e none := by
    simp [t, Fintype.prod_option]
  rw [hw, ht1]

end GlobalTheory.FieldPolyZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightPowerCm
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_dominant_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ la : GlobalTheory.AllWt.Weight Dw, (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) (Dw.p - 1)) → ∀ m : ℕ, ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la m), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy _hp _hq la _hanti _hgap m
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la m with he
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint_generator E H Dw l Xo c z f La hz e k
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  obtain ⟨w₀, hw₀, hsw⟩ := GlobalTheory.FieldPolyZ.exists_frChg_one_evR_eq E H Dw l Xo c z.K z.y y Y s hYd
    (by rw [hgY]; exact hgs)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  have hsu : (((s ^ e none : z.Kˣ)) : z.K) ≠ 0 := Units.ne_zero _
  refine ⟨N₀ * (∏ b, (Y b).det ^ k b) * ((((s ^ e none : z.Kˣ)) : z.K))⁻¹,
    mul_ne_zero (mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b))) (inv_ne_zero hsu),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ_genFix E H Dw l Xo c z.K z.y e k a hak F hF
  have h1 := hG w₀ Y hYd hw₀
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * ((((s ^ e none : z.Kˣ)) : z.K))⁻¹ * evR Xo c F y =
      N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [hsw e F hF, ← h1]
    field_simp
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' hY' h' => hG y' Y' hY' h') μ⟩, ?_⟩
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  change (t : z.K) * AddMonoidAlgebra.coeff G μ * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightPowerCmStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_denominator_dominant_weight_power_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ la : GlobalTheory.AllWt.Weight Dw, (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) (Dw.p - 1)) → ∀ m : ℕ, ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la m), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  first | exact @GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant_pow | exact GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant_pow | (intros; apply GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant_pow <;> assumption)
end

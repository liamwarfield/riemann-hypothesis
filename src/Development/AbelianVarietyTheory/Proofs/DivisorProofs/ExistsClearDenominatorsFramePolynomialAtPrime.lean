module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffBoundedByDeterminants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
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

namespace GlobalTheory.CoeffDenom

theorem dvd_pow_of_ne_zero_of_not_isUnit {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {d π : V} (hd : d ≠ 0) (hπ : π ≠ 0) (hπu : ¬ IsUnit π) : ∃ N : ℕ, d ∣ π ^ N := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨b, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ hϖ
  have hb : b ≠ 0 := by
    rintro rfl
    exact hπu (by rw [hu', pow_zero, mul_one]; exact u'.isUnit)
  refine ⟨a, ?_⟩
  rw [hu, hu', mul_pow, ← pow_mul]
  refine (Units.isUnit u).mul_left_dvd.2 (Dvd.dvd.mul_left ?_ _)
  exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hb))

end GlobalTheory.CoeffDenom

namespace GlobalTheory.CoeffDenom


open GlobalTheory.LamT in
theorem exists_clear_coeff_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 → ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he p
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
  have hloc := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg
    hL hS cl hcl

  let D : ℤ := ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩))
  let S : Finset (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := Formalism.L2.LamCM.FrVar Dw.mult) D.toNat).toFinset
  let τ : T.Fr := ∏ b, (g b).det ^ k b
  let yμ : (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) → T.Fr := fun μ => τ * (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v)⁻¹
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
  have hG1 : ∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
      (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
      (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := fun y'' Y hY hc =>
    hG y'' Y 1 hY (by rw [Units.val_one]; exact hc)
  have hdeg := GlobalTheory.T.framePolynomial_integerExponent_degree_eq E H Dw l Xo c z.K z.y e k he F hF G hG1 μ hμ
  have hμS : μ ∈ S := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  obtain ⟨w, hw⟩ := hloc F hF hv G hG1 μ
  obtain ⟨r, hr⟩ := hd (yμ μ) (Finset.mem_image_of_mem yμ hμS)
  apply (hiK _).1
  have hP : (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ((map_ne_zero iK).2 (hc0 v.1 v.2.2).1)
  have hc : iK (AddMonoidAlgebra.coeff G μ) = yμ μ * algebraMap T.V T.Fr w := by
    simp only [yμ]
    rw [mul_comm τ, mul_assoc, ← hw]
    field_simp
  rw [Algebra.smul_def] at hr
  have e1 : (((ϖ ^ N : 𝓞 z.K)) : z.K) = (ϖ : z.K) ^ N := by simp
  refine ⟨t * r * w, ?_⟩
  rw [map_mul iK, e1, map_pow, ← hπ, ← map_pow, hNt, hc]
  simp only [map_mul]
  rw [hr]
  ring

end GlobalTheory.CoeffDenom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrimeStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clear_denominators_framePolynomial_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 → ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  first | exact @GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime | exact GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime | (intros; apply GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlas
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlas
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (f : Γ(X, V)) : valF w V f = ev w V hV f :=
  GlobalTheory.Points.valR_eq w V hV f

theorem map_valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    {m n : Type} (A : Matrix m n Γ(X, V)) : A.map (valF w V) = A.map (ev w V hV) := by
  ext i j
  exact valF_eq_ev w V hV _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)}

def trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) : Matrix (Fin (N + 1)) (Fin k.M.n) Γ(Y.X, k.V) :=
  (A₀.map (resG Y.X hV)).submatrix id (finCongr (congrArg (fun M : GChart Y => M.n) hk))

def trC {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U)) : Matrix (Fin k.M.n) (Fin (N + 1)) Γ(Y.X, k.V) :=
  (C₀.map (resG Y.X hV)).submatrix (finCongr (congrArg (fun M : GChart Y => M.n) hk)) id

theorem trC_mul_trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U))
    (h : C₀ * A₀ = 1) : trC hk hV C₀ * trA hk hV A₀ = 1 := by
  subst hk
  ext i j
  have := congrArg (fun A => resG Y.X hV (A i j)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simp only [trC, trA, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Fin.cast_eq_self, id]
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tw_tr [IsReduced Y.X] {k k' : ECh Y p} {M₀ M₀' : GChart Y} (hk : k.M = M₀) (hk' : k'.M = M₀')
    {U U' : Y.X.Opens} (hV : k.V ≤ U) (hV' : k'.V ≤ U') (hUM : U ⊓ U' ≤ M₀'.U ⊓ M₀.U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (A₀' : Matrix (Fin (N + 1)) (Fin M₀'.n) Γ(Y.X, U'))
    (g : Γ(Y.X, U ⊓ U')ˣ)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ⊤ ≤ w ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U' →
      A₀.map (valF w _) = valF w _ g.val • (A₀'.map (valF w _) * (chg M₀'.toMChart M₀.toMChart).map (valF w _)))
    (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ k.V) (h' : ⊤ ≤ x ⁻¹ᵁ k'.V)
    (hM : ⊤ ≤ x ⁻¹ᵁ (k'.M.U ⊓ k.M.U)) :
    ∃ a : Sˣ, (trA hk hV A₀).map (ev x _ h) =
      (a : S) • ((trA hk' hV' A₀').map (ev x _ h') * (chg k'.M.toMChart k.M.toMChart).map (ev x _ hM)) := by
  subst hk hk'
  have key : ∀ r j, resG Y.X (inf_le_left : U ⊓ U' ≤ U) (A₀ r j) =
      g.val * ∑ t, resG Y.X inf_le_right (A₀' r t) * resG Y.X hUM (chg k'.M.toMChart k.M.toMChart t j) := by
    intro r j
    refine GlobalTheory.TwistEmb.eq_of_valR fun K _ w hw => ?_
    have hw1 := le_preimage_mono inf_le_left hw
    have hw2 := le_preimage_mono inf_le_right hw
    have hw3 := le_preimage_mono hUM hw
    have e := congrFun (congrFun (H K w hw1 hw2) r) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, valF_eq_ev w U hw1,
      valF_eq_ev w U' hw2, valF_eq_ev w _ hw, valF_eq_ev w _ hw3] at e
    show valF w _ _ = valF w _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [valF_eq_ev w _ hw, valF_eq_ev w _ hw, ev_res w _ hw hw1, e, map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, ev_res w _ hw hw2, ev_res w _ hw hw3]
  have hx : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := GlobalTheory.TwistEmb.le_inf' x (le_preimage_mono hV h) (le_preimage_mono hV' h')
  refine ⟨Units.map (ev x _ hx).toMonoidHom g, ?_⟩
  ext r j
  simp only [trA, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_eq_self, id, smul_eq_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ev_res x hV h (le_preimage_mono hV h), ← ev_res x inf_le_left hx (le_preimage_mono hV h), key, map_mul,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, ev_res x inf_le_right hx (le_preimage_mono hV' h'), ev_res x hV' h' (le_preimage_mono hV' h'),
    ev_res x hUM hx hM]

theorem exists_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)),
    PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  intro E _ _ _ H Dw l Xo c Y p hP
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => exists_gChart hP x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenChart_affineOpen_within E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

end GlobalTheory.FlagMod.FieldFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlasStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenbundleFrameAffineAtlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)), PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_atlas | exact GlobalTheory.FlagMod.FieldFlag.exists_atlas | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_atlas <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.PolOpen

section
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end

theorem mem_abLocus_of_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) (s : S')
    (hs : s ∈ abLocus ((Over.pullback j).obj G)) : j s ∈ abLocus G := by
  rintro K _ _ t ⟨p, hp⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range t ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ⟨s, by rw [Subsingleton.elim q p, hp]⟩
  let t' := IsOpenImmersion.lift j t hr
  have ht : t' ≫ j = t := IsOpenImmersion.lift_fac _ _ _
  have hp' : t' p = s := j.isOpenEmbedding.injective ((congrArg (fun q => q p) ht).trans hp)
  have h₁ : IsProper (pullback.snd (pullback.snd G.hom j) t') := hs K t' ⟨p, hp'⟩
  have h₂ := (IsPullback.of_hasPullback (pullback.snd G.hom j) t').paste_horiz (IsPullback.of_hasPullback G.hom j)
  rw [ht] at h₂
  rw [← h₂.isoPullback_inv_snd]
  infer_instance

theorem polOnAb_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (L : LB G.left)
    (hL : L.IsLB) (h : PolOnAb G L) : PolOnAb ((Over.pullback j).obj G) (L.pull (pullback.fst G.hom j)) := by
  intro W' hW'
  obtain ⟨ha, hK⟩ := h (j ''ᵁ W') (by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_abLocus_of_open j G s (hW' hs))
  have hr : Set.range (W'.ι ≫ j) ⊆ Set.range (j ''ᵁ W').ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  let e := IsOpenImmersion.lift (j ''ᵁ W').ι (W'.ι ≫ j) hr
  have he : e ≫ (j ''ᵁ W').ι = W'.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (e ≫ (j ''ᵁ W').ι) := by rw [he]; infer_instance
  have : IsOpenImmersion e := IsOpenImmersion.of_comp e (j ''ᵁ W').ι
  have p₀ := isGrpPullback_pullback G (j ''ᵁ W').ι
  have p₁ := (isGrpPullback_pullback ((Over.pullback j).obj G) W'.ι).comp (isGrpPullback_pullback G j)
  have w₁ := p₁.1.w.trans ((congrArg _ he.symm).trans (Category.assoc _ _ _).symm)
  have p₂ := IsGrpPullback.cancel p₀ (p₁.congr he.symm (p₀.1.lift_fst _ _ w₁).symm) (p₀.1.lift_snd _ _ w₁)
  have hL₀ := pull_isLB hL (pullback.fst G.hom (j ''ᵁ W').ι)
  have hL₁ := pull_isLB (pull_isLB hL (pullback.fst G.hom j)) (pullback.fst ((Over.pullback j).obj G).hom W'.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.pull (pullback.fst G.hom j)).pull (pullback.fst ((Over.pullback j).obj G).hom W'.ι))
      ((L.pull (pullback.fst G.hom (j ''ᵁ W').ι)).pull (p₀.1.lift _ _ w₁)) := by
    refine (CechPic.cls_eq_iff hL₁ (pull_isLB hL₀ _)).1 ?_
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL]
    exact (CechPic.pull_comp _ _ _).symm.trans ((congrArg (fun q => CechPic.pull q _) (p₀.1.lift_fst _ _ w₁).symm).trans
      (CechPic.pull_comp _ _ _))
  exact ⟨relAmple_pull_of_affine p₂.1 hL₀ hL₁ ((isGen_iff w).1 hw)
    (fun U' hU' => ⟨e ''ᵁ U', hU'.image_of_isOpenImmersion e, fun y hy => ⟨y, hy, rfl⟩⟩) ha,
    kTriv_pull p₂ hL₀ hL₁ ((isGen_iff w).1 hw) hK⟩

theorem polOnAb_affine : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsOpen (abLocus G) → PolOnAb G L.L → PolOnAb (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW _ h => polOnAb_open hW.fromSpec G L.L L.isLB h

end GlobalTheory.KeyVals.PolOpen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisationOnAbLocus_restrict_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsOpen (abLocus G) → PolOnAb G L.L → PolOnAb (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L := by
  first | exact @GlobalTheory.KeyVals.PolOpen.polOnAb_affine | exact GlobalTheory.KeyVals.PolOpen.polOnAb_affine | (intros; apply GlobalTheory.KeyVals.PolOpen.polOnAb_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendIntegralPadicEvaluationGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfExtension
namespace GlobalTheory.NormExtensionBound

open scoped Pointwise

theorem exists_extension {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (ev : A →+* K) : ∃ ev' : B →+* K, ∀ a, ev' (algebraMap A B a) = ev a := by
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker ev) ⊥ (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ (B ⧸ Q) (by rw [h, map_zero])
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) K :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ K (by rw [h, map_zero])
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let f : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker ev] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  have h := f.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem norm_le_one_of_extension {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (ev : A →+* PadicAlgCl p) (h : ∀ a, ‖ev a‖ ≤ 1)
    (ev' : B →+* PadicAlgCl p) (hev : ∀ a, ev' (algebraMap A B a) = ev a) (b : B) :
    ‖ev' b‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hcomp : ev'.comp (algebraMap A B) = ev := RingHom.ext hev
  have hq' := congrArg ev' hq
  rw [map_zero, Polynomial.hom_eval₂, hcomp, hqm.as_sum, Polynomial.eval₂_add,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hq'
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq'
  set y := ev' b
  by_contra hy
  push_neg at hy
  have hxn : y ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i :=
    eq_neg_of_add_eq_zero_left hq'
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hy1 : 1 ≤ ‖y‖ := hy.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖ev (q.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (q.natDegree - 1) :=
          mul_le_mul (h _) (pow_le_pow_right₀ hy1 (by omega)) (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖y‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖y‖ ^ q.natDegree ≤ ‖y‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖y‖ ^ (q.natDegree - 1) < ‖y‖ ^ q.natDegree := pow_lt_pow_right₀ hy (by omega)
  linarith

theorem main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (A B : Type) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)]
    (𝔷 : Ideal B), Function.Injective (algebraMap A B) →
    (∀ (b : B), (∀ (σ : B ≃ₐ[A] B), σ b = b) → b ∈ Set.range (algebraMap A B)) →
    Ideal.IsMaximal 𝔷 → ∀ (ev : A →+* PadicAlgCl p), (∀ (a : A), ‖ev a‖ ≤ (1 : ℝ)) →
    (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < (1 : ℝ)) →
    ∃ (ev' : B →+* PadicAlgCl p), (∀ (a : A), ev' (algebraMap A B a) = ev a) ∧
      (∀ (b : B), ‖ev' b‖ ≤ (1 : ℝ)) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < (1 : ℝ) := by
  intro p _ A B _ _ _ _ _ _ _ 𝔷 hinj hfix hmax ev h1 h2
  obtain ⟨e, he⟩ := exists_extension hinj ev
  have hle := norm_le_one_of_extension ev h1 e he
  let m : Ideal B :=
    { carrier := {b | ‖e b‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖e (a + b)‖ < 1
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        show ‖e (c * b)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hb }
  have hm : ∀ b, b ∈ m ↔ ‖e b‖ < 1 := fun _ => Iff.rfl
  have hmne : m ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hm]
    simp
  have hmu : m.under A = IsLocalRing.maximalIdeal A := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hmne)
    intro a ha
    rw [Ideal.mem_comap, hm, he]
    exact h2 a ha
  haveI hmm : m.IsPrime := ⟨hmne, fun {a b} hab => by
    rw [hm, map_mul, norm_mul] at hab
    by_contra hc
    rw [not_or, hm, hm, not_lt, not_lt] at hc
    exact absurd hab (not_lt.2 (one_le_mul_of_one_le_of_one_le hc.1 hc.2))⟩
  have hzu : 𝔷.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) 𝔷)
  haveI : Algebra.IsInvariant A B (B ≃ₐ[A] B) := ⟨fun b hb => hfix b hb⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B (B ≃ₐ[A] B) 𝔷 m
    (hzu.trans hmu.symm)
  refine ⟨e.comp (g : B →+* B), fun a => ?_, fun b => hle _, fun b hb => ?_⟩
  · simp [he]
  · have : g • b ∈ m := by
      rw [hg]
      exact Ideal.smul_mem_pointwise_smul g b 𝔷 hb
    exact this

end GlobalTheory.NormExtensionBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendIntegralPadicEvaluationGalois
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ValExt

theorem exists_ext_centred : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B), Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → 𝔷.IsMaximal → ∀ ev : A →+* PadicAlgCl p, (∀ a, ‖ev a‖ ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < 1) → ∃ ev' : B →+* PadicAlgCl p, (∀ a, ev' (algebraMap A B a) = ev a) ∧ (∀ b, ‖ev' b‖ ≤ 1) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.NormExtensionBound.main
  | exact _root_.GlobalTheory.NormExtensionBound.main
  | (apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormExtensionBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormExtensionBound.main ..)

end GlobalTheory.ValExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendIntegralPadicEvaluationGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_integral_padic_evaluation_galois : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B), Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → 𝔷.IsMaximal → ∀ ev : A →+* PadicAlgCl p, (∀ a, ‖ev a‖ ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < 1) → ∃ ev' : B →+* PadicAlgCl p, (∀ a, ev' (algebraMap A B a) = ev a) ∧ (∀ b, ‖ev' b‖ ≤ 1) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < 1 := by
  first | exact @GlobalTheory.ValExt.exists_ext_centred | exact GlobalTheory.ValExt.exists_ext_centred | (intros; apply GlobalTheory.ValExt.exists_ext_centred <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TopForm

namespace FrameBasis

theorem bijective_of_isFreeGen {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A) {m : ℕ}
    (hA : α.IsStandardSmoothOfRelativeDimension m) (x : Fin m → A)
    (hx : IsFreeGen A (dForm α x)) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension m k A := hA
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Omega α)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = m := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) m)
    let b := Module.finBasisOfFinrankEq A (Omega α) hr
    let v : Fin m → Omega α := fun i => dFun α (x i)
    obtain ⟨a, ha⟩ := hx.2 (exteriorPower.ιMulti A m b)
    have e := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) ha
    simp only [map_smul, dForm_eq, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, smul_eq_mul] at e
    have hu : IsUnit (b.det v) := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact e)
    obtain ⟨hli, hsp⟩ := (b.is_basis_iff_det).2 hu
    let b' := Module.Basis.mk hli hsp.ge
    have : (Fintype.linearCombination A fun i => dFun α (x i)) = b'.equivFun.symm.toLinearMap := by
      ext c
      simp [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply, b', v]
    rw [this]
    exact b'.equivFun.symm.bijective

end FrameBasis

end TopForm

end GlobalTheory

namespace GlobalTheory.TopForm.FrameBasis

theorem bijective_of_isLocalization_span {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {m : ℕ} (x : Fin m → A) (s : Set A) (hs : Ideal.span s = ⊤) (B : s → Type*)
    [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)] [∀ t : s, IsLocalization.Away t.1 (B t)]
    (H : ∀ t : s, Function.Bijective (Fintype.linearCombination (B t)
      fun i => dFun ((algebraMap A (B t)).comp α) (algebraMap A (B t) (x i)))) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  letI (t : s) : Algebra k (B t) := ((algebraMap A (B t)).comp α).toAlgebra
  haveI (t : s) : IsScalarTower k A (B t) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (t : s) : Algebra.FormallyEtale A (B t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t.1)
  let g : ∀ t : s, Ω[A⁄k] →ₗ[A] Ω[B t⁄k] := fun t => KaehlerDifferential.map k k A (B t)
  haveI H₁ (t : s) : IsLocalizedModule.Away t.1 (g t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (g t)).2
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A (B t))
  let π : ∀ t : s, (Fin m → A) →ₗ[A] (Fin m → B t) := fun t => (Algebra.linearMap A (B t)).compLeft (Fin m)
  haveI H₂ (t : s) : IsLocalizedModule.Away t.1 (π t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (π t)).2
      (IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap A (B t)))
  let e : ∀ t : s, (Fin m → B t) ≃ₗ[A] Ω[B t⁄k] := fun t =>
    (LinearEquiv.ofBijective _ (H t)).restrictScalars A
  haveI H₃ (t : s) : IsLocalizedModule.Away t.1 ((e t).toLinearMap ∘ₗ π t) :=
    IsLocalizedModule.of_linearEquiv _ _ _
  have hcomp (t : s) : g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i)) =
      (e t).toLinearMap ∘ₗ π t := by
    ext c
    simp [g, e, π, Fintype.linearCombination_apply, algebraMap_smul]
  haveI H₄ (t : s) : IsLocalizedModule.Away t.1
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) := by
    rw [hcomp t]; exact H₃ t
  refine bijective_of_isLocalized_span s hs (fun t => Ω[B t⁄k])
    (fun t => g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (fun t => Ω[B t⁄k]) g
    (Fintype.linearCombination A fun i => dFun α (x i)) fun t => ?_
  have : IsLocalizedModule.map (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t)
      (Fintype.linearCombination A fun i => dFun α (x i)) = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id

end GlobalTheory.TopForm.FrameBasis

namespace GlobalTheory.TopForm.FrameBasis

theorem exists_basis_of_isFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ),
    SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)),
    GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) →
    ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)),
      ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  intro k _ X p m hp U x hx
  have hU := hx.affine
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  haveI (t : (s : Set Γ(X, U))) := hU.isLocalization_basicOpen t.1
  have hbij : Function.Bijective
      (Fintype.linearCombination Γ(X, U) fun i => dFun (algX p U) (x i)) := by
    refine bijective_of_isLocalization_span (algX p U) x (s : Set Γ(X, U)) hs
      (fun t => Γ(X, X.basicOpen t.1)) fun t => ?_
    have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      (h t t.2 Γ(X, X.basicOpen t.1))
    have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen t.1)).comp (algX p U) =
        algX p (X.basicOpen t.1) := resG_comp_algX p (X.basicOpen_le t.1)
    have h₂ : (algX p (X.basicOpen t.1)).IsStandardSmoothOfRelativeDimension m := by
      rw [← resG_comp_algX p (X.basicOpen_le t.1)]
      exact h₁
    have hfr := (hx.res (hU.basicOpen t.1) (X.basicOpen_le t.1)).gen
    rw [resForm_dOn] at hfr
    have := bijective_of_isFreeGen _ h₂ _ hfr
    rw [e]
    exact this
  let eq := LinearEquiv.ofBijective _ hbij
  refine ⟨Module.Basis.ofEquivFun eq.symm, fun i => ?_⟩
  simp [eq, Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply, Pi.single_apply]

end GlobalTheory.TopForm.FrameBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrameStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kaehlerBasis_differentials_of_topFormFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ), SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)), GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) → ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)), ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  first | exact @GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame | exact GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame | (intros; apply GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoordsOrigin

instance isLocalRing_dualNumber (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 h)
    · exact Or.inr ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by simpa using h))

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

theorem one_left (X : Over (Sp R)) : (1 : X ⟶ G).left = X.hom ≫ (η[G]).left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

variable [IsCommMonObj G]

theorem tv_closedPoint (v : TanM (𝟙 (Sp R)) G) :
    (tv v).left (IsLocalRing.closedPoint (DualNumber R)) = origin G := by
  have h := congrArg (fun w => w.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  simp only [smT_left, one_left] at h
  have hl0 : IsLocalHom (epsMul (0 : R)) := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hl1 : IsLocalHom (algebraMap R (DualNumber R)) := ⟨fun a ha => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha⟩
  have e0 : (spMap (epsMul (0 : R))) (IsLocalRing.closedPoint (DualNumber R)) = IsLocalRing.closedPoint (DualNumber R) :=
    Spec_closedPoint (f := CommRingCat.ofHom (epsMul (0 : R)))
  have e1 : (spMap (algebraMap R (DualNumber R))) (IsLocalRing.closedPoint (DualNumber R)) = IsLocalRing.closedPoint R :=
    Spec_closedPoint (f := CommRingCat.ofHom (algebraMap R (DualNumber R)))
  have h2 := congrArg (fun φ => φ (IsLocalRing.closedPoint (DualNumber R))) h
  have h3 : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) =
      (tv v).left ((spMap (epsMul (0 : R))) (IsLocalRing.closedPoint (DualNumber R))) :=
    (congrArg (fun y => (tv v).left y) e0).symm
  rw [h3]
  refine h2.trans ?_
  exact congrArg (fun y => (η[G]).left y) e1


open Classical in
def tanDer (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)) : R :=
  if h : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) = origin G then
    (((G.left.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left).hom f).snd
  else 0

theorem tanDer_eq (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)) :
    tanDer G v f = (((G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left).hom f).snd := by
  rw [tanDer, dite_eq_left (tv_closedPoint G v)]

end GlobalTheory.CoordsOrigin
end
end

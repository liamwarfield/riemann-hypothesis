module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagQuotientIntegralEqUniversalConstMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.ChartSmooth

theorem isStandardSmooth_C (k : Type) [CommRing k] (D : ℕ) :
    (algebraMap k (MvPolynomial (Fin D) k)).IsStandardSmoothOfRelativeDimension D := by
  haveI : IsEmpty Empty := ⟨Empty.elim⟩
  let P₀ : Algebra.Presentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial k (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2
    (P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension]))

theorem isStandardSmooth_algX {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (x : Fin D → Γ(X, U)) (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (algX p U).IsStandardSmoothOfRelativeDimension D := by
  have hC : (MvPolynomial.eval₂Hom (algX p U) x).comp (algebraMap k _) = algX p U :=
    RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  have h := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 hx).comp
    (isStandardSmooth_C k D)
  rwa [hC, zero_add] at h

theorem smooth_of_etale {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (hU : IsAffineOpen U) (x : Fin D → Γ(X, U))
    (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have hA : IsAffine U.toScheme := hU
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv (isStandardSmooth_algX p x hx)
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    U.topIso.symm.commRingCatIsoToRingEquiv h₁
  refine (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension D)).2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_)
  have e : (U.ι ≫ p).appTop = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp) ≫ U.topIso.inv := by
    rw [Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Opens.topIso_inv,
      Scheme.Opens.ι_app, Category.assoc]
    exact (congrArg (p.app ⊤ ≫ ·) (Eq.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
      (X.presheaf.map_comp _ _))).trans (Category.assoc _ _ _).symm
  rw [e]
  exact h₂

end GlobalTheory.ChartSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinor
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory

theorem unitMinorSet_rank_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  intro k _ _ _ _ n d Y hY
  obtain ⟨-, f, hf⟩ := hY
  have hdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  have hunit : IsUnit (Y.submatrix id f) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsub : (Y.submatrix id f).rank = n := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  have hmul : Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f = Y.submatrix id f := by
    rw [Matrix.mul_submatrix_one]; rfl
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (Y.submatrix id f).rank := hsub.symm
    _ = (Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f).rank := by rw [hmul]
    _ ≤ Y.rank := Matrix.rank_mul_le_left _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinorStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_unit_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  first | exact @GlobalTheory.unitMinorSet_rank_eq | exact GlobalTheory.unitMinorSet_rank_eq | (intros; apply GlobalTheory.unitMinorSet_rank_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernel
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

theorem mem_augRk_of_fibre_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hnd hν Ψ hΨ hT
  have hT' : ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n →
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = 0 := fun Y hY => by
    obtain ⟨h, rfl⟩ := GlobalTheory.T.full_rank_normal_form_orbit k n d hnd Y hY
    exact hT h
  obtain ⟨s, hs⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d _ (GlobalTheory.T.isClopen_unit_minor_set k n d).isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ hΨ
  obtain ⟨Φ, hΦ, hS, hdiff, hF⟩ := GlobalTheory.T.clopen_integrability_full_rank_orbit k n d ν _ (GlobalTheory.T.isClopen_unit_minor_set k n d)
    (fun Φ hΦ Y => GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ hΦ Y) s Ψ hΨ hs
  have hA := GlobalTheory.T.smooth_character_orbital_integral_stable k n d ν hν _ (GlobalTheory.T.integral_group_of_unit_minor_stable k n d) (fun E hE Y hY => GlobalTheory.T.unit_minor_stable_integral_group k n d E Y hE hY) Φ hΦ hS
    (fun Y hY => by rw [hF]; exact hT' Y (GlobalTheory.T.rank_eq_of_unit_minor k n d Y hY))
  have e : Ψ = (Ψ - Φ) + Φ := by abel
  rw [e]; exact add_mem hdiff hA

end GlobalTheory.FullRankCoinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernelStatement
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_zeta_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  exact @GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasis
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.FlagBasis

theorem exists_coeff {C U : Type} [Field C] [AddCommGroup U] [Module C U] {n : ℕ} (b : Fin n → U) (i : ℕ)
    {y : U} (hy : y ∈ step C b i) : ∃ r : Fin n → C, (∀ j : Fin n, i ≤ j → r j = 0) ∧ ∑ j, r j • b j = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun j hj => Pi.single_eq_of_ne ?_ _, by simp [Pi.single_apply]⟩
    rintro rfl
    exact absurd hk (not_lt.2 hj)
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, fun j hj => by simp [hr j hj, hs j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a • r, fun j hj => by simp [hr j hj], by simp [Finset.smul_sum, smul_smul]⟩

theorem exists_lift {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {La : Submodule O U} (hfg : La.FG)
    {b : Fin n → U} (hb : LinearIndependent C b) (i : Fin n) {a : C} (ha : a ≠ 0) (hLa : a • b i ∈ La) :
    ∃ (w : U) (c : C), c ≠ 0 ∧ w ∈ La ∧ w - c • b i ∈ step C b i ∧
      ∀ x ∈ La, x ∈ step C b (i + 1) → ∃ o : O, x - o • w ∈ step C b i := by
  obtain ⟨c, hc, e, -⟩ := exists_grAt_eq hv hfg b i (hb.notMem_span_image (by simp)) ha
    (Submodule.zero_mem _) (by rwa [add_zero])
  obtain ⟨w, hw, hw'⟩ : c • (step C b i).mkQ (b i) ∈ grAt C La b i :=
    e ▸ Submodule.mem_span_singleton_self _
  have hw'' : (step C b i).mkQ w = c • (step C b i).mkQ (b i) := hw'
  refine ⟨w, c, hc, hw.1, (Submodule.Quotient.eq _).1 hw'', fun x hx hx' => ?_⟩
  have h1 : (step C b i).mkQ x ∈ grAt C La b i := ⟨x, ⟨hx, hx'⟩, rfl⟩
  rw [e, ← hw''] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h1
  exact ⟨o, (Submodule.Quotient.eq _).1 ho.symm⟩

theorem exists_adapted_basis : ∀ (O C U : Type) [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (v : Valuation C ℝ≥0), v.Integers O → ∀ (n : ℕ) (La : Submodule O U), La.FG → ∀ b : Fin n → U, LinearIndependent C b → (∀ j, ∃ a : C, a ≠ 0 ∧ a • b j ∈ La) → ∃ g : Matrix (Fin n) (Fin n) C, (∀ i j, i < j → g i j = 0) ∧ (∀ i, g i i ≠ 0) ∧ IsLatBasis C La fun i => ∑ j, g i j • b j := by
  intro O C U _ _ _ _ _ _ _ v hv n La hfg b hb hLa
  classical
  choose a ha hLa using hLa
  choose w c hc hw hwb hgen using fun i => exists_lift hv hfg hb i (ha i) (hLa i)
  choose r hr hrb using fun i => exists_coeff b _ (hwb i)
  let g : Matrix (Fin n) (Fin n) C := fun i j => r i j + if j = i then c i else 0
  have hg : ∀ i j, i < j → g i j = 0 := fun i j h => by
    simp [g, hr i j h.le, h.ne']
  have hd : ∀ i, g i i ≠ 0 := fun i => by simpa [g, hr i i le_rfl] using hc i
  have hgw : (fun i => ∑ j, g i j • b j) = w := funext fun i => by
    simp [g, add_smul, Finset.sum_add_distrib, hrb]
  have hws : ∀ i : Fin n, w i ∈ step C b (i + 1) := fun i => by
    simpa using Submodule.add_mem _ (step_mono b (Nat.le_succ _) (hwb i))
      (Submodule.smul_mem _ (c i) (mem_step_succ b i))
  refine ⟨g, hg, hd, ?_, ?_⟩
  · have hu : IsUnit g := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ fun i j hij => hg i j hij]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
    exact (Matrix.linearIndependent_rows_iff_isUnit.2 hu).map' (Fintype.linearCombination C b)
      (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hb s t h))
  · rw [hgw]
    refine le_antisymm (le_inf (Submodule.span_le.2 (Set.range_subset_iff.2 hw))
      (Submodule.span_le_restrictScalars O C _)) ?_
    have key : ∀ k, k ≤ n → ∀ x ∈ La, x ∈ step C b k → x ∈ Submodule.span O (Set.range w) := by
      intro k
      induction k with
      | zero =>
        intro _ x _ hx
        rw [step_zero, Submodule.mem_bot] at hx
        exact hx ▸ Submodule.zero_mem _
      | succ k ih =>
        intro hk x hx hx'
        obtain ⟨o, ho⟩ := hgen ⟨k, hk⟩ x hx hx'
        have h1 := ih (Nat.le_of_succ_le hk) _ (La.sub_mem hx (La.smul_mem o (hw _))) ho
        simpa using Submodule.add_mem _ h1
          (Submodule.smul_mem _ o (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
    rintro x ⟨hx, hx'⟩
    exact key n le_rfl x hx (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
      step_mono b (Nat.succ_le_of_lt i.2) (hws i)) hx')

end GlobalTheory.CompHt.FlagBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSets
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section
namespace GlobalTheory.LevGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem adelicProb_mul_volFund : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ ∀ Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (Φ k)) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x) → (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x) → (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ x0 FF hFF
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  have hvp := Formalism.L2.Pj.volPair_isVolPair (D.sp.W j) hP
  haveI : (Formalism.L2.Pj.volPair (D.sp.W j)).1.IsHaarMeasure := hvp.1.1
  have h0 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ 0 :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.1
  have h1 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ ⊤ :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.2
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU := hL.unf σ hσ
  have hΨ : ∀ k k', ((U σ).X k).Ψ = ((U σ).X k').Ψ ∧ ((U σ).X k).p0 = ((U σ).X k').p0 := fun k k' =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm, (hU.2.1 k).1.trans (hU.2.1 k').1.symm⟩
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨κ, hκ0, hκ1, hI⟩ := GlobalTheory.PeterssonCompare.lintegral_adelic (D.sp.W j) (U σ).X (dict σ) hM hth hd hK hu hΨ
    _ hvp.2 h0 h1
  set k0 := (dict σ 1).1
  obtain ⟨κ2, h20, h21, hH⟩ := GlobalTheory.T.flagQuotientIntegral_eq_universal_const_mul D.R.r Dw.q ((U σ).X k0).Ψ.card
  have hQ : ∀ k (F : Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞), Measurable F →
      (∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F (lact γ x) = F x) →
      (∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F (rmul x b) = F x) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) F = κ2 * ∫⁻ z in FF k, F (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) :=
    fun k F hF hΓ hB => hH D.host.E ((U σ).X k) (hU.2.1 k).1 (by rw [(hΨ k k0).1]) (x0 k) (FF k) F (hFF k).1 (hFF k).2
      hF hΓ hB
  have key : ∀ F : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F k (rmul x b) = F k x) →
      ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j)) =
        ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
          (κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k)) := by
    intro F hF hΓ hB
    obtain ⟨h2, h3⟩ := hI F hF hΓ hB
    have hout : ∀ g, F (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).1 (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).2 =
        F (dict σ g).1 (dict σ g).2 := by
      intro g
      have h4 : g * (Formalism.L2.Pj.autMk (D.sp.W j) g).out⁻¹ ∈ GQ (D.sp.W j) :=
        QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
      obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 (Formalism.L2.Pj.autMk (D.sp.W j) g).out
      rw [inv_mul_cancel_right] at e
      rw [e]
      exact (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
    have hq : Measurable fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2 := by
      rw [measurable_from_quotient]
      have : ((fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2) ∘ Quotient.mk'') =
          fun g => F (dict σ g).1 (dict σ g).2 := funext hout
      rw [this]
      exact h2
    have h5 : ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(Formalism.L2.Pj.muQ (D.sp.W j)) =
        κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k) := by
      rw [Formalism.L2.Pj.muQ, lintegral_map hq (Formalism.L2.Pj.autMk_measurable (D.sp.W j))]
      simp only [hout]
      exact h3
    rw [Formalism.L2.Pj.muQ1, if_pos (show Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ 0 ∧ Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ ⊤
      from hV), lintegral_smul_measure, h5, Formalism.L2.Pj.muQ_univ, smul_eq_mul]
  have e1 := key (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_congr rfl fun k _ => hQ k (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl),
    ← Finset.mul_sum] at e1
  simp only [setLIntegral_one, lintegral_const, measure_univ, mul_one, one_mul, Measure.restrict_apply_univ] at e1
  have hv0 : ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h1
  refine ⟨fun hS => ?_, fun hS => ?_, fun Φ hΦ hΓ hB => ?_⟩
  · rw [hS, mul_zero, mul_zero, mul_zero] at e1
    exact one_ne_zero e1
  · rw [hS, ENNReal.mul_top h20, ENNReal.mul_top hκ0, ENNReal.mul_top hv0] at e1
    exact ENNReal.one_ne_top e1
  · rw [key Φ hΦ hΓ hB, Finset.sum_congr rfl fun k _ => hQ k (Φ k) (hΦ k) (hΓ k) (hB k), ← Finset.mul_sum]
    calc _ = (∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) *
          (((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
            (κ * (κ2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k)))) := by ring
      _ = _ := by rw [← e1, mul_one]

end GlobalTheory.LevGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSetsStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicProbability_eq_normalised_fundamentalSets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ ∀ Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (Φ k)) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x) → (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x) → (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) := by
  first | exact @GlobalTheory.LevGeo.adelicProb_mul_volFund | exact GlobalTheory.LevGeo.adelicProb_mul_volFund | (intros; apply GlobalTheory.LevGeo.adelicProb_mul_volFund <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVariety
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalOpen

theorem exists_mul_isInteger (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ f : A, f ≠ 0 ∧ ∀ y : K, IsIntegral A y → ∃ a : A, algebraMap A K a = f • y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A K => (z : K))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun y hy => ?_⟩
  have key : ∀ z ∈ Submodule.span A (s : Set (integralClosure A K)),
      ∃ a : A, algebraMap A K a = (b : A) • (z : K) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hb _ (Finset.mem_image_of_mem _ hx)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [map_add (f := _), ha, hc, Subalgebra.coe_add, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_mul, ha, Subalgebra.coe_smul, smul_comm, ← Algebra.smul_def]
  exact key ⟨y, hy⟩ (hs ▸ Submodule.mem_top)

theorem exists_isIntegrallyClosed_away (A : Type*) [CommRing A] [IsDomain A]
    [Module.Finite A (integralClosure A (FractionRing A))] :
    ∃ f : A, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let K := FractionRing A
  obtain ⟨f, hf, h⟩ := exists_mul_isInteger A K
  refine ⟨f, hf, ?_⟩
  let B := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hg : ∀ y : Submonoid.powers f, IsUnit (algebraMap A K y) := fun y =>
    IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ hle
  letI : Algebra B K := (IsLocalization.lift (S := B) hg).toAlgebra
  have : IsScalarTower A B K := .of_algebraMap_eq fun a => (IsLocalization.lift_eq hg a).symm
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B K
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers f)
    (Rₘ := B) x hx
  obtain ⟨a, ha⟩ := h _ hm
  let t : Submonoid.powers f := ⟨f, Submonoid.mem_powers f⟩ * m
  refine ⟨IsLocalization.mk' B a t, ?_⟩
  have e := congrArg (algebraMap B K) (IsLocalization.mk'_spec B a t)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at e
  refine (hg t).mul_right_cancel ?_
  rw [e, mul_comm, ← Algebra.smul_def, Submonoid.smul_def, smul_smul]
  rfl

theorem exists_normal_opens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  intro k _ X p D h
  have := h.isIntegral
  have := h.finite
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, hft, -⟩ := RegGenSmooth.chart_props h i hi
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance hft
  have := finite_integralClosure_of_essFiniteType_int A
  obtain ⟨f, hf, hc⟩ := exists_isIntegrallyClosed_away A
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hB : GlobalTheory.IsNormalScheme (Sp B) := GlobalTheory.IsNormalScheme.spec (.of B)
  have : GlobalTheory.IsNormalScheme j.opensRange.toScheme := .of_isIso j.isoOpensRange.hom
  refine ⟨j.opensRange, ?_, GlobalTheory.IsNormalScheme.pred _⟩
  exact ⟨j (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), _, rfl⟩

end GlobalTheory.NormalOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  first | exact @GlobalTheory.NormalOpen.exists_normal_opens | exact GlobalTheory.NormalOpen.exists_normal_opens | (intros; apply GlobalTheory.NormalOpen.exists_normal_opens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAdd
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LamSpread


open Classical in
def sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) : ℕ := ∑ i : Fin (Dw.mult b), a (b, i)

theorem le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult b) : a (b, i) ≤ sumA Dw a b :=
  Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => a (b, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨i, hi⟩ : Fin (Dw.mult b)))

theorem spread_le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 0 < r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (k : U.Comp) (τ : (U.X k).Ψ) :
    (U.X k).spread (laU U a n k) τ ≤ (sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1)) + n := by
  have hsurj : Function.Surjective (relab (E := E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hrr := hU.1
  obtain ⟨ρ, hρ⟩ := hsurj τ.1
  have hρΨ : ρ (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (GlobalTheory.AllWt.conj_mem hn))).trans hσ0
    rw [GlobalTheory.AllWt.relab_conj, hρ] at h3
    exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
  have e1 : Function.invFun (relab c σ) τ.1 = ρ := by
    rw [← hρ]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) ρ
  have e2 : Function.invFun (relab c σ) (conjEmb τ.1) = conjEmb ρ := by
    rw [← hρ, ← GlobalTheory.AllWt.relab_conj]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) _
  have m1 : Dw.mult ρ = Dw.p := by rw [Datum.mult, if_pos hρΨ]
  have m2 : Dw.mult (conjEmb ρ) = Dw.q := by rw [Datum.mult, if_neg (GlobalTheory.AllWt.conj_not_mem ⟨ρ, hρΨ⟩)]
  rw [e1, e2]
  have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
    have : n / 2 + n / 2 ≤ n := by omega
    exact_mod_cast this
  have key : ∀ i : Fin r, -((sumA Dw a (conjEmb ρ) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
      laU U a n k τ i ≤ (sumA Dw a ρ : ℤ) + ((n / 2 : ℕ) : ℤ) := by
    intro i
    have hi' := i.isLt
    unfold laU
    rw [e1, e2]
    split_ifs with hi
    · have := le_sumA Dw a ρ ((i : ℕ) - (U.X k).p0) (by rw [m1]; omega)
      constructor <;> omega
    · have := le_sumA Dw a (conjEmb ρ) ((U.X k).p0 - 1 - (i : ℕ)) (by rw [m2]; omega)
      constructor <;> omega
  refine (GlobalTheory.WtSizes.spread_le hr _ ((sumA Dw a ρ : ℝ) + ((n / 2 : ℕ) : ℝ))
    ((sumA Dw a (conjEmb ρ) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_spread_laU_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : (U σ).Comp), (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
  intro D j H Dw l Xo c U dict hL σ hσ a n k
  have hU := hL.unf σ hσ
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hsurj : Function.Surjective (relab (E := D.host.E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  have hgb : Function.Bijective (Function.invFun (relab c σ)) :=
    Finite.injective_iff_bijective.1 (Function.LeftInverse.injective (Function.rightInverse_invFun hsurj))
  refine (Finset.sum_le_sum fun τ _ => spread_le_sumA (U σ) hσ hU hr a n k τ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (U σ).X k),
    nsmul_eq_mul]
  have h1 : ∑ τ : ((U σ).X k).Ψ, ((sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1))) ≤ absA Dw a := by
    have := GlobalTheory.WtSizes.sum_cm_le ((U σ).X k) (fun b => sumA Dw a (Function.invFun (relab c σ) b))
    rw [hgb.sum_comp (fun b => sumA Dw a b)] at this
    show _ ≤ ((∑ b, sumA Dw a b : ℕ) : ℝ)
    exact_mod_cast this
  have h2 : (fdeg D.host.E : ℝ) * n ≤ ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
    have : fdeg D.host.E * n ≤ fdeg D.host.E * D.R.r * n :=
      Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right _ hr)
    exact_mod_cast this
  linarith

end GlobalTheory.LamSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAddStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_weightSpread_le_exponentNorm_add : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : (U σ).Comp), (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
  first | exact @GlobalTheory.LamSpread.sum_spread_laU_le | exact GlobalTheory.LamSpread.sum_spread_laU_le | (intros; apply GlobalTheory.LamSpread.sum_spread_laU_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinClAndGamOrd
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.ClassFin

variable {D : D7}

def gfcToGf (V : HSp D) : GfC V →* Bridge.Gf V := (finHom V).rangeRestrict.comp (GfC V).subtype

theorem gfcToGf_surjective (V : HSp D) : Function.Surjective (gfcToGf V) := by
  rintro ⟨_, h, rfl⟩
  obtain ⟨k, hk, e⟩ := GlobalTheory.VolHeckeCompare.exists_finite_part V h
  exact ⟨⟨k, hk⟩, Subtype.ext e⟩

theorem bc_swapAE_injective (n : ℕ) :
    Function.Injective (Formalism.UG.bc (Lev.swapAE D) : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →* _) := by
  intro a b e
  apply Units.ext
  have h := congrArg Units.val e
  exact Matrix.map_injective (f := Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finG_injective (V : HSp D) : Function.Injective (finG V) := by
  intro a b e
  have e' : finHom V a.1 = finHom V b.1 := bc_swapAE_injective V.rank e
  have h1 : finHom V (a.1⁻¹ * b.1) = 1 := by rw [map_mul, map_inv, e', inv_mul_cancel]
  have := GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (mul_mem (inv_mem a.2) b.2) h1
  exact Subtype.ext (inv_mul_eq_one.1 this)

def finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (K.comap (Formalism.UG.bc (Lev.swapAE D))).comap (Bridge.Gf V).subtype

theorem mem_finLev_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (g : GfC V) :
    gfcToGf V g ∈ finLev V K ↔ g ∈ K.comap (finG V) := Iff.rfl

theorem isOpenLev_finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsCO V K) :
    GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V (finLev V K) := by
  have e : (((finLev V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) =
      ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
  rw [e]
  exact hK.1

theorem finite_finCl (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) : Finite (FinCl V K) := _root_.GlobalTheory.FunObj.finite_finCl V K hV hK

theorem continuous_finHom (V : HSp D) : Continuous (finHom V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  exact (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ

theorem gamOrd_ne_zero (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) (x : GfC V) : gamOrd V K x ≠ 0 := _root_.GlobalTheory.FunObj.gamOrd_ne_zero V K hV hK x

theorem finite_finCl_and_gamOrd : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))),
    (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) → IsCO V K → Finite (FinCl V K) ∧ ∀ x, gamOrd V K x ≠ 0 :=
  fun V K hV hK => ⟨finite_finCl V K (fun τ => hV (tauE _ τ)) hK, gamOrd_ne_zero V K (fun τ => hV (tauE _ τ)) hK⟩

end GlobalTheory.FunObj.ClassFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CongW.PlaceEmb

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_isIntegral_int {x : PadicAlgCl p} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := PadicAlgCl p)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl p))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_int_le (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : ‖σ (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int σ (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (σ : K →+* PadicAlgCl p) : Ideal (𝓞 K) where
  carrier := {y | ‖σ (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : σ ((a + b : 𝓞 K) : K) = σ (a : K) + σ (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : σ ((c • a : 𝓞 K) : K) = σ (c : K) * σ (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le σ c
    nlinarith [norm_nonneg (σ (c : K)), norm_nonneg (σ (a : K))]

theorem mem_smallIdeal (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : y ∈ smallIdeal σ ↔ ‖σ (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (σ : K →+* PadicAlgCl p) : (smallIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : σ ((a * b : 𝓞 K) : K) = σ (a : K) * σ (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  have h : ‖algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ := norm_algebraMap' _ _
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h, map_natCast] at h2
  exact h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* PadicAlgCl p, w.asIdeal = smallIdeal σ := by
  by_contra hcon
  push_neg at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, ¬ w.asIdeal ≤ smallIdeal (σ : K →+* PadicAlgCl p) := by
    intro σ hle
    exact hcon (σ : K →+* PadicAlgCl p) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] PadicAlgCl p)) : Set (K →ₐ[ℚ] PadicAlgCl p)),
        (smallIdeal (σ : K →+* PadicAlgCl p) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = ∏ σ : K →ₐ[ℚ] PadicAlgCl p, σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ (PadicAlgCl p) (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : PadicAlgCl p)‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = (p : PadicAlgCl p) * ((m : ℤ) : PadicAlgCl p) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : PadicAlgCl p)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : PadicAlgCl p), norm_nonneg ((m : ℤ) : PadicAlgCl p)]

end GlobalTheory.CongW.PlaceEmb

namespace GlobalTheory.CongW

open Formalism.ConjugateSelfDual

end GlobalTheory.CongW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosure
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem vanish_transfer_of_algClosure :
    ∀ (F σ : Type) [Field F] [Finite σ] (J : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F),
      (∀ x : σ → AlgebraicClosure F, (∀ g ∈ J, aeval x g = 0) → aeval x f = 0) →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (x : σ → Ω), (∀ g ∈ J, aeval x g = 0) →
        aeval x f = 0 := by
  intro F σ _ _ J f hf Ω _ _ x hx
  have hrad : f ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F)]
    exact fun y hy => hf y hy
  obtain ⟨m, hm⟩ := hrad
  have h0 : (aeval x f) ^ m = 0 := by
    rw [← map_pow]
    exact hx _ hm
  exact IsNilpotent.eq_zero ⟨m, h0⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosureStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure : ∀ (F σ : Type) [Field F] [Finite σ] (J : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F), (∀ x : σ → AlgebraicClosure F, (∀ g ∈ J, aeval x g = 0) → aeval x f = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (x : σ → Ω), (∀ g ∈ J, aeval x g = 0) → aeval x f = 0 := by
  first | exact @GlobalTheory.vanish_transfer_of_algClosure | exact GlobalTheory.vanish_transfer_of_algClosure | (intros; apply GlobalTheory.vanish_transfer_of_algClosure <;> assumption)
end
end

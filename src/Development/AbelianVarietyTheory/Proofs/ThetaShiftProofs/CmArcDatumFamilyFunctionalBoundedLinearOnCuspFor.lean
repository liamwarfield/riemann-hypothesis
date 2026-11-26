module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QuotLocalOfQuotientLength
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.LenDescentOfLengthBaseChangeLocal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLe
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.AlgebraMapArcSInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamDegStLogOm
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamIndLenDeg
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqParametersConstantStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kronecker_cmLogPeriod_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  first | exact @GlobalTheory.LamF.exists_kronecker_logOm_eq | exact GlobalTheory.LamF.exists_kronecker_logOm_eq | (intros; apply GlobalTheory.LamF.exists_kronecker_logOm_eq <;> assumption)
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem GlobalTheory.LamF.lam_ind_len_deg :
    Formalism.L2.Pj.abelian₂.LamIndSt ∧ Formalism.L2.Pj.abelian₂.LamLenSt ∧
      ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, Formalism.L2.Pj.abelian₂.LamDegSt Q.H large₂.logOm := by
  obtain ⟨hdeg, hind, hlen⟩ := GlobalTheory.T.cmLieStatements_iff_library
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  refine ⟨hind.1 GlobalTheory.LamF.Ind.lamInd, hlen.1 (GlobalTheory.LamF.lamLen GlobalTheory.thetaUnifAV_all hL), fun D Q hQ large₂ => ?_⟩
  obtain ⟨_, χ, hχ, h⟩ := GlobalTheory.T.exists_kronecker_cmLogPeriod_eq D Q hQ large₂
  rw [← h]
  exact (hdeg _ _ _).1 (GlobalTheory.LamF.lamDegSt_logOm GlobalTheory.thetaUnifAV_all hL _ Q.H χ hχ)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBound
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBound
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section Lines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
  {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)} {th : a.D₀.P.L.Sec}
  {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}

theorem CMIn.fin_Tl_ne_zero (s : CMIn a e th jj n' La c₁) : s.Tl.I ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := s.good
  exact h.1

theorem CMIn.fin_line_ne_zero (s : CMIn a e th jj n' La c₁) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    (s.line τ k).I ≠ 0 := by
  letI := H.starRing
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := s.good
  unfold CMIn.line
  cases s.kind τ k with
  | none => exact one_ne_zero
  | some m =>
    have h := s.L_good.2.2.2 m
    show (s.L.ℓ m).I ≠ 0
    revert h
    cases s.L.src m with
    | inl q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h1 q.2).1.1
    | inr q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h2 q.2).1.1

theorem CMIn.fin_count_valLine (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ)
    (w : HeightOneSpectrum (𝓞 K₁)) :
    FractionalIdeal.count K₁ w (s.valLine mo n).I =
      (n : ℤ) * (-FractionalIdeal.count K₁ w s.Tl.I) +
        ∑ x ∈ mo.support, (mo x : ℤ) * (-FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) := by
  classical
  have hT := s.fin_Tl_ne_zero
  have hL : ∀ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v ≠ 0 := fun v => pow_ne_zero _ (s.fin_line_ne_zero _ _)
  show FractionalIdeal.count K₁ w ((s.Tl.I⁻¹) ^ n * (∏ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v)⁻¹) = _
  rw [FractionalIdeal.count_mul K₁ w (pow_ne_zero _ (inv_ne_zero hT))
      (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hL v)),
    FractionalIdeal.count_pow, FractionalIdeal.count_inv, FractionalIdeal.count_inv,
    FractionalIdeal.count_prod K₁ w _ _ (fun v _ => hL v)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_) |>.trans ?_
  · rw [Finsupp.notMem_support_iff.mp hx]; simp
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [FractionalIdeal.count_pow]; ring

end Lines

theorem cfOf_fin_bound : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → 1 ≤ La → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ intAt Xo c a' n la, cfOf d.yF d.μ d.jj F ≠ 0 → -((w.asIdeal.ramificationIdx (𝓞 c.F) : ℝ) * beOf E n' (absA Dw a') la) ≤ (ordAt w (cfOf d.yF d.μ d.jj F) : ℝ) - (FractionalIdeal.count K₁ w (s.valLine d.μ n).I : ℝ) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS _ la w hlw a' n F hF hne
  obtain ⟨Z, gm, lam, A, Bm, ⟨hg0, hg⟩, hlam, ⟨hAB, hA⟩, hbd⟩ :=
    GlobalTheory.T.localArcIntegrality_of_cmNormalisedTrivialisation hK E H Dw l Xo c K₁ d n' La c₁ s hM hS la w hlw a' n
  obtain ⟨P, hPe, hPh⟩ := GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c)
    K₁ d a' n F hF.1
  set m : ℕ := w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la with hm
  have hC1 : (1 : ℝ) ≤ Z.r ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos Z.r_pos _)).mpr (pow_le_one₀ Z.r_pos.le Z.r_lt.le)
  have hbd' := hbd F hF
  rw [← hPe, FinPf.arcNum_algebraMap] at hbd'
  have key := FinKey.coeff_bound finCore_holds basisChange_holds (GlobalTheory.ArcQ.FinSite.«ι» Z) Z.K₀ Z.res Z.S Z.S_disc Z.S_dense
    Z.S_units P (absA Dw a') hPh n gm hg0 lam (fun τ k => (hlam τ k).1) A Bm hAB _ hC1 hA hbd' d.μ d.jj
  have hcf : cfOf d.yF d.μ d.jj F = (P.coeff d.μ).coeff d.jj := by
    rw [cfOf, ← hPe, FinPf.arcNum_algebraMap]
  rw [hcf] at hne ⊢
  rw [GlobalTheory.ArcQ.FinSite.«norm_ι» Z _ hne, hg] at key
  simp only [Finsupp.prod, (hlam _ _).2] at key
  have hz := FinPf.zpow_bound Z.r Z.r_pos Z.r_lt _ _ n (absA Dw a') m d.μ.support d.μ
    (fun x => -FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) key
  rw [s.fin_count_valLine]
  simp only [beOf, hm] at hz ⊢
  push_cast at hz ⊢
  nlinarith [hz]

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBoundStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmArcDatum_functional_finite_integrality_bound : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → 1 ≤ La → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ intAt Xo c a' n la, cfOf d.yF d.μ d.jj F ≠ 0 → -((w.asIdeal.ramificationIdx (𝓞 c.F) : ℝ) * beOf E n' (absA Dw a') la) ≤ (ordAt w (cfOf d.yF d.μ d.jj F) : ℝ) - (FractionalIdeal.count K₁ w (s.valLine d.μ n).I : ℝ) := by
  first | exact @GlobalTheory.ArcCM.cfOf_fin_bound | exact GlobalTheory.ArcCM.cfOf_fin_bound | (intros; apply GlobalTheory.ArcCM.cfOf_fin_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem GlobalTheory.ArcCM.lamDegSt_logOm₂ : Known → ∀ (D : D7) (T : Core D) (large₂ : SizeData₂ D), T.Q.Pins → GlobalTheory.LamF.LamDegSt T.Q.H large₂.logOm :=
  fun _ D T large₂ h => (GlobalTheory.LamF.lambdaBundle_conditions_iff.1 _ _ _).2 (GlobalTheory.LamF.lam_ind_len_deg.2.2 D T.Q h.1 large₂)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEq
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaNormLieNormUniqueAtEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaNormLieNormUniqueAtEmbedding
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArchNormUnique

open MeasureTheory GlobalTheory.ArchMetricCompare GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

theorem mean_eq {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Fd : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ Fd volume) {f : (Fin g → ℂ) → ℝ}
    (hf : ∀ a ∈ Λ, ∀ x, f (x + a) = f x) :
    (∫ z in Fd, f z) / (volume Fd).toReal = latticeMean Λ f := by
  rw [latticeMean_eq Λ volume hF hf, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, smul_eq_mul,
    div_eq_inv_mul]
  rfl

theorem archimedean_l2_norm_unique (hU : ThetaUnifAV) {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {s : P.L.Sec} {v v' : ℝ} (h : IsL2SquareIntegralProblem P rig σ s v)
    (h' : IsL2SquareIntegralProblem P rig σ s v') : v = v' := by
  obtain ⟨-, A, _, φ, u, Hm, χ, θ, Fd, hp, hu, o, hθ, hF, -, -, -, rfl⟩ := h
  obtain ⟨-, A', _, φ', u', Hm', χ', θ', Fd', hp', hu', o', hθ', hF', -, -, -, rfl⟩ := h'
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hp hp'
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU (pullPol P hp') P.g u' Hm' χ' hu'
  obtain ⟨F, hFe, hFΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A A' (pullPol P hp).isAb (pullPol P hp').isAb
    _ _ P.g P.g u u' t1 t2 e.hom he
  have hL := pull_isLB P.isLB φ
  have hL' := pull_isLB P.isLB φ'
  obtain ⟨t, ht⟩ : LBIso ((P.L.pull φ').pull e.hom.left) (P.L.pull φ) := by
    have h0 : LBIso (P.L.pull φ') (P.L.pull φ') := ⟨idIso _, idIso_isGen hL'⟩
    have h1 := (PolFibre.lbIso_pull_comp h0 e.hom.left).symm
    rwa [heψ] at h1
  have hHH : ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w := fun z w => by
    simpa using hermForm_pull_eq_of_lbIso_pow A A' _ _ hL hL' _ _ u u' Hm χ Hm' χ' hu hu' e.hom F hFe 1 1
      ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ z w
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz => by
    by_contra hne
    have h1 := hu.2.1 z hne
    have h2 := hHH z z
    rw [hz] at h2
    change 0 < (hermForm Hm z z).re at h1
    rw [← h2] at h1
    simp [hermForm] at h1
  let T := LinearEquiv.ofInjectiveEndo F hinj
  have hT : ∀ z, T z = F z := fun _ => rfl
  have hx : ∀ z, (u'.ex (F z)).left ≫ φ' = (u.ex z).left ≫ φ := fun z => by
    rw [hFe, Over.comp_left, Category.assoc, heψ]
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => ⟨fun hz => by
    rw [← u'.ker, hFe, ← (u'.ker 0).2 u'.Λ.zero_mem, ← map_zero F, hFe, cancel_mono] at hz
    rw [← u.ker, hz, u.ker]
    exact u.Λ.zero_mem, hFΛ z⟩
  let U : P.L.ι → (Fin P.g → ℂ) → Prop := fun j z => ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U fun _ => j
  have U' : ∀ j z, U j z → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ (P.L.pull φ').U fun _ => j := fun j z hz =>
    (le_pull_iff _ _ _ _).2 ((hx z).symm ▸ (le_pull_iff _ _ _ _).1 hz)
  have Uc : ∀ z, ∃ j, U j z := fun z => by
    obtain ⟨j, hj⟩ := exists_chart_at hL (u.ex z).left
    exact ⟨j PUnit.unit, hj⟩
  let Pm : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hr : Set.range Pm = u.Λ := Subtype.range_coe
  have hr' : Pm.range = u.Λ.toAddSubgroup := SetLike.coe_injective hr
  have hfr : ∀ j z, U j z → u'.fr (fun _ => j) (F z) = u.fr (fun _ => j) z :=
    GeneratorNorm.frames_eq Pm (by rw [hr']; exact u.discrete) (by rw [hr]; exact u.full) U (fun j => (u.hol _ 0).1) Uc
      (fun j z a hz => by
        have := ex_add_period u z a
        simp only [U] at hz ⊢
        exact this ▸ hz)
      (fun j j' z => valAt' ((u.ex z).left ≫ φ) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val)
      (fun j => u.fr fun _ => j) (fun j z => u'.fr (fun _ => j) (F z))
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun j => u.fr_hol _)
      (fun j => (u'.fr_hol _).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn (U' j))
      (fun j z => u.fr_ne _ z)
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩
        rw [u.fr_compat _ _ z h3, val_pull_g _ _ _ _ _ h3])
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨U' j z h1, U' j' z h2⟩
        show u'.fr _ (F z) = _ * u'.fr _ (F z)
        rw [u'.fr_compat _ _ _ h3, val_pull_g _ _ _ _ _ h3, hx])
      (fun j hj => by
        have h0 : ⊤ ≤ (P.L.pull (eSec P.A)).U fun _ => j := by
          have h1 := (le_pull_iff _ _ _ _).1 hj
          rw [TangentOrigin.ex_zero_left] at h1
          refine (le_spMap_iff σ _).1 ((le_pull_iff _ _ _ _).2 ?_)
          exact PolBaseChange.eSec_comm hp ▸ h1
        show u'.fr _ (F 0) = _
        rw [map_zero, o' j h0, o j h0])
      (fun a j z hz => by
        show ‖u.fr _ z‖ = _ * ‖u.fr _ (z + a)‖
        rw [hu.2.2.2 a _ z hz, norm_mul, norm_mul, hu.2.2.1, _root_.one_mul]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm z a))
      (fun a j z hz => by
        show ‖u'.fr _ (F z)‖ = _ * ‖u'.fr _ (F (z + a))‖
        rw [hu'.2.2.2 ⟨F a, hFΛ a a.2⟩ _ _ (U' j z hz), norm_mul, norm_mul, hu'.2.2.1, _root_.one_mul, map_add (f := _),
          ← hHH, ← hHH]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm' (F z) (F a)))
  have hθθ : ∀ z, θ' (F z) = θ z := fun z => by
    obtain ⟨j, hj⟩ := Uc z
    have h1 := hθ' j (F z) ((le_pull_iff _ _ _ _).1 (U' j z hj))
    rw [hx, hθ j z ((le_pull_iff _ _ _ _).1 hj), hfr j z hj] at h1
    exact (mul_right_cancel₀ (u.fr_ne _ z hj) h1).symm
  have hff : ∀ z, ‖θ' (F z)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (F z)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun z => by
    rw [hθθ, show hermSq Hm' (F z) = hermSq Hm z from congrArg Complex.re (hHH z z)]
  have hper : ∀ a ∈ u.Λ, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm (z + a)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun a ha z => by
    obtain ⟨th, hth⟩ := sec_pull_down ((isGen_iff _).1 (idIso_isGen hL)) P.isLB hL s
    have hth := KeyPow.appLE_eq_of_stalk _ s th (hth _ (𝟙 _))
    refine weight_periodic hL hu (s := th) (fun j z hz => ?_) ⟨a, ha⟩ z
    have e := val_via _ s th hth (u.ex z).left (j PUnit.unit) j ((top_le_preimage_inf _ _ _).2 ⟨hz, hz⟩)
    refine Eq.trans ?_ (hθ (j PUnit.unit) z ((le_pull_iff _ _ _ _).1 hz))
    rw [e]
    exact ((congrArg (· * _) (val_g_self hL _ j hz)).trans (_root_.one_mul _)).symm
  have hper' : ∀ a ∈ u'.Λ, ∀ z, ‖θ' (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (z + a)) =
      ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' z) := fun a ha z => by
    obtain ⟨a, rfl⟩ := T.surjective a
    obtain ⟨z, rfl⟩ := T.surjective z
    rw [← map_add (f := _), hT, hT, hff, hff, hper a ((hΛ a).1 ha)]
  haveI := u.discrete
  haveI := u'.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : IsZLattice ℝ u'.Λ := ⟨u'.full⟩
  rw [mean_eq u.Λ hF hper, mean_eq u'.Λ hF' hper',
    ← latticeMean_comp_equiv u.Λ u'.Λ (T.restrictScalars ℝ).toContinuousLinearEquiv hΛ hper']
  exact congrArg _ (funext fun z => (hff z).symm)

theorem norms_unique : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v v' : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), rig.IsGen → Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th σ v' → v = v') ∧ ∀ η' : epsR K ⟶ P.A, IsTangent η' → Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' σ v' → v = v' := by
  intro hK K _ P σ v v'
  refine ⟨fun rig th _ h h' => archimedean_l2_norm_unique hK.theta ((isL2Sq_iff_isThNormAt P rig σ th v).2 h)
    ((isL2Sq_iff_isThNormAt P rig σ th v').2 h'), ?_⟩
  rintro t ht ⟨Q, φ, w, x, hp, hw, hx, u, Hm, χ, z, hu, hz, rfl⟩ ⟨Q', φ', w', x', hp', hw', hx', u', Hm', χ', z', hu', hz', rfl⟩
  have e := CM.LieMetric.hermForm_eq hK.theta (P := P) (s := σ) ⟨g_eq hp, hp, LBIso.symm ⟨w, hw⟩⟩
    ⟨g_eq hp', hp', LBIso.symm ⟨w', hw'⟩⟩ hu hu' (I := PUnit) (v := fun _ => t) (fun _ => ht)
    (w := fun _ => x) (w' := fun _ => x') (W := fun _ => z) (W' := fun _ => z') (fun _ => ⟨hx, hz⟩) (fun _ => ⟨hx', hz'⟩)
    PUnit.unit PUnit.unit
  exact congrArg (fun c : ℂ => Real.log (Real.pi * c.re) / 2) e

end GlobalTheory.ArchNormUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaNormLieNormUniqueAtEmbeddingStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v v' : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), rig.IsGen → Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th σ v' → v = v') ∧ ∀ η' : epsR K ⟶ P.A, IsTangent η' → Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' σ v' → v = v' := by
  first | exact @GlobalTheory.ArchNormUnique.norms_unique | exact GlobalTheory.ArchNormUnique.norms_unique | (intros; apply GlobalTheory.ArchNormUnique.norms_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivStarStarZero
noncomputable section

namespace GlobalTheory.ArchConj

section Diff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt.Arch GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fderiv_star_star_zero {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases hF : DifferentiableAt ℂ F 0
  · have d := hF.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have hG : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun hG => hF (by
      have := hG.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := funext fun z => by simp
      rwa [star_zero, e] at this)
    rw [fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt hG]
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)
variable {X : Scheme.{0}} {L : LB X} {φ : A.left ⟶ X} {g : ℕ} (u : HolUnif A (L.pull φ) g)

theorem cj_isDiff' {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    (cjUnif h u).IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q (spMap (dualMap (starRingEnd ℂ)) q)]
    exact hq
  have e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => cj_val h _ U f
  rw [e1, fderiv_star_star_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem isLieNormAt_conjugate {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ} {t : epsR K ⟶ P.A} {v : ℝ}
    (H : IsLieNormAt P t σ v) : IsLieNormAt P t (ComplexEmbedding.conjugate σ) v := by
  obtain ⟨P', φ, w, t', h, hw, e, u, Hm, χ, z, hAH, hd, rfl⟩ := H
  have hg := g_eq h
  obtain ⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ P'.A.left),
      IsGrpPullback A' P'.A cj ψ := ⟨_, _, _, isGrpPullback_pullback P'.A cj⟩
  have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ t'.left) ≫ P'.A.hom = (epsR ℂ).hom ≫ cj := by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t'' : epsR ℂ ⟶ A' := Over.homMk (hc.1.lift _ _ sq) (hc.1.lift_snd _ _ _)
  have e' : t''.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := hc.1.lift_fst _ _ _
  have h' : IsGrpPullback A' P.A (spMap (ComplexEmbedding.conjugate σ)) (ψ ≫ φ) :=
    (hc.comp h).congr (spMap_conjugate σ) rfl
  have e'' : t''.left ≫ ψ ≫ φ = spMap (dualMap (ComplexEmbedding.conjugate σ)) ≫ t.left := by
    rw [← Category.assoc, e', Category.assoc]
    refine (congrArg _ e).trans ?_
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap]
  have hM := pull_isLB P.isLB φ
  have hAH' := cj_isAH hc (carry u P'.isLB hM hw) (carry_isAH _ _ hw hAH)
  have hd' := cj_isDiff' hc (carry u P'.isLB hM hw) e' (w := z) hd
  have hz : (z ⬝ᵥ Hm.mulVec (star z)).re = (star z ⬝ᵥ (Hm.map star).mulVec (star (star z))).re := by
    have := hermSq_star Hm (star z)
    rw [star_star] at this
    exact this.symm
  obtain ⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩ := P
  obtain rfl : P'.g = g := hg
  exact ⟨pullPol _ h', ψ ≫ φ, idIso _, t'', h', idIso_isGen (pull_isLB isLB _), e'',
    cjUnif hc (carry u P'.isLB hM hw), _, _, star z, hAH', hd', by rw [hz]; rfl⟩

end Diff

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem norms_conj : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th ((starRingEnd ℂ).comp σ) v) ∧ ∀ η' : epsR K ⟶ P.A, Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' ((starRingEnd ℂ).comp σ) v :=
  fun _ _ _ P σ v => ⟨fun rig th H => (ArchMetricCompare.isL2Sq_iff_isThNormAt P rig _ th v).1
    (ArchMetricCompare.isL2Sq_conjugate_embedding ((ArchMetricCompare.isL2Sq_iff_isThNormAt P rig σ th v).2 H)),
    fun _ H => isLieNormAt_conjugate H⟩

end GlobalTheory.ArchConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEq
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem len_conj_of_lieNorm (hK : Known) {K : Type} [Field K] [NumberField K] (P : Out.PolAV (Sp K))
    (v : epsR K ⟶ P.A) (hv : IsTangent v) (ℓ : MLine K) (hℓ : ℓ.Good)
    (h : ∀ σ : K →+* ℂ, Arch.IsLieNormAt P v σ (Real.log (ℓ.n σ))) (em : K →+* ℂ) :
    ℓ.n ((starRingEnd ℂ).comp em) = ℓ.n em := by
  have h1 := (GlobalTheory.ArchConj.norms_conj hK K P em _).2 v (h em)
  have h2 := (GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding hK K P _ _ _).2 v hv (h ((starRingEnd ℂ).comp em)) h1
  exact Real.log_injOn_pos (hℓ.2 _) (hℓ.2 _) h2

theorem valLine_conj : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ) (em : K₁ →+* ℂ), (s.valLine mo n).n ((starRingEnd ℂ).comp em) = (s.valLine mo n).n em := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s mo n em
  letI := H.starRing
  have tie := GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms hK E H Dw l c K₁ a e th jj n' La c₁ s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hΨ, h', hT, -⟩ := s.good
  have hTl : s.Tl.n ((starRingEnd ℂ).comp em) = s.Tl.n em := by
    have h1 := (GlobalTheory.ArchConj.norms_conj hK K₁ a.D₀.P em _).1 a.D₀.rig th (tie em).1
    have h2 := (GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding hK K₁ a.D₀.P _ _ _).1 a.D₀.rig th a.D₀.rig_gen (tie ((starRingEnd ℂ).comp em)).1 h1
    exact (sq_eq_sq₀ (hT.2 _).le (hT.2 _).le).1 h2
  have hL : ∀ m, (s.L.ℓ m).n ((starRingEnd ℂ).comp em) = (s.L.ℓ m).n em := by
    intro m
    have hm := s.L_good.2.2.2 m
    rcases hq : s.L.src m with q | q
    · rw [hq] at hm
      have hm' : s.L.ℓ m = s.ℓΨ q.2 := hm
      rw [hm']
      exact len_conj_of_lieNorm hK s.xΨ.P (s.xΨ.v q.2) (s.xΨ.basis.1 q.2) _ (hΨ q.2).1
        (fun σ => (tie σ).2.1 q.2) em
    · rw [hq] at hm
      have hm' : s.L.ℓ m = s.ℓ' q.2 := hm
      rw [hm']
      exact len_conj_of_lieNorm hK s.x'.P (s.x'.v q.2) (s.x'.basis.1 q.2) _ (h' q.2).1
        (fun σ => (tie σ).2.2.1 q.2) em
  have hline : ∀ τ k, (s.line τ k).n ((starRingEnd ℂ).comp em) = (s.line τ k).n em := by
    intro τ k
    unfold CMIn.line
    rcases s.kind τ k with _ | m
    · rfl
    · exact hL m
  simp only [CMIn.valLine, MLine.tensor, MLine.pow, MLine.dual, MLine.prodPow, hTl, hline]

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEqStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmValueLine_length_conj_eq : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ) (em : K₁ →+* ℂ), (s.valLine mo n).n ((starRingEnd ℂ).comp em) = (s.valLine mo n).n em := by
  first | exact @GlobalTheory.ArcCM.valLine_conj | exact GlobalTheory.ArcCM.valLine_conj | (intros; apply GlobalTheory.ArcCM.valLine_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NdegLineOptionLe
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmNumbersOfGood
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM


open scoped nonZeroDivisors in
theorem exists_locGen_at {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨c, hc⟩ := p.valuation_surjective K (WithZero.exp (-(FractionalIdeal.count K p I)))
  exact ⟨c, (isLocGen_iff_valuation_eq p c I).2 hc⟩

theorem cmNumbers_of_good : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)] (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La logOm : ℝ), (∀ a : 𝓞 E, star a = H.bar a) → LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → 1 ≤ La → LamDegSt H logOm → CMNumbers0 o.LamL L.ℓ o.Tl.dual La logOm := by
  intro hK E _ _ _ H _ l c nΨ n' f o La logOm hbar hG L hL hLa hDeg
  have hdeg := hDeg l c hbar nΨ n' f o La hG
  have hdet := GlobalTheory.LamF.Ind.lamInd E H l c hbar nΨ n' f o La hG L hL
  choose Hm hH hn hsq using GlobalTheory.LamF.lamLen hK.theta hK.laws E H l c hbar nΨ n' f o La hG L hL
  have hloc := GlobalTheory.LamF.letters_det_valuation_le E H l c nΨ n' f o La hG L hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, hLam, hkl, hka, -⟩ := hG
  obtain ⟨-, -, -, hℓ⟩ := hL
  have hlg : ∀ k, (L.ℓ k).Good := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  have hnd : ∀ k, (L.ℓ k).ndeg = logOm / 2 := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact hdeg.1 q.2
    | inr q => intro h1; rw [h1]; exact hdeg.2 q.2
  have hkey := key_deg hK.key o.K₁ o.xB o.Tl o.LamL hT hLam hkl hka
  have hHad := hadamard_local_base o.K₁ o.xB.P.g o.LamL L.ℓ L.U Hm La hLam.1 hlg hdet (by linarith) hH hn
    (fun p => by
      obtain ⟨cd, hcd⟩ := exists_locGen_at p o.LamL.I
      choose cl hcl using fun j => exists_locGen_at p (L.ℓ j).I
      exact ⟨cd, cl, hcd, hcl, hloc p cd cl hcd hcl⟩) hsq
  have hTd : o.Tl.dual.Good := (degree_algebraic o.K₁ o.Tl o.Tl hT hT).2.2.1
  have hd := finrank_pos_real o.K₁
  refine ⟨hLam, hlg, hTd, hLa, hHad, hnd, le_of_eq ?_⟩
  simp only [MLine.ndeg]
  rw [hkey]
  field_simp

end GlobalTheory.ArcCM
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

private theorem prod_option_eq_prod_isSome_of_none_eq_one {V M : Type} [Fintype V] [CommMonoid M] {g : ℕ} (k : V → Option (Fin g))
    (F : V → Option (Fin g) → M) (h1 : ∀ v, F v none = 1) :
    ∏ v, F v (k v) = ∏ w : {v // (k v).isSome = true}, F w.1 (some ((k w.1).get w.2)) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v => (k v).isSome = true) (fun v => F v (k v))]
  have h2 : ∏ w : {v // ¬ (k v).isSome = true}, F w.1 (k w.1) = 1 := by
    refine Finset.prod_eq_one (fun w _ => ?_)
    have hw : k w.1 = none := by simpa using w.2
    rw [hw, h1]
  rw [h2, _root_.mul_one]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  rw [Option.some_get]

private theorem mLine_prodPow_option_elim_eq_prodPow_isSome {K : Type} [Field K] [NumberField K] {g : ℕ} (ℓ : Fin g → MLine K)
    {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) :
    MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu =
      MLine.prodPow (fun w : {v // (k v).isSome = true} => ℓ ((k w.1).get w.2)) (fun w => mu w.1) := by
  unfold MLine.prodPow
  congr 1
  · exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).I ^ mu v) (fun v => by simp [MLine.one])
  · funext σ
    exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).n σ ^ mu v) (fun v => by simp [MLine.one])

theorem ndeg_line_option_le {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K)
    (de : MLine K) (La logOm : ℝ) {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) (n G : ℕ)
    (h : CMNumbers0 abelian₂ ℓ de La logOm) (hG : g ≤ G) :
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).Good ∧
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).ndeg ≤
      (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mu v : ℕ) : ℝ) + ((G * n : ℕ) : ℝ)) := by
  rw [mLine_prodPow_option_elim_eq_prodPow_isSome ℓ k mu]
  have hN := degree_norm_base K g abelian₂ ℓ de La logOm {v // (k v).isSome = true} (fun w => (k w.1).get w.2)
    (fun w => mu w.1) n h
  have hLa : 1 ≤ La := h.2.2.2.1
  have hP : 0 ≤ pDeg logOm + (1 / 2) * Real.log La := by
    have h0 := Real.log_nonneg hLa
    have h1 := abs_nonneg logOm
    unfold pDeg
    linarith
  refine ⟨hN.1, le_trans hN.2 (mul_le_mul_of_nonneg_left ?_ hP)⟩
  have hs : ∑ w : {v // (k v).isSome = true}, (mu w.1 : ℝ) ≤ ∑ v, (mu v : ℝ) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun v => (k v).isSome = true) (fun v => (mu v : ℝ))]
    have h0 : 0 ≤ ∑ w : {v // ¬ (k v).isSome = true}, (mu w.1 : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hgG : (g : ℝ) * n ≤ (G : ℝ) * n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hG) (Nat.cast_nonneg n)
  push_cast
  linarith

theorem valLine_ndeg_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (logOm : ℝ) (mo : ArcLt Dw →₀ ℕ) (n : ℕ), 1 ≤ La → LamDegSt H logOm → (s.valLine mo n).Good ∧ (s.valLine mo n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mo v : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n : ℕ) : ℝ)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s logOm mo n hLa hdeg
  letI := H.starRing
  have hcm := cmNumbers_of_good hK E H l c (Dw.p - 1) (Dw.q - 1) (Module.finrank ℚ E / 2) s.toCMPart.obj La logOm
    (fun _ => rfl) s.good s.L s.L_good hLa hdeg
  have hg : a.D₀.P.g ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have h9 : a.D₀.P.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) := s.good.2.2.2.2.2.2.2.2.1
    rw [h9]
    apply Nat.mul_le_mul_left
    omega
  exact ndeg_line_option_le (K := K₁) s.LamL s.L.ℓ s.Tl.dual La logOm (fun v : ArcLt Dw => s.kind v.1 v.2.2) mo n
    (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) hcm hg

end GlobalTheory.ArcCM
end

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.RunNum

theorem sum_extendByZero_fin_eq_sum_of_eq {p m : ℕ} (f : Fin p → ℕ) (h : m = p) : ∑ i : Fin m, ext0 f i = ∑ i, f i := by
  subst h
  exact Finset.sum_congr rfl fun i _ => by simp [ext0]

theorem conj_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have h0 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rwa [h] at h0
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h2] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem absA_wtA {D : D7} (T : Core D) (j : ℕ) (hD : IsDatW D j (T.Q.Dw j)) (hH : T.Q.PinHost)
    (w : WeightFamilies.Wt D j) :
    absA (T.Q.Dw j) (wtA w) = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  simp only [absA, wtA]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_add_distrib]
  have ht := hH.2.2.2 t
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_eq_single (DV.tauEmb D t)]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.1]; simp [Datum.mult, ht])
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.2.1]; simp [Datum.mult, conj_rt_ne _ _ ht])
    · intro b _ hb; simp [hb]
    · simp

theorem absA_add_le_size {D : D7} (T : Core D) (hp : T.Q.Pins) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    (absA (T.Q.Dw j) (wtA w) : ℝ) + (D.R.f : ℝ) * D.R.r * w.n ≤ w.size := by
  rw [absA_wtA T j (hp.2.2.2 j hj) hp.1 w]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith

theorem pnorm_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} [Fintype Comp]
    (X : Comp → Data E r) (la) {P : FDSec X} (hP : P ∈ holSub X la) (p : FPt X) :
    (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ Formalism.L2.Pj.supN X la P := by
  unfold Formalism.L2.Pj.supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem one_le_LaAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : 1 ≤ LaAt D j ka CR Tt cc :=
  le_max_left _ _

theorem archimedeanTerm_nonneg (E : Type) [Field E] [NumberField E] {r : ℕ} (hr : 1 ≤ r) {La : ℝ} (hLa : 1 ≤ La) (c₁ : ℝ) :
    0 ≤ archP E r La c₁ := by
  unfold archP
  have h1 : 0 ≤ Real.log (max 1 c₁) := Real.log_nonneg (le_max_left _ _)
  have h2 : 0 ≤ Real.log La := Real.log_nonneg hLa
  have h3 : 0 ≤ Real.log (rdE E) := by
    refine Real.log_nonneg (Real.one_le_rpow ?_ (by positivity))
    unfold dE
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have h4 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  linarith

theorem arch_good (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  obtain ⟨-, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hnum j hj
  have hFc : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
  have hS : (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F =
      supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (em.comp (algebraMap T.Q.c.F K₁)) (wtA ka) ka.n F.1 := by
    change cutN T.C T.Ns j ka _ F = _
    unfold cutN Core.Ns
    rw [if_pos hj, goodOf, if_pos hem]
  have h0 := (recB h).supN_nonneg j ka (em.comp (algebraMap T.Q.c.F K₁)) F
  have hb := GlobalTheory.T.norm_cmArcCoefficientFunctional_le hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s em D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (xiR D) ((recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F)
    (wtA ka) ka.n hd (one_le_LaAt D j ka CR Tt cc) hem (h.unf j hj _ hem) (h.xiAbs j hj _ hem) (dom_wtA ka)
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) _ _ (hG j hj _ hem)
      (h.chiTriv j hj _ hem _ _ (dom_wtA ka)))
    F.1 (cusp_le_sec _ _ _ _ _ hFc) h0 (by
      intro k y hy
      rw [hS]
      exact mul_le_mul_of_nonneg_left
        (pnorm_le_sup _ _ (((mem_cusp _ _ _ _ _ _).1 hFc).2 _ hem) ⟨k, ⟨y, hy⟩⟩) (lieFac_pos _ _ _).le)
  refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0)
  unfold CarchAt
  have h1 := absA_add_le_size T h.pins j hj ka
  have h2 : (fdeg D.host.E : ℝ) = D.R.f := by
    unfold fdeg
    rw [hf, Nat.mul_div_cancel_left _ two_pos]
  have h3 : (D.R.f : ℝ) * ka.n ≤ (D.R.f : ℝ) * D.R.r * ka.n := by
    have : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
    have h4 : (0 : ℝ) ≤ (D.R.f : ℝ) * ka.n := by positivity
    nlinarith
  rw [h2]
  have h5 := archimedeanTerm_nonneg D.host.E hr (one_le_LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j)
  exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith) h5) _

theorem arch_all (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  by_cases hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
  · exact arch_good hK h j ka CR Tt cc hG hj K₁ d hd s em hem F
  · have hg := goodEmb_goodOf T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
    rw [goodOf, if_neg hem] at hg
    have h1 := arch_good hK h j ka CR Tt cc hG hj K₁ d hd s ((starRingEnd ℂ).comp em) hg F
    rw [GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s d.μ ka.n em, RingHom.comp_assoc, recB_supN_conj] at h1
    simpa using h1

end GlobalTheory.ArcCM.RunNum

namespace GlobalTheory.ArcCM

open RunNum

theorem numGood_of_famQ : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ)
    (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D),
    GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m →
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T j ka CR Tt cc K₁ d →
    ∃ φ : @LinearMap T.Q.c.F T.Q.c.F _ _ (RingHom.id T.Q.c.F) ((recB h).Cusp j ka) K₁
        ((recB h).acgC j ka).toAddCommMonoid _ ((recB h).modC j ka) _,
      (∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧
      @NumGood T.Q.c.F ((recB h).Cusp j ka) _ _ ((recB h).acgC j ka) ((recB h).modC j ka)
        {F | F ∈ (recB h).Mlat j ka} (fun σ F => (recB h).supN j ka σ F)
        (beOf D.host.E (nAt D j ka CR Tt cc) (absA (T.Q.Dw j) (wtA ka)))
        (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) K₁ _ _ _ φ := by
  intro hK D T h j ka CR Tt cc large₂ hG hj _ K₁ _ _ _ d ⟨hd, ⟨s⟩⟩
  obtain ⟨hgood, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have hle : cutR T.C j ka ≤ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n :=
    (cutR_le T.C j ka).trans (cusp_le_sec _ _ _ _ _)
  obtain ⟨⟨ψ, hψ⟩, hdeg⟩ := cfOf_linear_and_degree hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n
  have hLa := one_le_LaAt D j ka CR Tt cc
  have hc : 0 ≤ pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc) := by
    have := Real.log_nonneg hLa
    unfold pDeg
    positivity
  have hφ : ∀ F : (recB h).Cusp j ka, (ψ.comp (Submodule.inclusion hle)) F = cfOf d.yF d.μ d.jj F.1 :=
    fun F => hψ _
  refine ⟨ψ.comp (Submodule.inclusion hle), hφ, ?_⟩
  by_cases hμ : ∑ v, d.μ v = absA (T.Q.Dw j) (wtA ka)
  · obtain ⟨hN, hNd⟩ := valLine_ndeg_le hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s large₂.logOm d.μ ka.n hLa
      (lamDegSt_logOm₂ hK D T large₂ h.pins)
    refine ⟨s.valLine d.μ ka.n, hN, hNd.trans ?_, GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s _ _, ?_, ?_⟩
    · unfold BdegAt
      refine mul_le_mul_of_nonneg_left ?_ hc
      rw [hμ, hf, hpq, Nat.mul_div_cancel_left _ two_pos]
      push_cast
      exact absA_add_le_size T h.pins j hj ka
    · intro la w hw F hF hne
      rw [hφ] at hne ⊢
      exact GlobalTheory.T.cmArcDatum_functional_finite_integrality_bound hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s
        (modelsAt_of_good_level hK _ _ _ _ _ _ (hpq ▸ hr) hgood) hd hLa la w hw (wtA ka) ka.n F.1
        ⟨hle F.2, fun v hv => hF la v hv⟩ hne
    · intro em F _ hne
      have hpos : 0 < (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F := by
        refine lt_of_le_of_ne ((recB h).supN_nonneg j ka _ F) fun h0 => hne ?_
        rw [((recB h).supN_eq_zero j ka _ F).1 h0.symm]
        exact map_zero _
      have h1 := arch_all hK h j ka CR Tt cc hG hj K₁ d hd s em F
      rw [hφ] at hne ⊢
      have h2 : 0 < ‖em (cfOf d.yF d.μ d.jj F.1)‖ := norm_pos_iff.2 ((map_ne_zero em).2 hne)
      have h3 := Real.log_le_log (mul_pos h2 (hN.2 em)) h1
      rwa [Real.log_mul h2.ne' (hN.2 em).ne', Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
  · have hz : ∀ F : (recB h).Cusp j ka, ¬ (ψ.comp (Submodule.inclusion hle)) F ≠ 0 := fun F hne =>
      hμ (hdeg F.1 (hle F.2) (hφ F ▸ hne))
    refine ⟨MLine.one, ⟨one_ne_zero, fun _ => one_pos⟩, ?_, fun _ => rfl, fun _ _ _ F _ hne => (hz F hne).elim,
      fun _ F _ hne => (hz F hne).elim⟩
    have : (MLine.one : MLine K₁).ndeg = 0 := by simp [MLine.ndeg, MLine.deg, MLine.one]
    rw [this]
    exact mul_nonneg hc (zero_le_one.trans ka.one_le_size)

end GlobalTheory.ArcCM

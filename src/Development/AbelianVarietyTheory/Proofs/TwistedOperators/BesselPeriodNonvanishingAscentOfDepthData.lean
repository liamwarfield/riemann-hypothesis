module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBessel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodGridFramesOfDepthFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.FirstRowDepth

theorem datumDep : GlobalTheory.SepRows.DatumDep := by
  intro D hq T L μ0 hL sc G W M hM ρ Φ i
  obtain ⟨-, ⟨hth, hlat⟩, -⟩ := GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua D hq T L μ0 hL sc G W M hM i.1 i.2 (Φ i)
  have hthP : ∀ P, IsThetaFunO W.ψ (G.pS (.chi i.1 0)) (G.pT (.chi i.1 0))
      (W.fock (.chi i.1 0) (W.cosVec i (Φ i)) P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth P
  refine ⟨hthP (ρ i), fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2).1) (hlat.1 u hu) (ρ i)
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP u
      (GlobalTheory.VacGood.infPart_latO hu.1) (hlat.2 e he u hu hh) (ρ i)

end GlobalTheory.FirstRowDepth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRow_data_have_depth : GlobalTheory.SepRows.DatumDep := by
  first | exact @GlobalTheory.FirstRowDepth.datumDep | exact GlobalTheory.FirstRowDepth.datumDep | (intros; apply GlobalTheory.FirstRowDepth.datumDep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTower
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandProd

theorem handP_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  intro D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ' Φ₀ h1 h' h0
  have hW₀ : IsWeilDatumO ψ J.W₀ B.V₀ s.χV (χA * χz) s.om₀ := hχ ▸ s.weil₀
  have tt := GlobalTheory.TensorTargetRule.tensorTarget D ψ hb.std B.V₀ B.A B.L B.o J.W₀
  funext h₁
  have hpt : ∀ h₀, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (B.o.boxT J.W₀ Ξ₁ Φ')) (omz (h₀, 1) Φ₀) 0 =
      omb (h₀, h₁) Ξ₁ 0 * thPair vL.μ vL.𝓕 Φ' Φ₀ := by
    intro h₀
    rw [tt.om_box s.χV χA χz s.om₀ omb omz hW₀ hb hz h₀ h₁ 1 Ξ₁ Φ' h1 h',
      ← GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B.L s.χV χz omz hz vL (h₀, 1) Φ' Φ₀ h' h0]
    have e : (fun v => B.o.boxT J.W₀ (omb (h₀, h₁) Ξ₁) (omz (h₀, 1) Φ') ((B.o.resT J.W₀).symm (0, v))) =
        fun v => omb (h₀, h₁) Ξ₁ 0 * omz (h₀, 1) Φ' v := by
      funext v
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply]
    simp only [contractT, e, thPair]
    rw [← integral_const_mul]
    congr 1; funext w
    have ew := congrFun e w
    rw [ew]; ring
  simp only [handP, hpt, Pi.smul_apply, smul_eq_mul, liftT_apply]
  rw [← integral_const_mul]
  congr 1; funext h₀; ring

end GlobalTheory.HandProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselHandedFunction_product_eq_coreLift_mul_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  first | exact @GlobalTheory.HandProd.handP_boxT | exact GlobalTheory.HandProd.handP_boxT | (intros; apply GlobalTheory.HandProd.handP_boxT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLift
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpFromBessel

variable {D : D7}

theorem pair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem per_smul {ρ : ℕ} (B : BesL D ρ) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (c • φ) f = c * B.per ψ φ f := by
  simp only [BesL.per, besPer, besFun, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem upFB : ∀ D : D7, UpFB D := by
  intro D ψ σ J B s 𝒮 Γ₀ K hL χA χz omb omz hχ hb hz φ G hφ hG hK Ξ₁ Φ₀ hΞ hΦ hne hvac hper
  by_contra hcon
  push_neg at hcon
  have hψ := s.weil.std
  obtain ⟨vL⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 B.L.rank J.W₀.rank
  have hvan := GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel D ψ σ J B s 𝒮 Γ₀ K hL vL _ _ omz hz φ G Φ₀ hφ hG hΦ hK hcon
  have htame := GlobalTheory.T.besselPeriod_handedDown_isTameThetaFunctional D ψ σ J B s vL _ _ omz hz φ G Φ₀ hφ hG hΦ
  obtain ⟨Φ, hΦS, hfl⟩ := hL.ne
  have hall := GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hψ J.W₀ B.V₀ Γ₀ _ htame _ (hL.vac Φ hΦS) hfl (fun w hw => by
    have h1 := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU
      (xLast B.d (vecB B.o B.ζ)) 0 Φ (hL.theta Φ hΦS)).2.1 w
    have h2 := hvan _ (hL.core Φ hΦS w hw)
    simp only [flFB, flatS] at h2 ⊢
    rw [h1] at h2
    exact h2) _ hvac
  have hlink := GlobalTheory.T.besselHandedFunction_product_eq_coreLift_mul_pairing D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ₀ Φ₀ hΞ hΦ hΦ
  simp only [hlink, per_smul] at hall
  exact hper ((mul_eq_zero.1 hall).resolve_left (pair_self_ne_zero hψ vL hΦ hne))

end GlobalTheory.UpFromBessel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift : ∀ D : D7, UpFB D := by
  first | exact @GlobalTheory.UpFromBessel.upFB | exact GlobalTheory.UpFromBessel.upFB | (intros; apply GlobalTheory.UpFromBessel.upFB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTower
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.RungJac

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.om = om ∧ s.χV = χV ∧ s.χW = χW ∧ s.vW = vW := by

  have hdesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨omA, hA⟩ := (hdesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hdesc ψ V₀ W χV χW omA hA).2 W₀ σ dW

  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨{ χV := χV, χW := χW, om := om, om₀ := om₀, weil := h, weil₀ := h₀, vW := vW, vS := vS, vT := vT, vU := vU },
    rfl, rfl, rfl, rfl⟩

private theorem rapidDec_star' {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : RapidDec V f) : RapidDec V (star f) := by
  refine ⟨fun γ hγ g => ?_, continuous_star.comp hf.2.1, fun N => ?_⟩
  · show star (f (γ * g)) = star (f g)
    rw [hf.1 γ hγ g]
  · obtain ⟨C, hC⟩ := hf.2.2 N
    exact ⟨C, fun g => by simpa only [Pi.star_apply, norm_star] using hC g⟩

private theorem isHeckeChar_of_isHeckeChar_mul {D : D7} {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ)
    (h' : IsHeckeChar D (χ * χ')) : IsHeckeChar D χ' := by
  have e : (χ' : (AE D)ˣ → Circle) = fun x => (χ x)⁻¹ * (χ * χ') x := by
    funext x
    simp
  refine ⟨?_, fun x => ?_⟩
  · rw [e]
    exact h.1.inv.mul h'.1
  · have hx := h'.2 x
    rw [MonoidHom.mul_apply, h.2 x, one_mul] at hx
    exact hx


set_option maxHeartbeats 1000000 in
theorem rungJ : FockTot → PartFixed → RungJ := by
  intro hFock hFix D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h h' hB
  obtain ⟨ρ, Φ, hne⟩ := hB
  have hi : 2 * k + 2 < D.R.m := by omega

  obtain ⟨c1, c2, -, c4, c5, c6, c7, c8, c9h, c9f⟩ :=
    GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 2) hi
  obtain ⟨c4a, c4b⟩ := c4 ⟨k + 1, by omega⟩
  rw [c4a, c4b] at c1

  have hex := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hc2 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c2⟩
  have hc1 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c1⟩
  have hEta : IsHeckeChar D L.eta := isHeckeChar_of_isHeckeChar_mul hc2.2.1 hc1.2.2.1
  obtain ⟨omz, hz⟩ : ∃ omz : Om (G.V (.core (2 * k + 2 + 1))) (negSp F.Lz),
      IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta omz := by
    refine hex _ _ W.ψ _ _ W.ψ_std hc2.2.1 hEta hc2.2.2.2.1 ?_
    show ResEta D L.eta F.Lz.rank
    rw [F.rk]
    exact GlobalTheory.HeckeCharacterRestriction.resEta_eta hL

  obtain ⟨s, hs_om, hs_χV, hs_χW, hs_vW⟩ := exists_step (F.dJ (k + 1) h) (F.dB k h') c1
    ⟨M.ν (.grid (2 * k + 2) 0), M.fd (.grid (2 * k + 2) 0), c9h, c9f⟩
  obtain ⟨𝒮, Γ₀, hLoc, hRow, hBox⟩ := hGood.fb k h h' s hs_om

  obtain ⟨f, hf, hΨi⟩ := hΨ.2 (2 * k + 2) hi
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hGood.lineNe (k + 1) h
  have hVf := (c5 f).1 hf
  have hRφ : RapidDec _ (star (Ψ (2 * k + 2 + 1))) := rapidDec_star' (hΨ.1 _ (by omega))
  have hRG : RapidDec _ (star (part W M ρ Φ u (2 * k + 2) h')) := rapidDec_star' (hu ρ Φ _ _)
  have hK : ∀ x ∈ lev G (.grid (2 * k + 2) 0), ∀ g,
      star (part W M ρ Φ u (2 * k + 2) h') (g * x) = star (part W M ρ Φ u (2 * k + 2) h') g :=
    fun x hx g => congrArg star (hFix D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k + 1) h' x hx g)

  have hper : (F.bes v k h').per W.ψ
      (liftT (omCore W (2 * k + 2)) (v (2 * k + 2 + 1)).μ (v (2 * k + 2 + 1)).𝓕 (star (Ψ (2 * k + 2 + 1))) (star f))
      (star (part W M ρ Φ u (2 * k + 2) h')) ≠ 0 := by
    rw [← c6 v f (Ψ (2 * k + 2 + 1)), ← hΨi]
    exact hne

  obtain ⟨Φ', hΦ'𝒮, hΦ'ne⟩ := GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift D W.ψ k (F.jac v (k + 1) h) (F.bes v k h') s 𝒮 Γ₀ _ hLoc
    (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta (omCore W (2 * k + 2)) omz hs_χW (by rw [hs_χV]; exact c2)
    (by rw [hs_χV]; exact hz) _ _ hRφ hRG hK (star f) Φ₀ hVf.1 hΦ₀.1 hΦ₀ne (hBox _ _ hVf hΦ₀) hper

  have hTame := (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ s.vW (star (part W M ρ Φ u (2 * k + 2) h')) hRG).2 (k + 1)
    (F.jac v (k + 1) h) _ _ s.om s.weil (negSp F.Lz) (F.ζ (k + 1)) _ _ omz hz (star (Ψ (2 * k + 2 + 1))) Φ₀ hRφ hΦ₀.1
  have hFk := hFock D hD T L μ0 hL sc G W M hM ⟨2 * k + 2, hi⟩ _ hTame
  obtain ⟨κ, P, hκP⟩ : ∃ κ P, (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (s.lift (star (part W M ρ Φ u (2 * k + 2) h')) (star (W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P))) Φ₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hΦ'ne (hFk hall Φ' (hRow Φ' hΦ'𝒮))

  have hpart : part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2) hi.le =
      part W M ρ Φ u (2 * k + 2) hi.le := by
    refine (c8 ρ Φ _ _ u fun j hj => ?_).symm
    have hj' : j ≠ ⟨2 * k + 2, hi⟩ := fun e => by
      rw [e] at hj
      exact lt_irrefl _ hj
    exact ⟨(Function.update_of_ne hj' P ρ).symm, (Function.update_of_ne hj' κ Φ).symm⟩
  have hdat : W.datum (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) ⟨2 * k + 2, hi⟩ =
      W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P := by
    simp only [GridData.Weil.datum, Function.update_self]
  have hlift := c7 (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u
  rw [hpart, hdat] at hlift
  have e2 : ∀ G0 X, s.lift G0 X = liftS (omRow W (2 * k + 2)) (M.ν (.grid (2 * k + 2) 0)) (M.fd (.grid (2 * k + 2) 0)) G0 X := by
    intro G0 X
    show liftS s.om s.vW.μ s.vW.𝓕 G0 X = _
    rw [hs_om, hs_vW]
  rw [e2] at hκP
  refine ⟨_, omz, hz, Function.update ρ ⟨2 * k + 2, hi⟩ P, Function.update Φ ⟨2 * k + 2, hi⟩ κ, Φ₀, hΦ₀, ?_⟩
  have key : (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (star (part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2 + 1) hi)) Φ₀ ≠ 0 := by
    rw [hlift]
    exact hκP
  exact key

end GlobalTheory.Asc.RungJac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTowerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower : FockTot → PartFixed → RungJ := by
  first | exact @GlobalTheory.Asc.RungJac.rungJ | exact GlobalTheory.Asc.RungJac.rungJ | (intros; apply GlobalTheory.Asc.RungJac.rungJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRung
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawPeriodNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawPeriodNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LastSeesaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

private lemma eq_one_of_subOne_mulVec_ratV_eq_zero {S : HSp D} (g : GA D S)
    (h : ∀ x : Fin S.rank → D.host.E, (subOne S g).mulVec (ratV x) = 0) : g = 1 := by
  have hm : subOne S g = 0 := by
    ext i j
    have hr : (ratV (Pi.single j (1 : D.host.E)) : Fin S.rank → AE D) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk; simp [ratV]
      · simp [ratV, hk]
    have hj := congrFun (h (Pi.single j 1)) i
    rw [hr, Matrix.mulVec_single] at hj
    simpa using hj
  have h1 : ((matHom S g).1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 1 := sub_eq_zero.mp hm
  have h2 : matHom S g = matHom S 1 := by
    rw [map_one]
    exact Units.ext h1
  exact (HR (AF D.host.F) D.sp.cm.sig S.gram).subtype_injective h2

theorem eq_one_of_mem_flagN {S S₀ : HSp D} (d : HypDec S S₀ 0) {n : GA D S} (hn : n ∈ flagN d) : n = 1 := by
  have hle : flagN d ≤ ⊥ := by
    unfold flagN NFlag
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, hg⟩
    refine Subgroup.mem_bot.2 (eq_one_of_subOne_mulVec_ratV_eq_zero g fun x => ?_)
    obtain ⟨a, ha⟩ := hg x (Subsingleton.elim _ _)
    rw [ha]
    ext i
    simp [Matrix.mulVec, dotProduct]
  exact Subgroup.mem_bot.1 (hle hn)

theorem per_zero (J : JacL D 0) {L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (omz : Om J.W₀ L') (φ : GA D J.W₀ → ℂ)
    (f : GA D J.W → ℂ) (Φ₀ : WO J.W₀ L' → ℂ) :
    J.per ψ ζ' omz φ f Φ₀ = ∫ g in J.v0.𝓕, φ g * f (J.d.emb0 g) * star (omz (g, 1) Φ₀ 0) ∂J.v0.μ := by
  have hν : J.vN.ν J.vN.𝓝 = 1 := J.vN.unit.2.2
  have hX : ∀ (T : HSp D) (x : Mx D T.rank 0), J.d.extX T x = 0 := by
    intro T x
    rw [HypDec.extX_apply]
    ext i j
    simp [Matrix.mul_apply]
  have hs : symplO J.W L' (0 : WO J.W L') 0 = 0 := by
    have h := GlobalTheory.Asc.symplO_swap (S := J.W) (T := L') (0 : WO J.W L') 0
    have h2 : symplO J.W L' 0 0 + symplO J.W L' 0 0 = 0 := by
      nth_rw 1 [h]
      exact neg_add_cancel _
    have h3 : algebraMap D.host.F (AF D.host.F) 2 * symplO J.W L' 0 0 = 0 := by
      rw [map_ofNat, two_mul, h2]
    have h4 := congrArg (fun t => algebraMap D.host.F (AF D.host.F) 2⁻¹ * t) h3
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul, mul_zero] at h4
    exact h4
  have hp : psiFlag ψ J.d 1 = 1 := by
    simp [psiFlag, upSum, psiE_zero]
  have hc : ∀ (h : GA D J.W₀) (n : flagN J.d),
      fjSrcFun ψ J.d ζ' omz φ f Φ₀ h n = φ h * f (J.d.emb0 h) * star (omz (h, 1) Φ₀ 0) := by
    intro h n
    have hn : n.1 = 1 := eq_one_of_mem_flagN J.d n.2
    simp only [fjSrcFun, thetaJS, jacS, ptS, cenS, hn, hp, hX, one_mul, Matrix.zero_mul, heisO_zero, star_one, mul_one]
    simp [symplOH, hs]
  simp only [JacL.per, fjSrc]
  congr 1
  funext h
  simp_rw [hc h]
  rw [setIntegral_const]
  simp [Measure.real, hν]

theorem integrable_norm_mul_pow {V : HSp D} (v : GlobalTheory.Unf.Vol V) {φ : GA D V → ℂ} (hφ : RapidDec V φ) (k : ℕ) :
    Integrable (fun g => ‖φ g‖ * quotHeight V g ^ k) (v.μ.restrict v.𝓕) := by
  have hm : AEStronglyMeasurable (fun g => ((quotHeight V g ^ k : ℝ) : ℂ)) (v.μ.restrict v.𝓕) :=
    (Complex.continuous_ofReal.comp ((GlobalTheory.Grow.continuous_quotHeight V).pow k)).aestronglyMeasurable
  have hI := hφ.integrableOn_mul_of_le v.haar v.fund hm (C := 1) (A := k) (fun g => by
    rw [one_mul, Complex.norm_real, norm_pow, Real.norm_of_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le])
  refine hI.norm.congr (ae_of_all _ fun g => ?_)
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, norm_pow, Real.norm_of_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le]
  ring

theorem tame_double {S X T L : HSp D} (o : OrthDec X T L) {χS χX : (AE D)ˣ →* Circle} {omX : Om S X}
    (hX : IsWeilDatumO ψ S X χS χX omX) (vS : GlobalTheory.Unf.Vol S) (vT : GlobalTheory.Unf.Vol T) {φ : GA D S → ℂ} {u : GA D T → ℂ}
    (hφ : RapidDec S φ) (hu : RapidDec T u) :
    (∀ f, IsThetaFunO ψ S X f → Integrable (fun y : GA D S × GA D T => φ y.1 * u y.2 * omX (y.1, o.emb (y.2, 1)) f 0)
      ((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕))) ∧
    Tame ψ S X fun f => ∫ y : GA D S × GA D T, φ y.1 * u y.2 * omX (y.1, o.emb (y.2, 1)) f 0
      ∂((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕)) := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D S).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D S).1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).1
  have := vS.haar
  have := vT.haar
  obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D X T L o
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have h1 := (hC 1).2
    have h2 := GlobalTheory.Grow.quotHeight_pos _ (o.emb ((1 : GA D T), 1))
    have h3 : 0 < quotHeight T (1 : GA D T) ^ a := pow_pos (GlobalTheory.Grow.quotHeight_pos _ _) a
    nlinarith
  have hemb : Continuous fun y : GA D S × GA D T => o.emb (y.2, 1) :=
    o.continuous_emb.comp (continuous_snd.prodMk continuous_const)
  have hint : ∀ k : ℕ, Integrable (fun y : GA D S × GA D T =>
      ‖φ y.1 * u y.2‖ * (quotHeight S y.1 * quotHeight X (o.emb (y.2, 1))) ^ k)
      ((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕)) := by
    intro k
    have h1 := integrable_norm_mul_pow vS hφ k
    have h2 := integrable_norm_mul_pow vT hu (a * k)
    have hp := (MeasureTheory.Integrable.mul_prod h1 h2).const_mul (C ^ k)
    refine hp.mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((((hφ.2.1.comp continuous_fst).mul (hu.2.1.comp continuous_snd)).norm).mul
        ((((GlobalTheory.Grow.continuous_quotHeight _).comp continuous_fst).mul ((GlobalTheory.Grow.continuous_quotHeight _).comp hemb)).pow k)).aestronglyMeasurable
    · have hS0 : 0 ≤ quotHeight S y.1 := (GlobalTheory.Grow.quotHeight_pos _ _).le
      have hX0 : 0 ≤ quotHeight X (o.emb (y.2, 1)) := (GlobalTheory.Grow.quotHeight_pos _ _).le
      have hle : quotHeight X (o.emb (y.2, 1)) ≤ C * quotHeight T y.2 ^ a := (hC y.2).2
      have hlin : quotHeight S y.1 * quotHeight X (o.emb (y.2, 1)) ≤ C * (quotHeight S y.1 * quotHeight T y.2 ^ a) := by
        nlinarith [mul_le_mul_of_nonneg_left hle hS0]
      have hpow : (quotHeight S y.1 * quotHeight X (o.emb (y.2, 1))) ^ k ≤
          C ^ k * (quotHeight S y.1 ^ k * quotHeight T y.2 ^ (a * k)) := by
        calc _ ≤ (C * (quotHeight S y.1 * quotHeight T y.2 ^ a)) ^ k := pow_le_pow_left₀ (mul_nonneg hS0 hX0) hlin k
          _ = _ := by rw [mul_pow, mul_pow, ← pow_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg hS0 hX0) k)), norm_mul]
      calc ‖φ y.1‖ * ‖u y.2‖ * (quotHeight S y.1 * quotHeight X (o.emb (y.2, 1))) ^ k
          ≤ ‖φ y.1‖ * ‖u y.2‖ * (C ^ k * (quotHeight S y.1 ^ k * quotHeight T y.2 ^ (a * k))) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = C ^ k * (‖φ y.1‖ * quotHeight S y.1 ^ k * (‖u y.2‖ * quotHeight T y.2 ^ (a * k))) := by ring
  exact GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ S X χS χX omX hX (GA D S × GA D T) ((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕))
    (fun y => φ y.1 * u y.2) (fun y => y.1) (fun y => o.emb (y.2, 1)) (fun _ => 0)
    ((hφ.2.1.comp continuous_fst).mul (hu.2.1.comp continuous_snd)).measurable continuous_fst hemb continuous_const hint

private lemma negSp_negSp (L : HSp D) : negSp (negSp L) = L := by
  cases L
  dsimp only [negSp]
  congr 1
  exact neg_neg _

private lemma exists_isWeilDatumO_star_of_isWeilDatumO_negSp {S L M : HSp D} (e : negSp (negSp L) = M) {χS χz : (AE D)ˣ →* Circle}
    {omz : Om S (negSp L)} (hz : IsWeilDatumO ψ S (negSp L) χS⁻¹ χz omz) :
    ∃ omL : Om S M, IsWeilDatumO ψ S M χS χz⁻¹ omL ∧
      ∀ g (f : WO S (negSp L) → ℂ) (F : WO S M → ℂ), HEq F (star f) → omL (g, 1) F 0 = star (omz (g, 1) f 0) := by
  subst e
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget omz, ?_, ?_⟩
  · simpa using (GlobalTheory.ConjWeil.conj_isWeilDatumO D ψ S (negSp L) χS⁻¹ χz omz hz).1
  · intro g f F hF
    obtain rfl := eq_of_heq hF
    have hcf : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f : WO S (negSp (negSp L)) → ℂ) = f := by
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [GlobalTheory.ConjWeil.conjTarget_apply, hcf]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem exists_conj {S L : HSp D} {χS χz : (AE D)ˣ →* Circle} {omz : Om S (negSp L)}
    (hz : IsWeilDatumO ψ S (negSp L) χS⁻¹ χz omz) : ∃ omL : Om S L, IsWeilDatumO ψ S L χS χz⁻¹ omL ∧
      ∀ g (f : WO S (negSp L) → ℂ), IsThetaFunO ψ S (negSp L) f →
        omL (g, 1) (star f : WO S L → ℂ) 0 = star (omz (g, 1) f 0) := by
  obtain ⟨omL, h1, h2⟩ := exists_isWeilDatumO_star_of_isWeilDatumO_negSp (negSp_negSp L) hz
  exact ⟨omL, h1, fun g f _ => h2 g f _ HEq.rfl⟩

theorem star_neg (hψ : IsStdChar D ψ (-1)) (S L : HSp D) (f : WO S (negSp L) → ℂ) :
    (IsThetaFunO ψ S (negSp L) f → IsThetaFunO ψ S L (star f : WO S L → ℂ)) ∧
      ∀ w : WO S L, heisO ψ S L w (star f : WO S L → ℂ) = (star (heisO ψ S (negSp L) w f) : WO S L → ℂ) := by
  have H := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S L
  have hcf : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f : WO S L → ℂ) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  refine ⟨fun hf => (H.1 (star f)).1.1 (by rw [hcf]; exact hf), fun w => ?_⟩
  have h := (H.2 w (star f)).1
  rw [hcf] at h
  rw [h]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem upLast : ∀ D : D7, UpLast D := by
  intro D ψ J X T L'' o Γ ΓL ΓX _ hLL ζ' χS χT χz om omX omz hom homX homz vT φ u hφ hu Ξ hΞ hne
  have hψ : IsStdChar D ψ (-1) := homX.std
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W₀).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W₀).1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).1
  have := J.v0.haar
  have := vT.haar
  obtain ⟨hIntg, hTame⟩ := tame_double (ψ := ψ) o homX J.v0 vT hφ hu

  have hval : ∀ F : WO J.W₀ X → ℂ, IsThetaFunO ψ J.W₀ X F →
      (∫ y : GA D J.W₀ × GA D T, φ y.1 * u y.2 * omX (y.1, o.emb (y.2, 1)) F 0
        ∂((J.v0.μ.restrict J.v0.𝓕).prod (vT.μ.restrict vT.𝓕))) =
      ∫ h in vT.𝓕, liftT omX J.v0.μ J.v0.𝓕 φ F (o.emb (h, 1)) * u h ∂vT.μ := by
    intro F hF
    rw [MeasureTheory.integral_prod_symm _ (hIntg F hF)]
    congr 1
    funext h
    rw [liftT_apply, ← integral_mul_const]
    congr 1
    funext g
    ring

  obtain ⟨f₁, f₂, hf₁, hf₂, hf₁0, hf₂0, hbox⟩ := hLL.ex
  have hf₀ : GlobalTheory.MixModel.OrthDec.boxT o J.W₀ (fun w => f₁ (J.d.ext0 T w)) (star f₂) ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hf₁0
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hf₂0
    have hx' : f₁ x ≠ 0 := hx
    have hy' : f₂ y ≠ 0 := hy
    intro h0
    have h1 := congrFun h0 ((o.resT J.W₀).symm ((GlobalTheory.WeilSrc.Zero.eqv J.d T).symm x, y))
    simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, Pi.star_apply] at h1
    rw [← GlobalTheory.WeilSrc.Zero.eqv_apply, AddEquiv.apply_symm_apply] at h1
    exact mul_ne_zero hx' (star_ne_zero.2 hy') h1

  obtain ⟨omL, homL, hconj⟩ := exists_conj (ψ := ψ) (S := J.W₀) (L := L'') homz
  have hpull := GlobalTheory.WeilSrc.Zero.isWeilDatumO_pull J.d hom
  have hTT := GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ X T L'' o J.W₀

  have hsee : ∀ (Φ : WO J.W T → ℂ) (Φ₀ : WO J.W₀ (negSp L'') → ℂ), IsThetaFunO ψ J.W T Φ →
      IsThetaFunO ψ J.W₀ (negSp L'') Φ₀ →
      (∫ y : GA D J.W₀ × GA D T, φ y.1 * u y.2 *
        omX (y.1, o.emb (y.2, 1)) (o.boxT J.W₀ (fun w => Φ (J.d.ext0 T w)) (star Φ₀)) 0
        ∂((J.v0.μ.restrict J.v0.𝓕).prod (vT.μ.restrict vT.𝓕))) =
      J.per ψ ζ' omz φ (liftS om vT.μ vT.𝓕 u Φ) Φ₀ := by
    intro Φ Φ₀ hΦ hΦ₀
    have hA : IsThetaFunO ψ J.W₀ T (fun w => Φ (J.d.ext0 T w)) := (GlobalTheory.WeilSrc.Zero.theta_iff J.d Φ).2 hΦ
    have hB : IsThetaFunO ψ J.W₀ L'' (star Φ₀ : WO J.W₀ L'' → ℂ) := (star_neg hψ J.W₀ L'' Φ₀).1 hΦ₀
    have hpt : ∀ (g : GA D J.W₀) (h : GA D T),
        omX (g, o.emb (h, 1)) (o.boxT J.W₀ (fun w => Φ (J.d.ext0 T w)) (star Φ₀)) 0 =
          om (J.d.emb0 g, h) Φ 0 * star (omz (g, 1) Φ₀ 0) := by
      intro g h
      rw [hTT.om_box χS χT χz⁻¹ omX _ omL homX hpull homL g h 1 _ _ hA hB, hTT.box_zero,
        hconj g Φ₀ hΦ₀, GlobalTheory.WeilSrc.Zero.pull_apply]
      have hfx : (fun x => Φ (J.d.ext0 T ((GlobalTheory.WeilSrc.Zero.eqv J.d T).symm x))) = Φ := by
        funext x
        rw [← GlobalTheory.WeilSrc.Zero.eqv_apply, AddEquiv.apply_symm_apply]
      simp only [hfx, map_zero]
    rw [per_zero, MeasureTheory.integral_prod _ (hIntg _ (hTT.box_theta _ _ hA hB))]
    congr 1
    funext g
    simp_rw [hpt]
    rw [liftS_apply, mul_comm (φ g) _, mul_assoc, ← integral_mul_const]
    congr 1
    funext h
    ring
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hval Ξ hΞ.1]
  refine GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hψ J.W₀ X ΓX _ hTame _ hbox hf₀ (fun w hw => ?_) Ξ hΞ
  obtain ⟨hw1, hw2⟩ := hLL.ann w hw
  have hΦ := (GlobalTheory.Asc.annVac D ψ hψ J.W T Γ).1 f₁ hf₁ _ hw1
  have hΦ₀ := (GlobalTheory.Asc.annVac D ψ hψ J.W₀ (negSp L'') ΓL).1 f₂ hf₂ _ hw2
  have e1 : heisO ψ J.W₀ T (o.resT J.W₀ w).1 (fun w => f₁ (J.d.ext0 T w)) =
      fun w' => heisO ψ J.W T (J.d.ext0 T (o.resT J.W₀ w).1) f₁ (J.d.ext0 T w') := by
    have h := GlobalTheory.WeilSrc.Zero.heisO_eqv (ψ := ψ) J.d (o.resT J.W₀ w).1 f₁
    simp only [GlobalTheory.WeilSrc.Zero.eqv_apply] at h
    exact h.symm
  have e2 := (star_neg hψ J.W₀ L'' f₂).2 (o.resT J.W₀ w).2
  rw [o.heisO_boxT ψ J.W₀, e1, e2, hsee _ _ hΦ.1 hΦ₀.1]
  exact hcon _ _ hΦ hΦ₀

end GlobalTheory.LastSeesaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawPeriodNonvanishingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeesaw_periodNonvanishing : ∀ D : D7, UpLast D := by
  first | exact @GlobalTheory.LastSeesaw.upLast | exact GlobalTheory.LastSeesaw.upLast | (intros; apply GlobalTheory.LastSeesaw.upLast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRung
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.AscBottom

variable {D : D7}

theorem rapidDec_star {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun γ hγ g => by simp [Pi.star_apply, h1 γ hγ g], h2.star, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  exact ⟨C, fun g => by simpa [Pi.star_apply, norm_star] using hC g⟩

theorem rung0 (hF : FockTot) : Rung0 := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h
  have hm : 0 < D.R.m := by omega
  obtain ⟨hom, homC, -, hev, hdep, hdn, hpart, -, -, -⟩ := GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hq T L μ0 hL sc G W M hM 0 hm
  obtain ⟨hchT, hchS⟩ := hev ⟨0, rfl⟩
  obtain ⟨hrap, hch⟩ := hΨ
  obtain ⟨f, hf, hΨ0⟩ := hch 0 hm
  have hhf := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vT : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hhf.1, hhf.2⟩
  let ρ₀ : G.RealVec := fun _ => 0
  let Φ₀ : G.Datum := fun _ => default
  have hu' : RapidDec (Yc D 0) (star u) := rapidDec_star (hu ρ₀ Φ₀ 0 (Nat.zero_le _))
  have hφ : RapidDec (G.V (.core 1)) (star (Ψ 1)) := rapidDec_star (hrap 1 (by omega))

  set a := G.ch.chi (D.R.m - 0) with ha
  have homR : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta) (omRow W 0) := by
    have := hom
    rwa [hchS, hchT] at this
  have homX : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta * L.eta⁻¹) (omCore W 0) := by
    rw [mul_inv_cancel_right]; exact homC
  have hHeta : IsHeckeChar D L.eta := by
    have := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homR.hecS) homR.hecT
    rwa [inv_inv, mul_inv_cancel_left] at this
  have hReta : ResEta D L.eta (negSp F.Lz).rank := by
    have h1 := Formalism.L2.Theta.resEta_mul (Formalism.L2.Theta.resEta_inv homC.resT) homR.resT
    rw [inv_inv, mul_inv_cancel_left] at h1
    refine Formalism.L2.Theta.resEta_parity h1 ?_
    have hr : (G.V (.grid 0 0)).rank + 1 = (G.V (.core 0)).rank := by
      have := F.oz.rank_add; rw [F.rk] at this; exact this
    show _ = F.Lz.rank % 2
    rw [F.rk]
    omega
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.core 1)) (negSp F.Lz) W.ψ a⁻¹⁻¹ L.eta W.ψ_std
    (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homX.hecS) hHeta (Formalism.L2.Theta.resEta_inv homX.resS) hReta

  have hΞ : VacG W.ψ _ _ (latCore G 0) (star f) := (hdep f).1 hf
  have hlift : liftT (omCore W 0) (v 1).μ (v 1).𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := by
    rw [hΨ0]; exact (hdn v f (Ψ 1)).symm
  have hint : (∫ x in vT.𝓕, liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) (F.oz.emb (x, 1)) *
      star u x ∂vT.μ) ≠ 0 := by
    have e : (fun x : GA D (Yc D 0) => liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f)
        (F.oz.emb (x, 1)) * star u x) = fun x => (starRingEnd ℂ) (Ψ 0 (stabilizerEmbedding G.sp.dec0 x) * u x) := by
      funext x
      have hl : liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := hlift
      rw [hl, hE.bot x, map_mul]; rfl
    rw [e, integral_conj]
    intro h0
    apply hper
    have := congrArg (starRingEnd ℂ) h0
    rw [Complex.conj_conj, map_zero] at this
    exact this
  obtain ⟨Φ', Φz, hΦ', hΦz, hne⟩ := GlobalTheory.T.lastSeesaw_periodNonvanishing D W.ψ (F.jac v 0 h) (G.V (.core 0)) (Yc D 0) F.Lz F.oz (latRow G 0) (ΓL 0)
    (latCore G 0) F.rk (hG.last h) (F.ζ 0) a⁻¹ (a⁻¹ * L.eta) L.eta (omRow W 0) (omCore W 0) omz homR homX homz vT
    (star (Ψ 1)) (star u) hφ hu' (star f) hΞ hint

  let ℓ : (WO (G.V (.grid 1 0)) (G.V (.grid 0 0)) → ℂ) → ℂ := fun Φ =>
    (F.jac v 0 h).per W.ψ (F.ζ 0) omz (star (Ψ 1)) (liftS (omRow W 0) vT.μ vT.𝓕 (star u) Φ) Φz
  have hT : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ (Yc D 0) vT (star u) hu').2 0 (F.jac v 0 h) a⁻¹ (a⁻¹ * L.eta) (omRow W 0) homR (negSp F.Lz)
      (F.ζ 0) a⁻¹⁻¹ L.eta omz homz (star (Ψ 1)) Φz hφ hΦz.1
  have hK : ∃ κ P, ℓ (star (W.fock (.chi 0 0) (W.cosVec 0 κ) P)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hne (hF D hq T L μ0 hL sc G W M hM ⟨0, hm⟩ ℓ hT hno Φ' hΦ')
  obtain ⟨κ, P, hκP⟩ := hK
  let ρ : G.RealVec := Function.update ρ₀ ⟨0, hm⟩ P
  let Φ : G.Datum := Function.update Φ₀ ⟨0, hm⟩ κ
  refine ⟨a⁻¹⁻¹, omz, homz, ρ, Φ, Φz, hΦz, ?_⟩
  have hp := hpart ρ Φ u
  have hd : W.datum ρ Φ ⟨0, hm⟩ = W.fock (.chi 0 0) (W.cosVec 0 κ) P := by
    show W.fock (.chi 0 0) (W.cosVec 0 (Φ ⟨0, hm⟩)) (ρ ⟨0, hm⟩) = _
    simp only [ρ, Φ, Function.update_self]
  rw [hd] at hp
  change ℓ _ ≠ 0 at hκP
  convert hκP using 2
  exact hp

end GlobalTheory.AscBottom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRungStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_thetaTower_bottom_rung : FockTot → Rung0 := by
  first | exact @GlobalTheory.AscBottom.rung0 | exact GlobalTheory.AscBottom.rung0 | (intros; apply GlobalTheory.AscBottom.rung0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  intro hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper
  obtain ⟨F, hE, ΓL, hG⟩ := hT D hq T L μ0 hL sc G W M hM v
  have key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h := by
    intro k
    induction k with
    | zero =>
      intro h
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h
        (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)
    | succ k ih =>
      intro h
      have h' : 2 * k + 2 ≤ D.R.m := by omega
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h
        (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))
  obtain ⟨r, hr⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hk : 2 * (r - 1) + 2 ≤ D.R.m := by omega
  have hk' : 2 * (r - 1) + 2 = D.R.m := by omega
  obtain ⟨ρ, Φ, hne⟩ := key (r - 1) hk
  refine ⟨ρ, Φ, ?_⟩
  let f : ∀ i, Fn G (.grid i 0) := fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0
  have hf : f D.R.m = thetaChi W M ρ Φ u := by
    simp only [f, dif_pos le_rfl]; rfl
  have := hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by
    simp only [f, dif_pos hk]; exact hne)
  rwa [hf] at this

end GlobalTheory.Asc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_ascent_of_tower_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_rungs | exact GlobalTheory.Asc.ascent_of_rungs | (intros; apply GlobalTheory.Asc.ascent_of_rungs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem partFixed_of_depFixed : DepFixed → DatumDep → PartFixed := by
  intro hD hd D q T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  have hf := hd D q T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩
  have key := hD D q T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ hf 1 (one_mem _) k hk
  show liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ (g * k) = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ g
  rw [liftA_apply, liftA_apply]
  congr 1
  funext x
  congr 1
  show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
  have e : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) =
      (negGA _ g, x) * G.toPair (.chi i 0) 1 k := by
    show _ = (negGA _ g, x) * (negGA _ k, 1)
    rw [map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.Asc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData : DepFixed → DatumDep → PartFixed := by
  first | exact @GlobalTheory.Asc.partFixed_of_depFixed | exact GlobalTheory.Asc.partFixed_of_depFixed | (intros; apply GlobalTheory.Asc.partFixed_of_depFixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_depFixed : DepFixed → Ascent := fun hD =>
  have hTot : FockTot := GlobalTheory.T.fockConjugates_span_depth_data
  have hPart : PartFixed := GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData hD GlobalTheory.T.firstRow_data_have_depth
  GlobalTheory.T.besselPeriod_ascent_of_tower_rungs (GlobalTheory.T.existsGoodGridFrames_of_depthFixed hD) (GlobalTheory.T.nonvanishing_thetaTower_bottom_rung hTot) (GlobalTheory.T.fourierJacobi_to_bessel_nonvanishing_tower hTot hPart)
    (GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower hTot hPart)

end GlobalTheory.Asc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data : DepFixed → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_depFixed | exact GlobalTheory.Asc.ascent_of_depFixed | (intros; apply GlobalTheory.Asc.ascent_of_depFixed <;> assumption)
end

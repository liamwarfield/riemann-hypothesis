module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullChartDens

theorem chernDens_pull_of_chart : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w) := by
  intro k _ X Y p q σ D π hπ B φ hφ c c' H z hz
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (φ.pull π hπ).isLB z) PUnit.unit
  rw [AlgChart.chernDens, AlgChart.chernDens, c.hess_eq hφ hz' hj (mem_pick _ _), AlgChart.hess,
    AlgChart.hess, ← (H z hz).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (φ.pull_φ π hπ _ _)

end GlobalTheory.PullChartDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChartStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w) := by
  first | exact @GlobalTheory.PullChartDens.chernDens_pull_of_chart | exact GlobalTheory.PullChartDens.chernDens_pull_of_chart | (intros; apply GlobalTheory.PullChartDens.chernDens_pull_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaIntegralLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_om_one (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (k h : UA σ W.J) :
    M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (om (1, k) Φ)) = thetaSum F (om (g, h * k) Φ)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_smul (M : Model σ Y W) (om : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) :
    M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I theta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (c • Φ)) = c * thetaSum F (om (g, h) Φ)
  rw [map_smul, thetaSum_smul]

theorem I_add (M : Model σ Y W) (om : Rep σ Y W) (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J) : M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← integral_add (hconv Φ hΦ h) (hconv Ψ hΨ h)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (Φ + Ψ)) = thetaSum F (om (g, h) Φ) + thetaSum F (om (g, h) Ψ)
  rw [map_add (f := _), thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΨ)]

theorem snd_eq_zero_of_at {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
  have hu : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun (hz u hu) i)
  rwa [one_mul] at h1

end GlobalTheory.ThetaIntegralLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsValsReal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ThetaLevel

theorem isGenSec_real {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := by
  intro s
  obtain ⟨r, hr, -⟩ := ρ.th₁_basis s
  exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩

end GlobalTheory.ThetaLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_real_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  intro o Ω _ _ _ _ S ρ K _ i
  haveI : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp S.R))
  haveI : IsAffine (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp K))
  exact GlobalTheory.EmbPull.isGenSec_pullS ρ.P GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny _ (GlobalTheory.ThetaLevel.isGenSec_real ρ)

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  intro o Ω _ _ _ _ S ρ K _ i
  exact GlobalTheory.UMin.isGenSec_real_pull o Ω S ρ K i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTLiftLie

theorem exists_factor_of_sq_zero {C C₀ k : Type} [CommRing C] [CommRing C₀] [Field k] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (x : Sp k ⟶ Sp C) :
    ∃ ψ : C₀ →+* k, x = spMap ψ ≫ spMap π := by
  let φ : C →+* k := (Spec.preimage x).hom
  have hx : x = spMap φ := by
    show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
    simp
  have hker : RingHom.ker π ≤ RingHom.ker φ := by
    intro a ha
    have h2 : a * a ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ha ha
    rw [hsq] at h2
    have h0 : a * a = 0 := by simpa using h2
    have : φ a * φ a = 0 := by rw [← map_mul, h0, map_zero]
    exact RingHom.mem_ker.2 (mul_self_eq_zero.1 this)
  have hc : (RingHom.liftOfSurjective π hπ ⟨φ, hker⟩).comp π = φ :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  generalize RingHom.liftOfSurjective π hπ ⟨φ, hker⟩ = ψ at hc
  refine ⟨ψ, ?_⟩
  rw [hx, ← hc]
  show Spec.map (CommRingCat.ofHom (ψ.comp π)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π)
  rw [← Spec.map_comp]
  rfl

theorem lieMult_of_sqZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h act hact k _ _ x β hx j
  obtain ⟨ψ, rfl⟩ := exists_factor_of_sq_zero π hπ hsq x
  have hact' : ∀ c, ((o₀.act.toF D).act c).left ≫ i = i ≫ ((act.toF D).act c).left :=
    fun c => hact _
  refine (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp C) (Sp C₀) A o₀.A (spMap π) i (act.toF D) (o₀.act.toF D)
    h hact' k (spMap ψ) (β.comp (b.t j)) D.m).1 ?_
  exact o₀.lieRank k (spMap ψ) β (by rw [← hx, Category.assoc]) j

end GlobalTheory.HTLiftLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  first | exact @GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift | exact GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift | (intros; apply GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrDiv

theorem dvd_of_forall_cDvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, ht⟩ := h W hW φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

end GlobalTheory.DvrDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  first | exact @GlobalTheory.DvrDiv.dvd_of_forall_cDvr | exact GlobalTheory.DvrDiv.dvd_of_forall_cDvr | (intros; apply GlobalTheory.DvrDiv.dvd_of_forall_cDvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem hasDiv_of_pCrd_pt : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω)
    (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  intro k Ω o _ _ _ _ M n g e hP z
  obtain ⟨τ, -, H⟩ := hP
  obtain ⟨c, hc⟩ := GlobalTheory.ProjSpace.exists_mem_chart o n (g z)
  let W : M.Z.Opens := g ⁻¹ᵁ GlobalTheory.ProjSpace.chart o n c
  have hzW : z ∈ W := hc
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨z, hzW⟩
  let j : PUnit → (GlobalTheory.ProjSpace.O1 o n).ι := fun _ => c
  let V := ((GlobalTheory.ProjSpace.O1 o n).pull (M.pt ≫ g)).U j
  have hV : V ≤ (M.pt ≫ g) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o n).U (j PUnit.unit) :=
    LB.wchart_le (GlobalTheory.ProjSpace.O1 o n) (fun _ => M.pt ≫ g) j PUnit.unit
  have hV' : ⊤ ≤ V := fun y _ => Set.mem_iInter.2 fun _ => hW (Set.mem_univ y)
  let ev : Γ(Sp Ω, V) →+* Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp ((Sp Ω).presheaf.map (homOfLE hV').op).hom
  have hconst : ∀ a : Ω, ev (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a := by
    intro a
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (((Sp Ω).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      (Sp Ω).presheaf.map (homOfLE hV').op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a
    rw [← Functor.map_comp]
    have : ((homOfLE (le_top : V ≤ ⊤)).op ≫ (homOfLE hV').op : Opposite.op (⊤ : (Sp Ω).Opens) ⟶ _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    exact (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv_hom_id_apply a
  have hval : ∀ i, ev (((M.pt ≫ g).appLE _ _ hV).hom ((GlobalTheory.ProjSpace.coord o n i).f (j PUnit.unit))) =
      valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    intro i
    rw [valF, dite_eq_left hW]
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (resG (Sp Ω) hV' _) = _
    rw [GlobalTheory.ProjSpace.resG_appLE, GlobalTheory.ProjSpace.pullRatio, GlobalTheory.ProjSpace.appLE_appLE]
    rfl
  have key : ∀ i, valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) = e i * ev (τ.s j).val := by
    intro i
    rw [← hval, H i j hV, map_mul, hconst]
  have h1 : e c * ev (τ.s j).val = 1 := by
    rw [← key c, GlobalTheory.ProjSpace.pullRatio_self, ← M.res_apply W ⟨z, hzW⟩, map_one]
  have hc0 : e c ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨c, hc0, fun i => ?_⟩
  have e1 : e i / e c = valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    rw [key i, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]
  rw [e1]
  exact RatModel.valF_mem_O hzW _

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  first | exact @GlobalTheory.UMin.hasDiv_of_pCrd_pt | exact GlobalTheory.UMin.hasDiv_of_pCrd_pt | (intros; apply GlobalTheory.UMin.hasDiv_of_pCrd_pt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_mul_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {m : G'.left ⟶ G.left} (hm : IsGrpPullback G' G f m) (T : Over S') (x y : T ⟶ G')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ x₀ y₀ : Over.mk s ⟶ G, x₀.left = x.left ≫ m ∧ y₀.left = y.left ≫ m ∧ (x₀ * y₀).left = (x * y).left ≫ m := by
  subst hs
  have e : ∀ z : T ⟶ G', (z.left ≫ m) ≫ G.hom = T.hom ≫ f := fun z ↦ by
    rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w z]
  exact ⟨Over.homMk (x.left ≫ m) (e x), Over.homMk (y.left ≫ m) (e y), rfl, rfl, hm.2 T x y _ _ rfl rfl⟩

end

theorem IsTransl.isTranslate_comp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] (x0 : Sp K ⟶ X) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) {R : Type} [CommRing R] (ψ : R →+* K) (v : Sp (DualNumber R) ⟶ t.G.left) (u : epsR K ⟶ A) (hu : u.left ≫ m = spMap (dualMap ψ) ≫ v) {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x u w), LogKS.IsTranslate t (φ.comp ψ) (x ≫ m) v (w ≫ m) := by
  intro E _ _ _ H X t K _ x0 A _ m hm R _ ψ v u hu B _ φ x hx w hw
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hw
  have sc : ∀ {P Q T : Type} [CommRing P] [CommRing Q] [CommRing T] (f : P →+* Q) (g : Q →+* T),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g ↦ by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have dc : (dualMap φ).comp (dualMap ψ) = dualMap (φ.comp ψ) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap]
  obtain ⟨x₀, y₀, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ t.G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ x0
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, sc])
  refine ⟨x₀, y₀, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← sc (dualMap ψ) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hu]; exact (Category.assoc (spMap (dualMap φ)) (spMap (dualMap ψ)) v).symm

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupSchemeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranslateOfTangentVector_fibre_to_groupScheme : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] (x0 : Sp K ⟶ X) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) {R : Type} [CommRing R] (ψ : R →+* K) (v : Sp (DualNumber R) ⟶ t.G.left) (u : epsR K ⟶ A) (hu : u.left ≫ m = spMap (dualMap ψ) ≫ v) {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x u w), LogKS.IsTranslate t (φ.comp ψ) (x ≫ m) v (w ≫ m) := by
  first | exact @GlobalTheory.CechKS.IsTransl.isTranslate_comp | exact GlobalTheory.CechKS.IsTransl.isTranslate_comp | (intros; apply GlobalTheory.CechKS.IsTransl.isTranslate_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobAdjoint

section Dual

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {P : LB (A ⊗ A).left}


end Dual

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

end Down

section Frob

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {A A₁ : Over (Sp R)} [GrpObj A] [GrpObj A₁]
  {π : A₁.left ⟶ A.left}

variable {G : PDivGroup p R} (t : G.TorsionTower A)

theorem absFrob_y (n : ℕ) : spMap ((absFrob hR G).app n).toRingHom ≫ (t.y n).left =
    (t.y n).left ≫ VB.frob A.left p (cast_left p R hR A) := by
  have h := natCast_eq_zero_of_algebra hR (G.A n)
  exact (congrArg (· ≫ (t.y n).left) (frob_sp p _ h (SS.FrobField.cast_zero_sp _ h)).symm).trans
    (VB.frob_naturality p _ (t.y n).left _)

theorem exists_tower (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) :
    ∃ t₁ : (frobTwist hR G).TorsionTower A₁, ∀ n,
      spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π :=
  letI := (frobRing hR).toAlgebra
  ⟨t.baseChange (O' := R) hπ, t.toBase_y (O' := R) hπ⟩

theorem map_eq_verschiebung (t₁ : (frobTwist hR G).TorsionTower A₁)
    (ht : ∀ n, spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π)
    (F : A ⟶ A₁) (V : A₁ ⟶ A) [IsMonHom F] [IsMonHom V]
    (hF : F.left ≫ π = VB.frob A.left p (cast_left p R hR A)) (hV : F ≫ V = 𝟙 A ^ p) :
    t₁.map t V = verschiebung hR G := by
  have e : t.map t₁ F = relFrob hR G := frobTwist_hom_ext hR fun n a ↦
    (t₁.semiOf_semiOf t t (s' := SemiHom.ofHom (t.map t₁ F)) (s'' := absFrob hR G) (ψ := F.left) ht
      (fun n ↦ congrArg Over.Hom.left (t.map_y t₁ F n)) (fun n ↦ by rw [hF]; exact absFrob_y hR t n) n a).symm.trans
      ((absFrob_app hR G n a).trans (relFrob_app_frobProj hR n a).symm)
  have : IsMonHom (𝟙 A ^ p) := hV ▸ inferInstance
  refine eq_verschiebung_of_relFrob_comp hR ?_
  rw [← e, ← t.map_comp, t.map_congr t hV, t.map_pow_id]

end Frob

section Pairing

open GlobalTheory.CatCoh GlobalTheory.AbLaw

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

end Pairing

end GlobalTheory.FrobAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleNefSmall

theorem mem_nonzeroLocus_secPow_one {X : Scheme.{0}} {L : LB X} (s : L.Sec) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) : x ∈ Out.nonzeroLocus (Cartier.secPow s 1) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  show x ∈ X.basicOpen (resG X (Cartier.lbPow_U L 1 (fun _ => i)).le (s.f i) ^ 1)
  rw [pow_one]
  unfold resG
  rw [Scheme.basicOpen_res]
  exact ⟨(Cartier.lbPow_U L 1 (fun _ => i)).ge (X.basicOpen_le _ hi), hi⟩

end GlobalTheory.AmpleNefSmall

namespace GlobalTheory.AmpleNefSmall


open ProjSpace in
theorem exists_ample_nef_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∃ A : HermLB p, IsAmpleLB A.B ∧ A.IsNef D ∧ ∃ s ∈ A.smallSec, s ≠ 0 := by
  intro hAr k _ X _ p D hX
  obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
  have := hj
  have := hX.finite
  have := isProper_str k N
  have : IsProper p := hjp ▸ inferInstance
  let B : LB X := (O1 k N).pull j
  have hB : B.IsLB := LB.isLB_pull (O1_isLB k N) j
  let c : Fin (N + 1) → B.Sec := fun a => Cartier.secPull (coord k N a) j
  have hc : ⨆ a, Out.nonzeroLocus (c a) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord k N).ge (Opens.mem_top (j x)))
    refine Opens.mem_iSup.2 ⟨a, ?_⟩
    show x ∈ Out.nonzeroLocus (Cartier.secPull (coord k N a) j)
    rw [Cartier.nonzeroLocus_secPull]
    exact ha
  let A₀ : HermLB p := HermLB.fs p hB c hc (fun _ => 1) (fun _ => by simp)
    fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hA : IsAmpleLB A₀.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  have hsmall : ∀ a, c a ∈ A₀.smallSec := by
    intro a σ y
    have e (a) : Weight.combVal p σ c 1 a = secVal _ σ (c a) := by
      simp [Weight.combVal, Matrix.one_apply]
    refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := hB) (he := fun a => e a ▸ secVal_mem _)
      (h := Weight.noCommonZero_combVal hc (M := 1) (by simp)) y)
    exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
      (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))
  have hgen : ∀ x : X, CharZero (X.residueField x) →
      ∃ i, x ∈ Out.nonzeroLocus (Cartier.secPow (c i) 1 : (A₀.pow 1).B.Sec) := fun x _ =>
    have ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top x))
    ⟨a, mem_nonzeroLocus_secPow_one _ ha⟩
  obtain ⟨t, ht, hnef⟩ := GlobalTheory.NefOfGen.nef_of_gen hAr k X p D hX A₀ 1 (N + 1)
    (fun i => Cartier.secPow (c i) 1) le_rfl hgen (HermLB.semiPos_fs hB c hc _ _ _)
    (ProjModel.nefFib_of_isAmpleLB A₀ hA)
  refine ⟨A₀.shift (fun _ => t) fun _ => rfl, hA, hnef, ?_⟩
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top (genericPoint X)))
  refine ⟨c a, fun σ y => ?_, fun h0 => ?_⟩
  · refine le_of_eq_of_le (HermLB.nsq_shift A₀ (fun _ => t) (fun _ => rfl) (secVal p σ (c a)) y) ?_
    have h1 := hsmall a σ y
    have h2 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 := Weight.nsq_nonneg (A₀.φ σ) (secVal p σ (c a)) y
    nlinarith
  · have e : c a = (0 : B.Sec) := h0
    rw [e] at ha
    simp [Out.nonzeroLocus] at ha

end GlobalTheory.AmpleNefSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_nef_hermitian_smallSection : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ A : HermLB p, IsAmpleLB A.B ∧ A.IsNef D ∧ ∃ s ∈ A.smallSec, s ≠ 0 := by
  first | exact @GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec | exact GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec | (intros; apply GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.ExpLin

open GlobalTheory.TangentOrigin

theorem existsUnique_linear_lift :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
      SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)) (α : G ⟶ G),
      IsExp y e → IsExp y e' → IsMonHom α → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = e z ≫ α := by
  intro X G _ _ g hab hsm y e e' α he he' hα
  obtain ⟨Λ, hdisc, -, hker⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice X G g hab hsm y e' he'
  letI : CommGroup (Over.mk y ⟶ G) := inferInstance
  let ex : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (e' z)) he'.1
  let G' : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (e z ≫ α)) (fun z w ↦ by
      show e (z + w) ≫ α = (e z ≫ α) * (e w ≫ α)
      rw [he.1]
      exact MonObj.mul_comp _ _ α)
  let pt : (Over.mk y).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (Over.mk y).left, q = pt := fun q ↦ Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (e' 0).left pt) (U := ⊤) (Set.mem_univ _)
  have h0 : ⊤ ≤ (e' 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker' : (ex.ker : Set (Fin g → ℂ)) = Λ := Set.ext fun z ↦ hker z
  have hholG : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z ↦ (e z).left ≫ α.left) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp he.2.2.1 α.left
  have hS0 : (0 : Additive (Over.mk y ⟶ G)) ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U} := by
    rw [← map_zero ex]
    exact h0
  have hsep : ∀ a ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      ∀ b ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      (∀ s : Γ(G.left, U), valAt' (Additive.toMul a).left U s = valAt' (Additive.toMul b).left U s) → a = b := by
    intro a ha b hb h
    exact Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦
        (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))))
  have hSe : IsOpen {z : Fin g → ℂ | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    have := (he'.2.2.1 U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hSG : IsOpen {z : Fin g → ℂ | ⊤ ≤ ((e z).left ≫ α.left) ⁻¹ᵁ U} := by
    have := (hholG U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfe : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' (e' z).left U s) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    intro s
    have := (he'.2.2.1 U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfG : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' ((e z).left ≫ α.left) U s)
      {z | ⊤ ≤ ((e z).left ≫ α.left) ⁻¹ᵁ U} := by
    intro s
    have := (hholG U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hD : ∀ w : Fin g → ℂ, (∀ s : Γ(G.left, U), fderiv ℂ (fun z ↦ valAt' (e' z).left U s) 0 w = 0) → w = 0 := by
    intro w hw
    obtain ⟨v, hv, -⟩ := he'.2.2.2.1 w
    obtain ⟨v0, hv0, -⟩ := he'.2.2.2.1 0
    have hvU : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff v.left U).2 (hv.1 ▸ h0)
    have hv0U : ⊤ ≤ v0.left ⁻¹ᵁ U := (top_le_preimage_iff v0.left U).2 (hv0.1 ▸ h0)
    have key : ∀ (u : Sp (DualNumber ℂ) ⟶ G.left) (hu : ⊤ ≤ u ⁻¹ᵁ U) (x : Sp ℂ ⟶ G.left) (hx : ⊤ ≤ x ⁻¹ᵁ U)
        (s : Γ(G.left, U)), spMap fstC ≫ u = x → (evalPt u U hu s).fst = evalPt x U hx s := by
      rintro u hu x hx s rfl
      exact (evalPt_spMap_comp fstC u U hu hx s).symm
    have heq : v.left = v0.left := by
      refine ext_evalPt (R := DualNumber ℂ) hU hvU hv0U (RingHom.ext fun s ↦ TrivSqZeroExt.ext ?_ ?_)
      · exact (key _ hvU _ h0 s hv.1).trans (key _ hv0U _ h0 s hv0.1).symm
      · have a := hv.2 U hvU s
        have b := hv0.2 U hv0U s
        rw [map_zero] at b
        exact a.trans ((hw s).trans b.symm)
    have hv0' : IsDerivAt0 (fun z ↦ (e' z).left) w v0.left := heq ▸ hv
    exact (he'.2.2.2.2 v0 hv0.1).unique hv0' hv0
  obtain ⟨F, hF, hu⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') he'.2.1
    (hker' ▸ isDiscrete_iff_discreteTopology.2 hdisc)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(G.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    hS0 hsep hSe hSG hfe hfG hD
  exact ⟨F, hF, fun M hM ↦ hu M hM⟩

end GlobalTheory.ExpLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)) (α : G ⟶ G), IsExp y e → IsExp y e' → IsMonHom α → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = e z ≫ α := by
  first | exact @GlobalTheory.ExpLin.existsUnique_linear_lift | exact GlobalTheory.ExpLin.existsUnique_linear_lift | (intros; apply GlobalTheory.ExpLin.existsUnique_linear_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRham
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.ConjSeq

theorem frobDR_primPull (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    frobDR p R hR A (primPull (dp0 R) (𝟙 _) f c) = primPull (dp0 R) (𝟙 _) f (frobDR p R hR B c) := by
  have k := (frobMor p R hR B (cast_left p R hR B)).comp (homMor (dp0 R) (𝟙 _) f)
  exact (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) f) (frobMor p R hR A (cast_left p R hR A)) k (fun _ ↦ rfl)
    (GlobalTheory.VB.frob_naturality p _ f.left _) c).trans
    (GrpMor.pull_pull (frobMor p R hR B (cast_left p R hR B)) (homMor (dp0 R) (𝟙 _) f) k (fun _ ↦ rfl) rfl c).symm

end GlobalTheory.AbDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisSmoothCommGroupSchemeField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisSmoothCommGroupSchemeField
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieField

theorem exists_isLieBasis_field : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (g : ℕ),
    SmoothOfRelativeDimension g B.hom → ∃ y : Fin g → (epsR K ⟶ B), IsLieBasis y :=
  fun _ _ B _ _ _ hdim => GlobalTheory.KeyPow.exists_isLieBasis B hdim

end GlobalTheory.LieField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisSmoothCommGroupSchemeFieldStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (g : ℕ), SmoothOfRelativeDimension g B.hom → ∃ y : Fin g → (epsR K ⟶ B), IsLieBasis y := by
  first | exact @GlobalTheory.LieField.exists_isLieBasis_field | exact GlobalTheory.LieField.exists_isLieBasis_field | (intros; apply GlobalTheory.LieField.exists_isLieBasis_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G),
      g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  intro p _ R _ G H f g hgf a ha
  have hle : kerIdeal (f.app 1) ≤ RingHom.ker (g.app 1 : G.A 1 →ₐ[R] H.A 1) := by
    rw [kerIdeal, Ideal.map_le_iff_le_comap]
    intro c hc
    have hc' : counit (R := R) c = 0 := hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e : g.app 1 (f.app 1 c) = Hom.app (g ≫ f) 1 c := rfl
    change g.app 1 (f.app 1 c) = 0
    rw [e, hgf, prime_smul_id_app]
    have h1 := H.mulBy_pow_self 1 c
    rw [pow_one] at h1
    rw [h1, hc', map_zero]
  exact hle ha

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmulStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G), g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  first | exact @GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul | exact GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul | (intros; apply GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def SecTw {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))} {N : ℕ}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : Prop :=
  ∀ (Z : Scheme.{0}) (p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left),
    p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left →
    p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom →
    ∀ z J, Good A.L z J → sval t' p z J = sval t p' z J
end GlobalTheory.Mum
end

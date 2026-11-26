module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Formalism.AdmissibleDesigns.StatementOneBFromUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCountP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormOneTwist

variable {D : D7}

def quotC (D : D7) : (AE D)ˣ →* (AE D)ˣ :=
  MonoidHom.id _ / Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def finQuot (D : D7) : (AE D)ˣ →* (GlobalTheory.FinalJoin.AfE D)ˣ :=
  (Units.map (finPart D).toMonoidHom).comp (quotC D)

theorem finPart_mul_inv (x : (AE D)ˣ) :
    finPart D (x : AE D) * finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
  rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]

theorem finQuot_val (x : (AE D)ˣ) :
    ((finQuot D x : (GlobalTheory.FinalJoin.AfE D)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      finPart D (x : AE D) * sigR (Af D.host.F) D.sp.cm.sig (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) := by
  show finPart D ((x : AE D) * sigR (AF D.host.F) D.sp.cm.sig ((x⁻¹ : (AE D)ˣ) : AE D)) = _
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]

theorem normOne_finQuot (x : (AE D)ˣ) : GlobalTheory.FinalJoin.NormOne (finQuot D x) := by
  change _ * sigR (Af D.host.F) D.sp.cm.sig _ = 1
  rw [finQuot_val]
  exact GlobalTheory.DetOnto.norm_one _ (GlobalTheory.DetOnto.sigR_sigR D) (finPart_mul_inv x)

theorem finQuot_of_isDetRoot {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetRoot V g x) :
    finQuot D x = Matrix.GeneralLinearGroup.det (finHom V g) := by
  apply Units.ext
  have h1 := congrArg (finPart D) hx
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR] at h1
  rw [finQuot_val, h1, mul_assoc, ← RingHom.map_mul, finPart_mul_inv x, RingHom.map_one, mul_one,
    GlobalTheory.DetRootChar.finPart_det]

theorem finQuot_incA (e : D.host.Eˣ) :
    ((finQuot D (Units.map (incA D).toMonoidHom e) : (GlobalTheory.FinalJoin.AfE D)ˣ) : GlobalTheory.FinalJoin.AfE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((e : D.host.E) * D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) := by
  rw [finQuot_val]
  show finPart D (incA D (e : D.host.E)) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (incA D ((e⁻¹ : D.host.Eˣ) : D.host.E))) = _
  show ((1 : Af D.host.F) ⊗ₜ[D.host.F] (e : D.host.E)) *
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.NormOneTwist

namespace GlobalTheory.NormOneTwist

variable {D : D7}

end GlobalTheory.NormOneTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CosetSum

open GlobalTheory.AutMult

theorem mem_realLevSet_iff {D : D7} {W : HSp D} {K : Subgroup (GA D W)} (hK : K ≤ GfC W) (h : GA D W) :
    (∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k) ↔ toFin W h ∈ K.subgroupOf (GfC W) := by
  constructor
  · rintro ⟨u, hu, k, hk, rfl⟩
    have h1 : toFin W u = 1 := toFin_coe_inf (V := W) ⟨u, hu⟩
    have h2 : toFin W k = ⟨k, hK hk⟩ := toFin_coe (V := W) ⟨k, hK hk⟩
    rw [map_mul, h1, h2, one_mul, Subgroup.mem_subgroupOf]
    exact hk
  · intro h'
    exact ⟨toInf W h, (toInf W h).2, toFin W h, (Subgroup.mem_subgroupOf).1 h', (toInf_mul_toFin h).symm⟩

theorem integral_eq_sum_cosets : ∀ (D : D7) (W : HSp D) (ν : Measure (GA D W)) (K : Subgroup (GA D W)), ν.IsHaarMeasure → K ≤ GfC W → IsOpen {g : GfC W | (g : GA D W) ∈ K} → ∀ Φ : GA D W → ℂ, Integrable Φ ν → MeasurableSet {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} ∧ HasSum (fun q : GfC W ⧸ K.subgroupOf (GfC W) => ∫ h in {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k}, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) (∫ g, Φ g ∂ν) := by
  intro D W ν K hν hKf hKo Φ hΦ
  obtain ⟨i0, -, i2, -, i4, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D W
  haveI := i0; haveI := i2; haveI := i4
  set K' := K.subgroupOf (GfC W) with hK'
  set C : Set (GA D W) := {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} with hCdef
  have hK'o : IsOpen (K' : Set (GfC W)) := hKo
  have hC : C = toFin W ⁻¹' (K' : Set (GfC W)) := Set.ext fun h => mem_realLevSet_iff hKf h
  have hCo : IsOpen C := hC ▸ hK'o.preimage (continuous_toFin W)
  have hCm : MeasurableSet C := hCo.measurableSet
  refine ⟨hCm, ?_⟩

  let s : GfC W ⧸ K' → Set (GA D W) := fun q => (fun g => ((Quotient.out q : GfC W) : GA D W)⁻¹ * g) ⁻¹' C
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (toFin W g) := by
    intro q g
    show _ ∈ C ↔ _
    rw [hC, Set.mem_preimage, map_mul, map_inv, toFin_coe, SetLike.mem_coe]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hCm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  haveI : Countable (GfC W ⧸ K') := by
    have hpd : (Set.univ : Set (GfC W ⧸ K')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (K' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hK'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [K'.one_mem]⟩))
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hΦ.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  refine (funext fun q => ?_ : (fun q : GfC W ⧸ K' => ∫ h in C, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) =
    fun q => ∫ x in s q, Φ x ∂ν) ▸ hsum
  have hpre : (fun h => ((Quotient.out q : GfC W) : GA D W) * h) ⁻¹' s q = C := by
    ext h; simp [s]
  rw [← hpre]
  exact ((measurePreserving_mul_left ν _).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft _) Φ (s q))

end GlobalTheory.CosetSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_tsum_realPoints_levelCoset_translates : ∀ (D : D7) (W : HSp D) (ν : Measure (GA D W)) (K : Subgroup (GA D W)), ν.IsHaarMeasure → K ≤ GfC W → IsOpen {g : GfC W | (g : GA D W) ∈ K} → ∀ Φ : GA D W → ℂ, Integrable Φ ν → MeasurableSet {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} ∧ HasSum (fun q : GfC W ⧸ K.subgroupOf (GfC W) => ∫ h in {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k}, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) (∫ g, Φ g ∂ν) := by
  first | exact @GlobalTheory.CosetSum.integral_eq_sum_cosets | exact GlobalTheory.CosetSum.integral_eq_sum_cosets | (intros; apply GlobalTheory.CosetSum.integral_eq_sum_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthInvariantsNegTwistKmodO
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.FinInvKO

theorem isFiniteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem length_lt_top_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : Submodule O (KmodO O)) {c : O} (hc : c ≠ 0) (h : ∀ x ∈ S, c • x = 0) :
    Module.length O S < ⊤ := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (FractionRing O)).ne hc
  let x₀ : KmodO O := Submodule.Quotient.mk ((algebraMap O (FractionRing O) c)⁻¹)
  let ψ : O →ₗ[O] KmodO O := LinearMap.toSpanSingleton O _ x₀
  have hS : S ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := h _ hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : algebraMap O (FractionRing O) a = algebraMap O (FractionRing O) c * y := by
      rw [← Algebra.smul_def]; exact ha
    refine ⟨a, ?_⟩
    simp only [ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ha', mul_comm (algebraMap O (FractionRing O) c) y, mul_assoc,
      mul_inv_cancel₀ hc', mul_one]
  have hk : ∀ z : LinearMap.range ψ, c • z = 0 := by
    rintro ⟨_, a, rfl⟩
    ext1
    simp only [SetLike.val_smul, ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul,
      smul_smul, Submodule.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, mul_comm (algebraMap O (FractionRing O) c), mul_assoc, mul_inv_cancel₀ hc', mul_one]
  have hfl := isFiniteLength_of_killed hc hk
  exact lt_of_le_of_lt (Module.length_le_of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS))
    (lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 hfl))

theorem finiteLength_invariants_negTwist_KmodO : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants
      ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤ := by
  intro D i w hw e he
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := hgI.1
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  haveI : CharZero (FractionRing (D.nd.O i)) :=
    (D.nd.embK i).charZero_iff (D.nd.embK i).injective |>.1 inferInstance
  haveI : CharZero (D.nd.O i) := (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).charZero
  have hle : 1 ≤ (1 + D.nd.l i ^ D.nd.s0 i) ^ e := Nat.one_le_pow _ _ (by omega)
  have hlt : 1 < (1 + D.nd.l i ^ D.nd.s0 i) ^ e :=
    Nat.one_lt_pow he.ne' (by have := pow_pos hp.pos (D.nd.s0 i); omega)
  have hc : (((1 + D.nd.l i ^ D.nd.s0 i) ^ e - 1 : ℕ) : D.nd.O i) ≠ 0 :=
    Nat.cast_ne_zero.2 (by omega)
  refine length_lt_top_of_killed _ hc fun v hv => ?_
  have h1 := hv ⟨g, hgD⟩
  change ((((Glob.epsO D.nd i) ^ (-(e : ℤ))) g : (D.nd.O i)ˣ) : D.nd.O i) • v = v at h1
  have hu : ((Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) = 1 + (D.nd.l i : D.nd.O i) ^ D.nd.s0 i := by
    simp [Glob.epsO, hg]
  have h2 : (((Glob.epsO D.nd i g) ^ e : (D.nd.O i)ˣ) : D.nd.O i) • v = v := by
    conv_lhs => rw [← h1]
    rw [smul_smul, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  rw [Nat.cast_sub hle, Nat.cast_one, sub_smul, one_smul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h2, sub_self]

end GlobalTheory.FinInvKO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPoint
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SelmerBoundAtPoint

theorem finCore : Formalism.MainNotions.N.K.H0.FinCore :=
  ⟨fun {D} i r ρ π g2 w hw => GlobalTheory.FiniteTwistInvariants.main D i r ρ π g2 w hw,
   fun {D} i w hw e he => GlobalTheory.FinInvKO.finiteLength_invariants_negTwist_KmodO D i w hw e he⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hA hT hE D i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin tie a51 unr hR hL hTB
  have : Fact ReciprocityTheory.ChartRestriction.T2.Core := ⟨GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler hA hT hE⟩
  have : Fact Formalism.MainNotions.N.K.H0.FinCore := ⟨finCore⟩
  exact Formalism.MainNotions.N.K.Closed.theorem_n5_from_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin
    tie a51 (Formalism.MainNotions.N.K.StD.unramified_input_of_admitted i dc unr) hR hL hTB

end GlobalTheory.SelmerBoundAtPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPointStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  first | exact @GlobalTheory.SelmerBoundAtPoint.main | exact GlobalTheory.SelmerBoundAtPoint.main | (intros; apply GlobalTheory.SelmerBoundAtPoint.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadingOver

open GlobalTheory.GoodPts

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

theorem norm_le_one_of_valuation_le_one {x : F} (hx : (placeAt φ).valuation F x ≤ 1) : ‖φ x‖ ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact norm_int_le_one φ n

variable (T : CDVR)

theorem valV_le_one_of_inV {x : T.Fr} (hx : InV T x) : valV T.V x ≤ 1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem inV_of_valV_le_one {x : T.Fr} (hx : valV T.V x ≤ 1) : InV T x := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
    (IsDiscreteValuationRing.maximalIdeal T.V) x hx
  have hu : IsUnit (d : T.V) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  refine ⟨n * ↑hu.unit⁻¹, ?_⟩
  rw [map_mul, ← hnd, mul_assoc, ← map_mul, hu.mul_val_inv, map_one, mul_one]

theorem vV_zpow {x : T.Fr} (n : ℤ) : vV T.V (x ^ n) = n * vV T.V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

variable {T}

theorem overLa_placeAt_of_isReading {io : F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (hR : IsReading φ T io k) :
    ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  set P := placeAt φ with hP
  have key : ∀ y : T.Fr, valV T.V y ≤ 1 ↔ ‖k y‖ ≤ 1 := fun y =>
    ⟨fun h => (hR.int y).2 (inV_of_valV_le_one T h), fun h => valV_le_one_of_inV T ((hR.int y).1 h)⟩
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖φ (π : F)‖ < 1 := (mem_placeAt φ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    have h' : π = 0 := by exact_mod_cast h
    rw [h', map_zero] at hπ
    exact WithZero.exp_ne_zero.symm hπ
  have hνπ : P.valuation F (π : F) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  set x := io (π : F) with hx
  have hx0 : x ≠ 0 := (map_ne_zero io).2 hπ0
  have hkx : ‖k x‖ < 1 := by rw [hx, hR.comp]; exact hπn
  have hvx1 : valV T.V x < 1 := by
    refine lt_of_le_of_ne ((key x).2 hkx.le) fun h1 => ?_
    have h2 : valV T.V x⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
    have h3 := (key _).1 h2
    rw [map_inv₀, norm_inv] at h3
    have h4 : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 hx0)
    exact absurd h3 (not_le.2 ((one_lt_inv₀ h4).2 hkx))
  have hvx : 0 < vV T.V x := by
    have h := (WithZero.log_lt_log (valV_ne_zero hx0) one_ne_zero).2 hvx1
    rw [WithZero.log_one] at h
    simp only [vV]; omega
  refine ⟨(vV T.V x).toNat, by omega, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  set n := vLa P a with hn
  set b := a * (π : F) ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hπ0)
  have hνa : P.valuation F a = WithZero.exp (-n) := by
    rw [hn, vLa, neg_neg, WithZero.exp_log ((P.valuation F).ne_zero_iff.2 ha)]
  have hνb : P.valuation F b = 1 := by
    rw [hb, map_mul, map_zpow₀, hνa, hνπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hkb : ‖k (io b)‖ ≤ 1 := by rw [hR.comp]; exact norm_le_one_of_valuation_le_one φ hνb.le
  have hkb' : ‖k (io b)⁻¹‖ ≤ 1 := by
    rw [← map_inv₀, hR.comp]
    exact norm_le_one_of_valuation_le_one φ (by rw [map_inv₀, hνb, inv_one])
  have hvb1 : valV T.V (io b) = 1 := by
    have h1 := (key _).2 hkb
    have h2 := (key _).2 hkb'
    rw [map_inv₀] at h2
    have hv0 : valV T.V (io b) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hb0)
    have h3 : valV T.V (io b) * (valV T.V (io b))⁻¹ ≤ valV T.V (io b) * 1 := mul_le_mul_right h2 _
    rw [mul_inv_cancel₀ hv0, mul_one] at h3
    exact le_antisymm h1 h3
  have hvb : vV T.V (io b) = 0 := by simp [vV, hvb1]
  have hab : io a = io b * x ^ n := by
    rw [hx, ← map_zpow₀, ← map_mul, hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hab, vV_mul ((map_ne_zero io).2 hb0) (zpow_ne_zero _ hx0), hvb, vV_zpow, Int.toNat_of_nonneg hvx.le]
  ring

theorem overLa_placeAt : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e :=
  fun _ _ _ _ _ φ _ _ _ hR => overLa_placeAt_of_isReading φ hR

end GlobalTheory.ReadingOver

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCpStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  first | exact @GlobalTheory.ReadingOver.overLa_placeAt | exact GlobalTheory.ReadingOver.overLa_placeAt | (intros; apply GlobalTheory.ReadingOver.overLa_placeAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpoly
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcTame

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.LlcTame

attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
private theorem eq_one_of_isSemisimple_of_charpoly_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hs : f.IsSemisimple)
    (hc : f.charpoly = (X - 1) ^ Module.finrank ℂ V) : f = 1 := by
  have hn : IsNilpotent (f - 1) := by
    refine ⟨Module.finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa using this
  have hs' : (f - 1).IsSemisimple :=
    hs.sub_of_commute (Commute.one_right f) Module.End.isSemisimple_id
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hs')

attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
theorem _root_.GlobalTheory.LlcTame.isTameWD_iff_charPol : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (y : _root_.GlobalTheory.WeilDeligne.WD h), _root_.GlobalTheory.LocLanglands.IsTameWD y ↔
    ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) →
      y.charPol σ = (X - 1) ^ y.lpDim := by
  intro E Ω _ _ _ _ _ A w h y
  unfold _root_.GlobalTheory.LocLanglands.IsTameWD
  constructor
  · rintro ⟨n, a, rfl, ha⟩ σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    refine (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).trans ?_
    rw [hd, ha σ hσ, LinearMap.charpoly_one]
  · intro H
    obtain ⟨n, a, rfl⟩ := y.exists_rep
    refine ⟨n, a, rfl, fun σ hσ => ?_⟩
    have hc := H σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    rw [hd] at hc
    have hc' := (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).symm.trans hc
    exact eq_one_of_isSemisimple_of_charpoly_eq _ (a.semisimple σ) hc'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpolyStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), IsTameWD y ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → y.charPol σ = (X - 1) ^ y.lpDim := by
  first | exact @GlobalTheory.LlcTame.isTameWD_iff_charPol | exact GlobalTheory.LlcTame.isTameWD_iff_charPol | (intros; apply GlobalTheory.LlcTame.isTameWD_iff_charPol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatible
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcDepth

theorem eq_pow_natDegree_of_dvd {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hd : p ∣ (X - 1) ^ n) :
    p = (X - 1) ^ p.natDegree := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at hd ⊢
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) n).1 hd
  have hpi := eq_of_monic_of_associated hp ((monic_X_sub_C (1 : ℂ)).pow i) hi
  rw [hpi, natDegree_pow, natDegree_X_sub_C, mul_one]

theorem prod_map_pow {α : Type*} (q : ℂ[X]) (f : α → ℕ) (s : Multiset α) :
    (s.map fun y => q ^ f y).prod = q ^ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, pow_add]

theorem fixed_ne_bot_iff_isTameWD : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc →
      ∀ x : IrrGL (k := w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  intro hDZC hDZI hEx hZel hGeo hBZ E Ω _ _ _ _ _ A w h rc hrc x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨a, ha, ε, -, hL⟩ := id hrc
  obtain ⟨m, hm⟩ := hEx _ x
  have hs : HasSupport x.rep (msupp m) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZel _ m x hm
  have hcp := GlobalTheory.T.central_character_rec_compatible hEx hZel hGeo hBZ E Ω A w h a ha _ rc hL x (msupp m) hs
  have hdy : ∀ y ∈ msupp m, (fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ ↔ IsTameWD (rc y)) :=
    fun y hy => hDZC E Ω A w h rc hrc y (hs.isCusp hy)
  have htame : IsTameWD (rc x) ↔ ∀ y ∈ msupp m, IsTameWD (rc y) := by
    simp only [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly E Ω A w h]
    constructor
    · intro H y hy σ hσ
      have hdvd : (rc y).charPol σ ∣ (rc x).charPol σ := by
        rw [hcp σ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
      rw [H σ hσ] at hdvd
      have e := eq_pow_natDegree_of_dvd ((rc y).charPol_monic σ) hdvd
      rwa [WD.charPol_natDegree] at e
    · intro H σ hσ
      rw [hcp σ, Multiset.map_congr rfl (fun y hy => H y hy σ hσ), prod_map_pow]
      congr 1
      rw [hL.dim x, Multiset.map_congr rfl (fun y _ => hL.dim y), hs.sum_fst, Fintype.card_fin]
  rw [htame]
  constructor
  · intro hx y hy
    rw [← hdy y hy]
    obtain ⟨n, xs, hxs, hcs⟩ := hs
    have H := GlobalTheory.SmGL.depthZeroSupport _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hx)
    rw [← hxs] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨v, hv, hv0⟩ := H i
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  · intro H
    exact hDZI _ x (msupp m) hs fun y hy => (hdy y hy).2 (H y hy)

end GlobalTheory.LlcDepth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_rec_compatible : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → ∀ x : IrrGL (k := w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  first | exact @GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD | exact GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD | (intros; apply GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.WildAdditive

theorem not_isUnit_natCast (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Nontrivial O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : ¬ IsUnit (l : O) := by
  rintro ⟨u, hu⟩
  have htop : (⊤ : Submodule ℤ_[l] O) ≤ IsLocalRing.maximalIdeal ℤ_[l] • ⊤ := by
    intro x _
    have hx : x = (l : ℤ_[l]) • (((u⁻¹ : Oˣ) : O) * x) := by
      rw [Algebra.smul_def, map_natCast, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hx]
    have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    exact Submodule.smul_mem_smul hl Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) ⊤
    (Module.finite_def.mp inferInstance) htop (IsLocalRing.maximalIdeal_le_jacobson _)
  exact top_ne_bot hbot

theorem exists_pow_nsmul_eq_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (x : KOG O 1) :
    ∃ n : ℕ, l ^ n • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (y 0)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O

  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_natCast l O)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hl

  obtain ⟨k, hk⟩ :=
    IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  obtain ⟨c, hc⟩ := hk.dvd.trans (pow_dvd_pow_of_dvd hl k)
  refine ⟨k, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  unfold stdG
  rw [LinearMap.mem_range]
  refine ⟨fun _ => c * a, ?_⟩
  funext j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  have hb' : algebraMap O (FractionRing O) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hlk : ((l ^ k : ℕ) : FractionRing O) =
      algebraMap O (FractionRing O) b * algebraMap O (FractionRing O) c := by
    rw [← map_mul, ← hc, map_pow, map_natCast, Nat.cast_pow]
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, Pi.smul_apply,
    nsmul_eq_mul, ← hab]
  rw [hlk, map_mul]
  field_simp

theorem eq_zero_of_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (M : Type) [AddCommGroup M] (f : G E Ω → M) (hf : IsLocallyConstant f)
    (I : Subgroup (G E Ω)) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b)
    (hM : ∀ x : M, ∃ n : ℕ, l ^ n • x = 0) (σ : G E Ω) (hI : σ ∈ I)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : f σ = 0 := by
  classical
  have hI1 : (1 : G E Ω) ∈ I := I.one_mem
  have hf1 : f 1 = 0 := by
    have h := hadd 1 hI1 1 hI1
    rw [one_mul] at h
    simpa using h
  have hpow : ∀ n : ℕ, f (σ ^ n) = n • f σ := by
    intro n
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hadd _ (I.pow_mem hI n) _ hI, ih, succ_nsmul]
  have hU : f ⁻¹' {f 1} ∈ nhds (1 : G E Ω) := (hf.isOpen_fiber (f 1)).mem_nhds rfl
  obtain ⟨L, hLfin, hLsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hU
  have hUo : IsOpen (L.fixingSubgroup : Set (G E Ω)) := L.fixingSubgroup_isOpen
  have : Finite (G E Ω ⧸ L.fixingSubgroup) := L.fixingSubgroup.quotient_finite_of_isOpen hUo
  have : L.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hd : L.fixingSubgroup.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hσU : σ ^ L.fixingSubgroup.normalCore.index ∈ L.fixingSubgroup :=
    L.fixingSubgroup.normalCore_le (L.fixingSubgroup.normalCore.pow_index_mem σ)
  obtain ⟨a, d, hdl, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd l hl.ne_one

  have hl1 : A.valuation (l : Ω) = 1 := by
    have h1 := (hA (l : 𝓞 E)).not.mpr hlv
    have h2 := A.valuation_le_one (l : A)
    simp only [map_natCast] at h1 h2
    exact le_antisymm h2 (not_lt.mp h1)
  have hk : ¬ A.valuation ((l ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hl1, one_pow]
    exact lt_irrefl _
  have hτ : ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ d) y / y - 1) < 1 :=
    GlobalTheory.WildInertiaChar.wild_pow A σ hσ d
  have hτU : σ ^ d ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ d) hτ (l ^ a) hk x
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσU
    rw [← pow_mul, mul_comm, ← hdec]
    exact hσU x hx
  have hd0 : d • f σ = 0 := by
    rw [← hpow d]
    have := hLsub hτU
    simpa [hf1] using this
  obtain ⟨n, hn⟩ := hM (f σ)
  have hcop : IsCoprime ((l ^ n : ℕ) : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hl).mpr hdl))
  obtain ⟨u, w, huw⟩ := hcop
  calc f σ = (1 : ℤ) • f σ := (one_zsmul _).symm
    _ = (u * ((l ^ n : ℕ) : ℤ) + w * (d : ℤ)) • f σ := by rw [huw]
    _ = u • ((l ^ n) • f σ) + w • (d • f σ) := by
        rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = 0 := by rw [hn, hd0, smul_zero, smul_zero, add_zero]

private theorem valuation_apply_eq_of_valuation_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  by_cases hy : y = 0
  · simp [hy]
  · have h1 : A.valuation (σ y / y) = 1 := by
      have := Valuation.map_one_add_of_lt A.valuation (hσ y hy)
      simpa using this
    rw [← div_mul_cancel₀ (σ y) hy, map_mul, h1, one_mul]

private theorem mem_ine_of_valuation_div_sub_one_lt_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  rw [mem_Ine]
  let : MulAction (G E Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
  refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← ValuationSubring.valuation_le_one_iff,
      ← ValuationSubring.valuation_le_one_iff]
    have key : A.valuation x = A.valuation (σ⁻¹ • x) := by
      have h := valuation_apply_eq_of_valuation_div_sub_one_lt A σ hσ (σ⁻¹ • x)
      rwa [← AlgEquiv.smul_def, smul_inv_smul] at h
    rw [key]
  · intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · have h3 : σ x - x = x * (σ x / x - 1) := by
        rw [mul_sub, mul_div_cancel₀ _ h0, mul_one]
      rw [h3, map_mul]
      calc _ ≤ 1 * A.valuation (σ x / x - 1) := by gcongr
        _ < 1 := by rw [one_mul]; exact hσ x h0

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ f : GE D.nd → KOG (D.nd.O i) 1, IsLocallyConstant f → (∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f (a * b) = f a + f b) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), f σ = 0 := by
  intro D i v hv f hf hadd σ hσ
  exact eq_zero_of_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i) (D.nd.lPrime i).out hv
    (D.nd.plOm.2 v) (KOG (D.nd.O i) 1) f hf (Ine (F := D.host.E) (D.nd.plOm.1 v)) hadd
    (exists_pow_nsmul_eq_zero (D.nd.l i) (D.nd.O i)) σ (mem_ine_of_valuation_div_sub_one_lt_one _ σ hσ) hσ

end GlobalTheory.WildAdditive
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstantStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ f : GE D.nd → KOG (D.nd.O i) 1, IsLocallyConstant f → (∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f (a * b) = f a + f b) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), f σ = 0 := by
  first | exact @GlobalTheory.WildAdditive.main | exact GlobalTheory.WildAdditive.main | (intros; apply GlobalTheory.WildAdditive.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniUpMul
namespace GlobalTheory.UnipotentUpperMul

theorem isUniUp_mul : ∀ {R : Type} [inst : CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R},
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp M → Formalism.MainNotions.ArithmeticCylinders.IsUniUp M' → Formalism.MainNotions.ArithmeticCylinders.IsUniUp (M * M') := by
  intro R _ N M M' hM hM' a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hka | hak
    · rw [(hM a k).1 hka, zero_mul]
    · rw [(hM' k b).1 (lt_of_lt_of_le hba hak), mul_zero]
  · intro hab
    subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hM' a a).2 rfl, mul_one]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [(hM a k).1 h, zero_mul]
      · rw [(hM' k a).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UnipotentUpperMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KurValue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie Polynomial

theorem exists_norm_eq_of_mem_closure {K : Type*} [NormedField K] [IsUltrametricDist K] {S : Set K} {x : K}
    (hx : x ∈ closure S) (h0 : x ≠ 0) : ∃ y ∈ S, ‖x‖ = ‖y‖ := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx ‖x‖ (norm_pos_iff.2 h0)
  refine ⟨y, hy, ?_⟩
  rw [dist_comm, dist_eq_norm] at hd
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hd.ne
  rw [sub_add_cancel, max_eq_right hd.le] at this
  exact this.symm

variable {p : ℕ} [Fact p.Prime]

theorem mem_range_of_isIntegral {x : ℂ_[p]} (hx : IsIntegral (PadicAlgCl p) x) :
    x ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range :=
  minpoly.mem_range_of_degree_eq_one _ x (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hx))

theorem exists_lift {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ ψ : F →+* PadicAlgCl p, ∀ a, algebraMap (PadicAlgCl p) ℂ_[p] (ψ a) = φ a := by
  have h : ∀ a : F, φ a ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range := fun a => by
    have h1 : IsIntegral ℚ (φ a) := (Algebra.IsIntegral.isIntegral (R := ℚ) a).map φ.toRatAlgHom
    exact mem_range_of_isIntegral h1.tower_top
  choose f hf using h
  have hi := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, hf⟩
  · rw [hf, map_one, map_one]
  · simp only [map_mul, hf]
  · simp only [map_zero, hf]
  · simp only [map_add (f := _), hf]

theorem exists_finite {F : Type} [Field F] [NumberField F] (ψ : F →+* PadicAlgCl p) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (∀ a, ψ a ∈ K) ∧
      ∀ x ∈ K, ∃ a, ‖x‖ = ‖ψ a‖ := by
  let b := Module.finBasis ℚ F
  refine ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)), ?_, fun a => ?_, fun x hx => ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← b.sum_repr a, map_sum]
      refine sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · let M : IntermediateField ℚ_[p] (PadicAlgCl p) :=
      ψ.fieldRange.topologicalClosure.toIntermediateField fun r => by
        have hc : IsClosed {r : ℚ_[p] | algebraMap ℚ_[p] (PadicAlgCl p) r ∈ ψ.fieldRange.topologicalClosure} :=
          (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
        refine (Padic.denseRange_ratCast p).induction_on r hc fun q => ?_
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem _ _
    have hM : IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)) ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      exact Subfield.le_topologicalClosure ψ.fieldRange ⟨b i, rfl⟩
    by_cases h0 : x = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (ψ.fieldRange : Set (PadicAlgCl p))) (hM hx) h0
    exact ⟨a, h⟩

theorem exists_norm_eq {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : x ∈ kurC φ) :
    ∃ a : F, ‖x‖ = ‖φ a‖ := by
  obtain ⟨ψ, hψ⟩ := exists_lift φ
  obtain ⟨K, hK, hmem, hnorm⟩ := exists_finite ψ
  let M : Subfield ℂ_[p] := (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension p K).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])
  have hle : kurC φ ≤ M.topologicalClosure := by
    refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
    · rintro _ ⟨a, rfl⟩
      exact M.le_topologicalClosure ⟨ψ a, ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (hmem a), hψ a⟩
    · refine Subfield.topologicalClosure_minimal _ (Subfield.closure_le.2 ?_) (Subfield.isClosed_topologicalClosure _)
      rintro ζ ⟨n, hn, hpn, hζ⟩
      obtain ⟨ξ, rfl⟩ := mem_range_of_isIntegral (IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one))
      refine M.le_topologicalClosure ⟨ξ, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow hK hpn ?_, rfl⟩
      apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
      rw [map_pow, hζ, map_one]
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (M : Set ℂ_[p])) (hle hx) h0
  obtain ⟨n, hn, hyn⟩ := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_iff hK y).1 hy
  obtain ⟨z, hz, hyz⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn p K hK hn hyn
  obtain ⟨a, ha⟩ := hnorm z hz
  refine ⟨a, ?_⟩
  rw [h, ← hψ, norm_algebraMap', norm_algebraMap', ← ha, hyz]

theorem exists_near {F : Type} [Field F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ y ∈ kurC φ, ‖x - y‖ < 1 := by
  rcases hx.lt_or_eq with hlt | heq
  · exact ⟨0, zero_mem _, by rwa [sub_zero]⟩
  obtain ⟨z, hz⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x one_pos
  rw [dist_eq_norm, PadicComplex.coe_eq] at hz
  have hz1 : ‖z‖ = 1 := by
    have h1 : ‖algebraMap (PadicAlgCl p) ℂ_[p] z - x‖ < ‖x‖ := by rwa [norm_sub_rev, heq]
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rwa [sub_add_cancel, max_eq_right h1.le, heq, norm_algebraMap'] at this
  obtain ⟨ζ, m, hm, hζ, h⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar z hz1
  refine ⟨algebraMap (PadicAlgCl p) ℂ_[p] ζ, root_mem_kurC φ hm (by rw [← map_pow, hζ, map_one]), ?_⟩
  have e : x - algebraMap (PadicAlgCl p) ℂ_[p] ζ =
      (x - algebraMap (PadicAlgCl p) ℂ_[p] z) + algebraMap (PadicAlgCl p) ℂ_[p] (z - ζ) := by
    rw [map_sub]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz (by rwa [norm_algebraMap']))

theorem kurC_value_residue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    (∀ x ∈ kurC φ, ∃ a : F, ‖x‖ = ‖φ a‖) ∧ ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ∃ y ∈ kurC φ, ‖x - y‖ < 1 :=
  fun _ _ _ _ _ φ => ⟨fun _ hx => exists_norm_eq φ hx, fun _ hx => exists_near φ hx⟩

end GlobalTheory.KurValue

end
end

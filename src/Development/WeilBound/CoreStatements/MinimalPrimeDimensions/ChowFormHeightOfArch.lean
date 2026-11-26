module

public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsClosedOfCoheight
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFUnitNeZero
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FormHeightGen
public import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasis
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DimClosureAddOneLe
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdOfForallEmultiplicityLe
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartResidueDegreeAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeChartArea

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartResidueDegreeAlgClosedClosed
open GroundTheory.Heights₂.Heights

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ObjectsChow_ChowDegreeClosedPoint : GroundTheory.Heights₂.Heights.ObjectsChow.ChowDegreeClosedPoint.Statement :=
  @GroundTheory.Heights₂.Heights.ObjectsChow.ChowDegreeClosedPoint.proof GroundTheory.Heights₂.Heights.ObjectsChow.ClosedPointChartField.proof GroundTheory.Heights₂.Heights.ObjectsChow.ClosedPointConeCoord.proof

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.NormOfDividedFormSep : GroundTheory.Heights₂.Heights.NormOfDividedFormSep.Statement :=
  @GroundTheory.Heights₂.Heights.NormOfDividedFormSep.proof GroundTheory.Heights₂.Heights.NormFormEval.full GroundTheory.Heights₂.Heights.NormFormDvd.full GroundTheory.Heights₂.Heights.PrimeMapFractionRing.full

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFreeParAlgIndep : GroundTheory.Heights₂.Heights.ChartFreeParAlgIndep.Statement :=
  @GroundTheory.Heights₂.Heights.ChartFreeParAlgIndep.proof GroundTheory.Heights₂.Heights.ChartParAlgebraic.proof

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartPointSeparable : GroundTheory.Heights₂.Heights.ChartPointSeparable.Statement :=
  @GroundTheory.Heights₂.Heights.ChartPointSeparable.proof GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFreeParAlgIndep

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFracSeparable : GroundTheory.Heights₂.Heights.ChartFracSeparable.Statement :=
  @GroundTheory.Heights₂.Heights.ChartFracSeparable.proof GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartPointSeparable

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartNormAlgClosed : GroundTheory.Heights₂.Heights.ChartNormAlgClosed.Statement :=
  @GroundTheory.Heights₂.Heights.ChartNormAlgClosed.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartFracSeparableInhabited.chartLocDomain GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.full GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.full GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.NormOfDividedFormSep GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartFracSeparable

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.LocalSectionLengthSum : GroundTheory.Heights₂.Heights.LocalSectionLengthSum.Statement :=
  @GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof

theorem GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.SectionLengthSum : GroundTheory.Heights₂.Heights.SectionLengthSum.Statement :=
  @GroundTheory.Heights₂.Heights.SectionLengthSum.proof GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.LocalSectionLengthSum

namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing

theorem chartResidueDegreeAlgClosed_closed : ChartResidueDegreeAlgClosed.Statement :=
  ChartResidueDegreeAlgClosed.proof ChowFormBirationalAlgClosed.proof ChartFinite.full ChartKernel.full
    SectionPerfect.coneDimOfChowForm_full ConeDimComponent.proof_closed
    SectionPerfect.chowFormExists_full IncidenceGeneric.full ChartLocalOrder.full

theorem chartLengthAlgClosed_closed : ChartLengthAlgClosed.Statement :=
  ChartLengthAlgClosed.proof SpecFirstMemIncIdeal.full ChartFinite.full LengthFiniteAlgebra.full
    ChartMaxIdeals.full ChartLocalOrder.full chartResidueDegreeAlgClosed_closed

theorem chartChoiceAlgClosed_closed : ChartChoiceAlgClosed.Statement :=
  ChartChoiceAlgClosed.proof SectionPerfect.incIdealPrime_full chowFormMultiHomog

theorem sectionCycleReduced_closed : SectionCycleReduced.Statement :=
  sectionCycleReduced_of SectionComponents.proof_closed GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.SectionLengthSum

end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing

namespace GlobalTheory.CompanionTheory.Ar.Short

end GlobalTheory.CompanionTheory.Ar.Short
end

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.StCharts
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.Cartier

namespace ChowFormHeightComparison₂.CF.H

variable {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {m : ℕ} {p : Z ⟶ Sp R} {s : Fin m → B.Sec}

theorem eval₂_coords_eq_zero (hB : B.IsLB) {σ : R →+* ℂ} (y : CxPts p σ) {q : MvPolynomial (Fin m) R}
    (hq : q ∈ ptIdeal p s (under y)) : eval₂ σ (coords p σ hB s y) q = 0 := by
  have hy0 : y ∈ ptsIn p σ (B.U (pick hB y)) := mem_pick hB y
  have hz : under y ∈ B.U (pick hB y) := mem_ptsIn.mp hy0
  let ψ := Z.descResidueField (Scheme.stalkClosedPointTo (y : Sp ℂ ⟶ Z))
  have hev : ∀ f : Γ(Z, B.U (pick hB y)),
      ψ.hom ((Z.evaluation (B.U (pick hB y)) (under y) hz).hom f) = ev p σ (B.U (pick hB y)) f y := by
    intro f
    have hv := congrArg (fun g => g.hom f)
      (Points.germ_stalkClosedPointTo_eq_valMap (C := ℂ) (y : Sp ℂ ⟶ Z) (B.U (pick hB y)) hy0)
    rw [ev_eq hy0, evHom]
    refine Eq.trans ?_ hv
    rfl
  have hmem : q ∈ RingHom.ker (coneHom p s (under y) (pick hB y) hz) := by
    have h := hq
    simp only [ptIdeal, Submodule.mem_iInf] at h
    exact h _ hz
  have hΦ : eval₂Hom σ (coords p σ hB s y) = (Polynomial.evalRingHom 1).comp
      ((Polynomial.mapRingHom ψ.hom).comp (coneHom p s (under y) (pick hB y) hz)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [coneHom, RingHom.comp_apply, eval₂Hom_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
      erw [hev, ev_algX hy0]
    · intro k
      simp only [coneHom, RingHom.comp_apply, eval₂Hom_X', Polynomial.coe_mapRingHom, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, one_mul]
      erw [hev]
      rfl
  have he : eval₂ σ (coords p σ hB s y) q = eval₂Hom σ (coords p σ hB s y) q := rfl
  rw [he, hΦ, RingHom.comp_apply, RingHom.comp_apply, RingHom.mem_ker.mp hmem, map_zero, map_zero]

theorem exists_form (h1 : StPts) [IsIntegral Z] [NoetherianSpace Z] (hE : Emb p s) (U : Z.Opens)
    (hU : genericPoint Z ∈ U) : ∃ (n : ℕ) (q : MvPolynomial (Fin m) R), q.IsHomogeneous n ∧
      q ∉ ptIdeal p s (genericPoint Z) ∧ ∀ z, z ∉ U → q ∈ ptIdeal p s z := by
  obtain ⟨hprime, hspec, -, -⟩ := h1 R Z p B m s hE
  let C : Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
  obtain ⟨S, hirr, hSC⟩ := NoetherianSpace.exists_finset_irreducible C
  have hg0 : ∀ k : S, ∃ g : Z, IsGenericPoint g (k : Set Z) := fun k => QuasiSober.sober (hirr k) k.1.isClosed
  choose g hg using hg0
  have hr0 : ∀ k : S, ∃ (d : ℕ) (r : MvPolynomial (Fin m) R), r.IsHomogeneous d ∧ r ∈ ptIdeal p s (g k) ∧
      r ∉ ptIdeal p s (genericPoint Z) := by
    intro k
    have hk : (k : Set Z) ⊆ (U : Set Z)ᶜ := by
      intro z hz
      have h' : z ∈ (C : Set Z) := by
        rw [hSC]
        exact (Finset.le_sup (f := id) k.2) hz
      exact h'
    have hnot : ¬ ptIdeal p s (g k) ≤ ptIdeal p s (genericPoint Z) := by
      intro hle
      have hm : genericPoint Z ∈ closure ({g k} : Set Z) := specializes_iff_mem_closure.mp ((hspec _ _).mpr hle)
      have hcl : closure ({g k} : Set Z) = (k : Set Z) := hg k
      rw [hcl] at hm
      exact hk hm hU
    obtain ⟨f, hf, hfn⟩ := Set.not_subset.mp hnot
    have hex : ∃ d, homogeneousComponent d f ∉ ptIdeal p s (genericPoint Z) := by
      by_contra hcon
      push_neg at hcon
      apply hfn
      rw [← MvPolynomial.sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => hcon d
    obtain ⟨d, hd⟩ := hex
    exact ⟨d, _, homogeneousComponent_isHomogeneous d f, (hprime (g k)).isHomog f hf d, hd⟩
  choose d r hr using hr0
  refine ⟨∑ k, d k, ∏ k, r k, IsHomogeneous.prod _ _ _ fun k _ => (hr k).1, ?_, ?_⟩
  · intro hmem
    obtain ⟨k, -, hk⟩ := ((hprime _).isPrime.prod_mem_iff).mp hmem
    exact (hr k).2.2 hk
  · intro z hz
    have hzC : z ∈ (C : Set Z) := hz
    rw [hSC, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hzC
    simp only [Set.mem_iUnion] at hzC
    obtain ⟨k, hkS, hzk⟩ := hzC
    have hle := (hspec (g ⟨k, hkS⟩) z).mp ((hg ⟨k, hkS⟩).specializes hzk)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) (hle (hr ⟨k, hkS⟩).2.1)

end ChowFormHeightComparison₂.CF.H


open ChowFormHeightComparison₂.CF.H in
theorem ChowFormHeightComparison₂.CF.stCharts (h1 : ChowFormHeightComparison₂.CF.StPts) : ChowFormHeightComparison₂.CF.StCharts := by
  intro K _ _ Z _ p B m s e hE hX
  have := hX.isNoetherian
  obtain ⟨U, x, hU, hg, hx⟩ := GlobalTheory.GenericEtale.exists_etale_coords hX
  obtain ⟨n, q, h₁, h₂, h₃⟩ := exists_form h1 hE U hg
  refine ⟨n, q, h₁, h₂, fun σ y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ U := mem_ptsIn.2 (by_contra fun h => hy (eval₂_coords_eq_zero hE.isLB y (h₃ _ h)))
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy'
  exact ⟨c, hc⟩
end
end

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowDegreeSection
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Short.ChowClosing in
theorem chowDegreeSection : ObjectsChow.ChowDegreeSection.Statement :=
  ObjectsChow.ChowDegreeSection.proof
    (chowFormSectionPerfect_of
      (chowFormSectionAlgClosed_of
        (SectionOrderAlgClosed.proof IncIdealBelow.full SpecFirstMemIncIdeal.full
          chartChoiceAlgClosed_closed Vertical.SpecFirstNeField.full
          LocalizationPrimeDVR.full EmultiplicityOrd.full ChartFinite.full ChartLocDomain.full
          GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartNormAlgClosed
          chartLengthAlgClosed_closed LengthQuotientDet.full))
      sectionCycleReduced_closed MinimalPrimeComap.proof
      (FundCycleBaseChange.proof MinimalPrimeComap.proof))

theorem algX_strHom {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  ext r
  rw [algebraMap_eq_strHom]
  simp only [algX, RingHom.comp_apply, CommRingCat.hom_comp]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Base

variable {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S}
  {B : LB Z} {m : ℕ} {s : Fin m → B.Sec}

theorem algX_eq_comp (h : algX p ⊤ = (algX q ⊤).comp π) (U : Z.Opens) : algX p U = (algX q U).comp π := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), h, ← RingHom.comp_assoc, TopForm.resG_comp_algX]

private theorem eq_of_algX_top_eq {R : Type} [CommRing R] {Z : Scheme.{0}} {f g : Z ⟶ Sp R}
    (h : algX f ⊤ = algX g ⊤) : f = g := by
  have hf : ∀ φ : Z ⟶ Sp R,
      algX φ ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ.appTop).hom := by
    intro φ
    ext r
    simp only [algX, RingHom.comp_apply, CommRingCat.hom_comp]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [hf, hf] at h
  have e : f.appTop = g.appTop := by
    simpa using CommRingCat.hom_ext h
  haveI : Mono (Sp R).toSpecΓ := by
    rw [← SpecMap_ΓSpecIso_hom]
    infer_instance
  rw [← cancel_mono (Sp R).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

theorem eq_comp_spMap (h : algX p ⊤ = (algX q ⊤).comp π) : q ≫ spMap π = p := by
  apply eq_of_algX_top_eq
  rw [h]
  ext r
  have key := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  simp only [algX, Scheme.Hom.appLE, spMap, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply,
    RingHom.coe_comp, Function.comp_apply]
  rw [key]
  rfl

theorem emb_base (h : algX p ⊤ = (algX q ⊤).comp π) (hE : Emb p s) : Emb q s := by
  obtain ⟨hLB, hcov, hch⟩ := hE
  refine ⟨hLB, hcov, fun k => ?_⟩
  obtain ⟨ha, t, hs, hr⟩ := hch k
  refine ⟨ha, t, fun x => ?_, hr⟩
  obtain ⟨P, rfl⟩ := hs x
  refine ⟨MvPolynomial.map π P, ?_⟩
  rw [algX_eq_comp h]
  simp [MvPolynomial.eval₂_map]

theorem ptIdeal_base (h : algX p ⊤ = (algX q ⊤).comp π) (z : Z) :
    ptIdeal p s z = (ptIdeal q s z).comap (MvPolynomial.map π) := by
  simp only [ptIdeal, Ideal.comap_iInf, RingHom.comap_ker]
  refine iInf_congr fun i => iInf_congr fun hi => congrArg _ ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_
  · simp [coneHom, algX_eq_comp h]
  · simp [coneHom]

end Base

end ChowFormHeightComparison₂.CF.V

namespace ChowFormHeightComparison₂.CF

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem C_mem_ptIdeal_genericPoint_iff {R : Type} [CommRing R] {Z : Scheme.{0}} [IsIntegral Z] {B : LB Z} {m : ℕ}
    (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (hB : B.IsLB) (r : R) :
    MvPolynomial.C r ∈ ptIdeal p s (genericPoint Z) ↔ algX p ⊤ r = 0 := by
  have hη : genericPoint Z ∈ ⨆ i, B.U i := by
    rw [hB.cover]
    trivial
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.mp hη
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker, coneHom, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Polynomial.C_eq_zero]
  constructor
  · intro h
    have := h i₀ hi₀
    rw [V.evaluation_algX] at this
    exact (evaluation_genericPoint_eq_zero_iff _ _).mp this
  · intro h i hi
    rw [V.evaluation_algX, h]
    simp

private theorem isProjOver_of_surjective_base {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}}
    {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S} (hπ : Function.Surjective π)
    (hq : q ≫ spMap π = p) (hP : IsProjOver p) : IsProjOver q := by
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  let ι : Z ⟶ Limits.pullback p (spMap π) := Limits.pullback.lift (𝟙 Z) q (by simp [hq])
  have h1 : ι ≫ Limits.pullback.fst p (spMap π) = 𝟙 Z := Limits.pullback.lift_fst _ _ _
  have h2 : ι ≫ Limits.pullback.snd p (spMap π) = q := Limits.pullback.lift_snd _ _ _
  haveI : IsIso ι := ⟨⟨Limits.pullback.fst p (spMap π), h1, by
    rw [← cancel_mono (Limits.pullback.fst p (spMap π)), Category.assoc, h1]
    simp⟩⟩
  rw [← h2]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ι (ProjSpace.isProjOver_pullback_snd π hP)

open V in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem stVert (h1 : StPts) (h2 : StPull) (h3 : StDiv) : StVert := by
  intro K _ _ Z _ p B m s v d hP hE hv hd
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set κ := v.asIdeal.ResidueField
  have hB := hE.isLB
  have hker : ∀ r, algX p ⊤ r = 0 ↔ r ∈ v.asIdeal := by
    intro r
    rw [← C_mem_ptIdeal_genericPoint_iff p s hB r, ← hv, Ideal.mem_comap]
  let e : (𝓞 K ⧸ v.asIdeal) ≃+* κ :=
    RingEquiv.ofBijective _ v.asIdeal.bijective_algebraMap_quotient_residueField
  let φ : κ →+* Γ(Z, ⊤) :=
    (Ideal.Quotient.lift v.asIdeal (algX p ⊤) fun r hr => (hker r).mpr hr).comp e.symm.toRingHom
  letI inst : Algebra κ Γ(Z, ⊤) := φ.toAlgebra
  refine ⟨inst, ?_⟩
  have hπ : algX p ⊤ = (algX (strHom κ Z) ⊤).comp (algebraMap (𝓞 K) κ) := by
    rw [V.algX_strHom]
    ext r
    show algX p ⊤ r = φ (algebraMap (𝓞 K) κ r)
    have hr : e.symm (algebraMap (𝓞 K) κ r) = Ideal.Quotient.mk v.asIdeal r := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hr,
      Ideal.Quotient.lift_mk]
  have hsurj : Function.Surjective (algebraMap (𝓞 K) κ) :=
    v.asIdeal.algebraMap_residueField_surjective
  have hEκ : Emb (strHom κ Z) s := V.emb_base hπ hE
  have hPκ : IsProjOver (strHom κ (X := Z)) := isProjOver_of_surjective_base hsurj (V.eq_comp_spMap hπ) hP
  have hred : reduceMod v (ptIdeal p s (genericPoint Z)) = ptIdeal (strHom κ Z) s (genericPoint Z) := by
    rw [V.ptIdeal_base hπ]
    exact Ideal.map_comap_of_surjective _ (MvPolynomial.map_surjective _ hsurj) _
  rw [hred]
  set J := ptIdeal (strHom κ Z) s (genericPoint Z)
  have hdimle : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) ≤ m := by
    refine (ringKrullDim_quotient_le J).trans ?_
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hdimge : ((d : WithBot ℕ∞) + 1) ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) := by
    have := V.dim_add_one_le h1 hEκ
    rwa [hd] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = n := by
    revert hdimle hdimge
    generalize ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = x
    intro hdimle hdimge
    induction x using WithBot.recBotCoe with
    | bot => simp at hdimge
    | coe y =>
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) := hdimle
        rw [WithBot.coe_le_coe, top_le_iff] at h'
        exact ENat.coe_ne_top m h'
      | coe n => exact ⟨n, rfl⟩
  have hnd : d + 1 ≤ n := by
    rw [hn] at hdimge
    exact_mod_cast hdimge
  have hn' : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = ↑(n - 1 + 1) := by
    rw [hn]
    congr 1
    omega
  obtain ⟨hZ, hdeg⟩ := V.field_case h1 h2 h3 V.chowDegreeSection
    GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ObjectsChow_ChowDegreeClosedPoint (n - 1) Z B s hPκ hEκ hn'
  have hnd' : n - 1 = d := by
    rw [hd] at hZ
    exact_mod_cast hZ.symm
  rw [← hnd']
  exact hdeg

end ChowFormHeightComparison₂.CF
end
end

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Matrix GlobalTheory.ChowHt GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.D

theorem gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : MvPolynomial ι K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.equivHeightOneSpectrum.symm v) f = gaussNorm v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs gaussNorm
  congr 2
  funext s
  apply NNReal.eq
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply]
  show ((‖(FinitePlace.embedding v) (AddMonoidAlgebra.coeff f s)‖).toNNReal : ℝ) = HeightOneSpectrum.adicAbv K v (AddMonoidAlgebra.coeff f s)
  rw [FinitePlace.norm_embedding]
  exact Real.coe_toNNReal _ (AbsoluteValue.nonneg _ _)

theorem mean_eq_mahler {m k : ℕ} (hm : 1 ≤ m) (h : HermNorm m) {f : MvPolynomial (Fin k × Fin m) ℂ} (hf : f ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst h.mat⁻¹ f) = mahler h k f := by
  have hB : (h.mat * h.mat⁻¹)ᴴ * (h.mat * h.mat⁻¹) = 1 := by
    rw [Matrix.mul_nonsing_inv _ h.isUnit_det]
    simp
  rw [← GlobalTheory.CompanionTheory.Ar.HS.SphereMean.sphere_mean_eq_mahler m k h h.mat⁻¹ f hm hf hB]
  have hP : ∀ n, ReciprocityTheory.MultiplicativeHeights.sphereProb n = GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP n := by
    intro n
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP
    rw [ProbabilityTheory.cond, MeasureTheory.Measure.restrict_univ]
  have hE : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere k m,
      eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (linSubst h.mat⁻¹ f) =
        eval (fun p : Fin k × Fin m => (h.mat⁻¹ *ᵥ fun a => (↑(z p.1) : EuclideanSpace ℂ (Fin m)).ofLp a) p.2) f := by
    intro z
    unfold linSubst
    rw [MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    erw [MvPolynomial.aeval_bind₁]
    refine congrArg (fun g => MvPolynomial.aeval g f) ?_
    funext p
    simp [ReciprocityTheory.MultiplicativeHeights.blockPoint, ReciprocityTheory.MultiplicativeHeights.spherePoint, Matrix.mulVec, dotProduct, mul_comm]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  simp only [hP, hE]

theorem formHeight_one_eq {K : Type} [Field K] [NumberField K] {m k : ℕ} (hm : 1 ≤ m) (H : ArchData K m) (δ : ℕ)
    {f : MvPolynomial (Fin k × Fin m) K} (hf : f ≠ 0) :
    formHeight δ (1 : Matrix (Fin m) (Fin m) K) (fun σ => (H.normAt σ).mat⁻¹) f = chowHt H k δ f := by
  unfold formHeight chowHt
  rw [GlobalTheory.HeightUnique.linSubst_one, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  have e (σ : K →+* ℂ) : ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst (H.normAt σ).mat⁻¹ (MvPolynomial.map σ f)) =
      mahler (H.normAt σ) k (MvPolynomial.map σ f) :=
    mean_eq_mahler hm _ fun h0 => hf (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  simp only [gaussAbs_eq, e]
  ring

end ChowFormHeightComparison₂.CF.D

private theorem coneMap_comp_coordSubst {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N N' : ℕ}
    (M : Matrix (Fin N) (Fin N') K) (y : Fin N → Ω) :
    (GlobalTheory.CompHt.coneMap K y).comp (GlobalTheory.CompHt.coordSubst M) =
      GlobalTheory.CompHt.coneMap K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) := by
  apply MvPolynomial.algHom_ext
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, GlobalTheory.CompHt.coordSubst, GlobalTheory.CompHt.coneMap, MvPolynomial.aeval_X, map_sum,
    map_mul, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem aeval_linSubst {K L : Type} [Field K] [CommRing L] [Algebra K L] {B N n : ℕ}
    (M : Matrix (Fin N) (Fin n) K) (f : MvPolynomial (Fin B × Fin N) K) (u : Fin B × Fin n → L) :
    MvPolynomial.aeval u (linSubst M f) =
      MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, algebraMap K L (M p.2 k) * u (p.1, k)) f := by
  unfold linSubst
  rw [MvPolynomial.aeval_eq_bind₁]
  erw [MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g f) ?_
  funext p
  simp [MvPolynomial.aeval_X, MvPolynomial.aeval_C]

private theorem isChowForm_of_isChowFormInt {k : Type} [Field k] {N : ℕ} {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (hf : IsChowFormInt I e dl f) :
    GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  refine ⟨hf.ne_zero, fun p => ⟨fun hp => hf.dvd_of_forall_aeval_eq_zero
    (fun u hu => hp u ((hf.zero_iff u).1 hu)), ?_⟩⟩
  rintro ⟨q, rfl⟩ u hu
  rw [map_mul, (hf.zero_iff u).2 hu, zero_mul]

private theorem sum_algebraMap_mul_sum_eq_matrix_mul {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b c : ℕ}
    (M : Matrix (Fin a) (Fin b) K) (P : Matrix (Fin b) (Fin c) K) (z : Fin a → L) (k : Fin c) :
    ∑ j : Fin b, algebraMap K L (P j k) * ∑ i : Fin a, algebraMap K L (M i j) * z i =
      ∑ i, algebraMap K L ((M * P) i k) * z i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem sum_sum_algebraMap_mul_comm {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b : ℕ}
    (g : Matrix (Fin a) (Fin b) K) (v : Fin b → L) (z : Fin a → L) :
    ∑ j, (∑ k, algebraMap K L (g j k) * v k) * z j = ∑ k, v k * ∑ j, algebraMap K L (g j k) * z j := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

private theorem exists_right_inverse_of_span_col_eq_top {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) : ∃ P : Matrix (Fin m) (Fin N) K, g * P = 1 := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective g.mulVecLin
    (by rw [Matrix.range_mulVecLin, hg])
  refine ⟨LinearMap.toMatrix' r, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hr
  have h2 : LinearMap.toMatrix' g.mulVecLin = g := LinearMap.toMatrix'_toLin' g
  rw [LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id] at h1
  exact h1

private theorem isMultiHomog_of_isMultiHomogeneous_const {K : Type} [Field K] {B n δ : ℕ} (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f) : GroundTheory.Heights₂.Heights.IsMultiHomog δ f := by
  intro s hs
  funext b
  have hb : ∑ j : Fin n, s (b, j) = δ := hf s (MvPolynomial.mem_support_iff.2 hs) b
  rw [← hb, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [GroundTheory.Heights₂.Heights.groupWeight, Pi.single_apply]


open ChowFormHeightComparison₂.CF.D in
theorem ChowFormHeightComparison₂.CF.stForm : ChowFormHeightComparison₂.CF.StForm := by
  intro K Ω _ _ _ _ d N m δ g A hspan hA y Φ hΦ H hH
  obtain ⟨P, hgP⟩ := exists_right_inverse_of_span_col_eq_top g hspan
  have hne : Φ ≠ 0 := hΦ.ne_zero
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      exfalso
      have hirr := hΦ.irred
      have hC := MvPolynomial.eq_C_of_isEmpty Φ
      have hc : AddMonoidAlgebra.coeff Φ 0 ≠ 0 := fun h => hne (by rw [hC, h, map_zero])
      rw [hC] at hirr
      exact hirr.not_isUnit ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C)
    · exact h0
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exfalso
      have := congrFun (congrFun hgP ⟨0, hN⟩) ⟨0, hN⟩
      simp [Matrix.mul_apply] at this
    · exact h0
  refine ⟨isChowForm_of_isChowFormInt (dl := δ) ?_, isMultiHomog_of_isMultiHomogeneous_const _ (GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog), ?_⟩
  · refine ⟨GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog, PositivityTheory.UnitarySelfGeneration.UnitProductCombination.irreducible_linSubst hgP hΦ.irred, ?_⟩
    intro u
    rw [aeval_linSubst, hΦ.zero_iff]
    constructor
    · rintro ⟨z, hz0, hzI, hzu⟩
      refine ⟨fun k => ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j, ?_, ?_, ?_⟩
      · intro hx
        apply hz0
        have hx' : ∀ k, ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j = 0 := fun k => congrFun hx k
        funext i
        have h2 := sum_algebraMap_mul_sum_eq_matrix_mul g P z i
        simp only [hx', mul_zero, Finset.sum_const_zero, hgP, Matrix.one_apply] at h2
        simpa using h2.symm
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hzI
        show GlobalTheory.CompHt.coneMap K y (GlobalTheory.CompHt.coordSubst g h) = 0
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst]
        exact hh
      · intro i
        exact (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) z).symm.trans (hzu i)
    · rintro ⟨x, hx0, hxI, hxu⟩
      have hxz : ∀ k, x k = ∑ j, algebraMap K (AlgebraicClosure K) (g j k) *
          ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' := by
        intro k
        have hl : (MvPolynomial.X k - GlobalTheory.CompHt.coordSubst (P * g) (MvPolynomial.X k)) ∈
            GlobalTheory.CompHt.coneIdeal K (fun k => ∑ j, algebraMap K Ω (g j k) * y j) := by
          show GlobalTheory.CompHt.coneMap K _ _ = 0
          have e : (fun k => ∑ j, algebraMap K Ω ((P * g) j k) * ∑ i, algebraMap K Ω (g i j) * y i) =
              fun k => ∑ i, algebraMap K Ω (g i k) * y i := by
            funext k
            rw [sum_algebraMap_mul_sum_eq_matrix_mul, ← Matrix.mul_assoc, hgP, Matrix.one_mul]
          rw [map_sub, ← AlgHom.comp_apply, coneMap_comp_coordSubst, e, sub_self]
        have h3 := hxI _ hl
        rw [map_sub, GlobalTheory.CompHt.aeval_coordSubst, MvPolynomial.aeval_X, MvPolynomial.aeval_X, sub_eq_zero] at h3
        rw [h3]
        exact (sum_algebraMap_mul_sum_eq_matrix_mul P g x k).symm
      refine ⟨fun j => ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k', ?_, ?_, ?_⟩
      · intro hz
        apply hx0
        have hz' : ∀ j, ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' = 0 := fun j => congrFun hz j
        funext k
        rw [hxz k]
        simp [hz']
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hxI
        show GlobalTheory.CompHt.coneMap K _ (GlobalTheory.CompHt.coordSubst P h) = 0
        have e : (fun k => ∑ j, algebraMap K Ω (P j k) * ∑ i, algebraMap K Ω (g i j) * y i) = y := by
          funext k
          rw [sum_algebraMap_mul_sum_eq_matrix_mul, hgP]
          simp [Matrix.one_apply]
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst, e]
        exact hh
      · intro i
        refine (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) _).trans ?_
        simp only [← hxz]
        exact hxu i
  · rw [← PositivityTheory.UnitarySelfGeneration.UnitProductCombination.formHeight_gen hN g hspan A hA (fun σ => (H.normAt σ).mat⁻¹) ?_ hne hΦ.homog,
      formHeight_one_eq hm H δ (GlobalTheory.HeightUnique.linSubst_ne_zero hgP hne)]
    intro σ x
    have h1 := hH σ x
    unfold GroundTheory.Heights₂.Heights.HermNorm.dualNorm at h1
    rw [← h1, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Matrix.mulVec, dotProduct, ← Matrix.transpose_nonsing_inv]
end
end

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SumNormSqUnitary
set_option autoImplicit false

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts
open GroundTheory.Heights₂.Heights (HermNorm ArchData)

namespace ChowFormHeightComparison₂.CF

theorem sum_normSq_eq {m : ℕ} (w : Fin m → ℂ) : ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_normSq_unitary {m : ℕ} {V : Matrix (Fin m) (Fin m) ℂ} (h : star V * V = 1) (x : Fin m → ℂ) :
    ∑ i, ‖(V *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_normSq_eq, sum_normSq_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, h, Matrix.vecMul_one]

def normOf {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : M.det ≠ 0) : HermNorm m :=
  ⟨M⁻¹, Matrix.isUnit_nonsing_inv_det M h.isUnit⟩

theorem dualNorm_normOf {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : M.det ≠ 0) (y : Fin m → ℂ) :
    (normOf M h).dualNorm y = √(∑ a, ‖∑ k, M k a * y k‖ ^ 2) := by
  have hT : IsUnit Mᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit
  simp only [HermNorm.dualNorm, normOf]
  rw [Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hT]
  congr 1

theorem norm_normOf_conj {m : ℕ} {M M' U : Matrix (Fin m) (Fin m) ℂ} (h : M.det ≠ 0) (h' : M'.det ≠ 0)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (e : M' = M.map (starRingEnd ℂ) * U) (u : Fin m → ℂ) :
    (normOf M' h').norm (star u) = (normOf M h).norm u := by
  subst e
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hinvU : U⁻¹ = star U := Matrix.inv_eq_left_inv hU1
  have hmap : (M.map (starRingEnd ℂ))⁻¹ = (M⁻¹).map (starRingEnd ℂ) := by
    have h1 : M.map (starRingEnd ℂ) = (Mᴴ)ᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have h2 : (M⁻¹).map (starRingEnd ℂ) = ((M⁻¹)ᴴ)ᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [h1, h2, ← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
  have hv : (M⁻¹).map (starRingEnd ℂ) *ᵥ star u = star (M⁻¹ *ᵥ u) := by
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have key : (M.map (starRingEnd ℂ) * U)⁻¹ *ᵥ star u = star U *ᵥ star (M⁻¹ *ᵥ u) := by
    rw [Matrix.mul_inv_rev, hinvU, hmap, ← Matrix.mulVec_mulVec, hv]
  simp only [HermNorm.norm, normOf]
  rw [key]
  congr 1
  have hV : star (star U) * star U = 1 := by rw [star_star]; exact hU2
  rw [sum_normSq_unitary hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.star_apply]

theorem glue : StMain → StModel → StForm → GlobalTheory.Published.ArExists → PositivityTheory.UnitarySelfGeneration.ChowFormHeight := by
  intro hMain hModel hForm hAr
  intro K Ω _ _ _ _ d N m δ g A hg hA _ y Z hcl hvar Φ hΦ H hH e hgen s hval hs Mt hdet hc harch
  haveI := Z.integral
  obtain ⟨hEmb, hgenI⟩ := hModel K Ω m (fun k => ∑ j, algebraMap K Ω (g j k) * y j) Z hcl H hH e hgen s hval hs
    hvar.charZero
  let D : ArchData K m := ⟨fun σ => normOf (Mt (σ.comp (algebraMap (𝓞 K) K))) (hdet _), fun σ u => by
      obtain ⟨U, hU, hUe⟩ := hc (σ.comp (algebraMap (𝓞 K) K))
      exact norm_normOf_conj (hdet _) (hdet _) hU hUe u⟩
  have hdual : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      (D.normAt σ).dualNorm (fun k => ∑ j, σ (g j k) * x j) = Adelic.archSize (A σ) x := by
    intro σ x
    show (normOf (Mt (σ.comp (algebraMap (𝓞 K) K))) (hdet _)).dualNorm _ = _
    rw [dualNorm_normOf, harch σ x]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  obtain ⟨hCF, hMH, hFH⟩ := hForm K Ω d N m δ g A hg hA y Φ hΦ D hdual
  obtain ⟨h0, hh0⟩ := (hAr (𝓞 K) Z.Z Z.s d hvar).1 (HermLB.fs Z.s hH s hs Mt hdet hc)
  have hSI : (HermLB.fs Z.s hH s hs Mt hdet hc).IsSelfInter (h0 (genericPoint _)) := ⟨h0, hh0, rfl⟩
  have hFS : ∀ σ : K →+* ℂ,
      IsFS ((HermLB.fs Z.s hH s hs Mt hdet hc).φ (σ.comp (algebraMap (𝓞 K) K))) s (D.normAt σ) := by
    intro σ i z _
    refine (Weight.fsBasis_φ (p := Z.s) (σ := σ.comp (algebraMap (𝓞 K) K)) hH s hs _ (hdet _) i z).trans ?_
    show _ = Real.log (((normOf (Mt (σ.comp (algebraMap (𝓞 K) K))) (hdet _)).dualNorm _) ^ 2)
    rw [dualNorm_normOf, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    rfl
  have hEq := hMain K m D d Z.Z Z.s (HermLB.fs Z.s hH s hs Mt hdet hc) s hvar hEmb hFS δ
    (ChowHt.linSubst g Φ) (hgenI ▸ hCF) hMH _ hSI
  rw [hFH, ← hEq]
  exact hSI

end ChowFormHeightComparison₂.CF
end
end

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DescEval
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.Points

namespace ChowFormHeightComparison₂.CF

namespace ModelEmbedding

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω} {m : ℕ}
  {σ : Fin m → H.Sec} {t : Fin m → Ω}

theorem emb (hM : M.IsCl t) (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hs : ⨆ k, nonzeroLocus (σ k) = ⊤) : Emb M.s σ := by
  refine ⟨hH, hs, fun i => ?_⟩
  have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
    have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
    subst this
    infer_instance
  have key' := mem_nonzeroLocus_iff_div hH hd hv (PositivityTheory.UnitarySelfGeneration.UnitProductCombination.exists_unit hd hv hs) i
  generalize nonzeroLocus (σ i) = W at key' ⊢
  by_cases hi : t i = 0
  · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
    subst hW
    refine ⟨isAffineOpen_bot _, fun _ => 0, fun f => ⟨0, Subsingleton.elim _ _⟩, fun j l => ?_⟩
    have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
    exact Subsingleton.elim _ _
  · obtain ⟨U, hUa, hUe, hR⟩ := hM.2 i hi
    have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
    subst hWU
    have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
    have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
      (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
    choose r hr using hr
    refine ⟨hUa, r, fun f => ?_, fun j l => ?_⟩
    · have h1 : valF M.pt W f ∈ M.ringOn W := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
      rw [hR, Algebra.adjoin_range_eq_range_aeval] at h1
      obtain ⟨q, hq⟩ := h1
      have e : (M.res W hne).comp (eval₂Hom (algX M.s W) r) =
          (aeval (R := o) fun j => t j / t i).toRingHom :=
        MvPolynomial.ringHom_ext (fun a => by
          simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
          exact (M.res_apply W hne _).trans (M.valF_constFn hne a)) fun j => by
          simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
          exact (M.res_apply W hne _).trans (hr j)
      exact ⟨q, M.res_injective W hne ((RingHom.congr_fun e q).trans (hq.trans (M.res_apply W hne f).symm))⟩
    · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
      · have hl' : (H.U l : Set M.Z).Nonempty := hl.mono fun z (hz : z ∈ W ⊓ H.U l) => hz.2
        apply M.res_injective _ hl
        rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
          hv j l hl', hv i l hl', hr]
        have hdl := hd.ne l
        field_simp
      · have := hempty _ hl
        exact Subsingleton.elim _ _

theorem desc_eval (U : M.Z.Opens) (hV : M.pt (IsLocalRing.closedPoint Ω) ∈ U) (f : Γ(M.Z, U)) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt)).hom
      ((M.Z.evaluation U _ hV).hom f) = valF M.pt U f := by
  rw [valF_eq_valR, valR_eq M.pt U (M.top_le_preimage_pt ⟨_, hV⟩), ← germ_stalkClosedPointTo_eq_valMap,
    ← CommRingCat.comp_apply, ← Scheme.germ_residue, Category.assoc, Scheme.residue_descResidueField]

end ModelEmbedding

open ModelEmbedding

attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem stModel : StModel := by
  intro K Ω _ _ _ _ m t Z hZ H hH e he s hv hs _
  refine ⟨emb hZ hH he hv hs, ?_⟩
  have key : ∀ (i : H.ι) (h : Z.pt (IsLocalRing.closedPoint Ω) ∈ H.U i),
      RingHom.ker (coneHom Z.s s _ i h) =
        (GlobalTheory.CompHt.coneIdeal K t).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := fun i h => by
    have hne : (H.U i : Set Z.Z).Nonempty := ⟨_, h⟩
    have e1 : (Polynomial.mapRingHom (Scheme.descResidueField
        (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Z.pt)).hom).comp (coneHom Z.s s _ i h) =
        (GlobalTheory.CompHt.coneMap K ((e i)⁻¹ • t)).toRingHom.comp (MvPolynomial.map (algebraMap (𝓞 K) K)) :=
      MvPolynomial.ringHom_ext (fun a => by
        simp only [coneHom, GlobalTheory.CompHt.coneMap, eval₂Hom_C, RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, Polynomial.algebraMap_apply]
        exact congrArg Polynomial.C ((desc_eval _ h _).trans ((Z.valF_constFn hne a).trans
          (IsScalarTower.algebraMap_apply (𝓞 K) K Ω a)))) fun k => by
        simp only [coneHom, GlobalTheory.CompHt.coneMap, eval₂Hom_X', RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          aeval_X]
        exact congrArg (fun c => Polynomial.X * Polynomial.C c) ((desc_eval _ h _).trans ((hv k i hne).trans
          (div_eq_inv_mul _ _)))
    rw [← GlobalTheory.CompHt.coneIdeal_smul (inv_ne_zero (he.ne i))]
    have hinj : Function.Injective (Polynomial.mapRingHom (Scheme.descResidueField
        (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Z.pt)).hom) :=
      Polynomial.map_injective _ (RingHom.injective _)
    exact (RingHom.ker_comp_of_injective (coneHom Z.s s _ i h) hinj).symm.trans
      ((congrArg RingHom.ker e1).trans (RingHom.comap_ker _ _).symm)
  have h2 : ptIdeal Z.s s (genericPoint Z.Z) =
      (GlobalTheory.CompHt.coneIdeal K t).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [← Z.pt_apply (IsLocalRing.closedPoint Ω)]
    have hm : Z.pt (IsLocalRing.closedPoint Ω) ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hl⟩ := Opens.mem_iSup.1 hm
    exact le_antisymm ((iInf₂_le l hl).trans (key l hl).le) (le_iInf₂ fun i h => (key i h).ge)
  rw [genIdeal, h2]
  exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin m))) (MvPolynomial (Fin m) K) _

end ChowFormHeightComparison₂.CF
end
end

namespace ChowFormHeightComparison₂.CF

open GroundTheory.Heights₂.Heights in
theorem chowFormHeight_of_arch (hA : StArch) (hM : MahlerSection.Statement) (hE : GlobalTheory.Published.ArExists) :
    PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  glue (stMain_of (stVert stPts stPull stDiv) hA
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full hM ChowFormBaseChange.full BaseChangeAvoid.full)
    ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full) stModel stForm hE

end ChowFormHeightComparison₂.CF

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubscheme
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix


open GlobalTheory.Mean4O.CombForm in
theorem exists_subAtlas : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp π _ hπ e A hA hs
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, h⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, h, hπ]⟩
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hq
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hp
  have hc : Continuous (ptMap π hπ σ) := PtsOver.continuous_map π hπ _
  have hinj : Function.Injective (ptMap π hπ σ) := fun a b h =>
    Subtype.ext ((cancel_mono π).1 (congrArg Subtype.val h))
  have hE : IsClosedEmbedding (ptMap π hπ σ) := hc.isClosedEmbedding hinj
  let h : CxPts q σ ≃ₜ Set.range (ptMap π hπ σ) := hE.isEmbedding.toHomeomorph
  haveI : CompactSpace (Set.range (ptMap π hπ σ)) := h.compactSpace
  let A' : FinHolAtlas e (CxPts q σ) := (AnRead.all q σ e).finAtlas
  have hA' : IsAlgAtlas A' := AnRead.isAlgAtlas_finAtlas _
  have hm : HoloMap A' A (ptMap π hπ σ) := hA.holoMap hA' (f := π) fun _ => rfl
  have hB : HoloMap (tAtlas A' h) A Subtype.val := ⟨continuous_subtype_val, fun j l => hm.2 j l⟩
  refine ⟨tAtlas A' h, hB, fun L v hv => ?_⟩
  have hsm (i : Fin e) : (L i).φ.IsSmooth hA.anRead := (Weight.isCInf_iff_isSmooth _).1 (L i).cInf
  have hv' : Continuous fun y => v (ptMap π hπ σ y) := hv.comp hc
  have hP (i : Fin e) : IsPotential A' ((L i).pull π hπ).φ.locPot :=
    Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth _).1 ((L i).pull π hπ).cInf)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact k Y q σ e A' hA' (fun i => (L i).pull π hπ) _ hv'.measurable
  rw [h₂ (h₁.2 (mIntegrableCont _ _ hP _ hv')),
    GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport e _ _ A' h _ _
      (fun i => isPotentialPullback A _ _ hB _ ((hsm i).isPotential hA))
      (hv.comp continuous_subtype_val)]
  exact (SameForm.mInt_eq (fun i => (hsm i).sameForm_pull hA hA' π hπ) _).symm

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubschemeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  first | exact @GlobalTheory.Mix.exists_subAtlas | exact GlobalTheory.Mix.exists_subAtlas | (intros; apply GlobalTheory.Mix.exists_subAtlas <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealVanishingIdealClosure
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncForm

theorem ideal_vanishingIdeal_closure {X : Scheme.{0}} (U : X.affineOpens) {η : X} (hη : η ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).ideal U =
      (U.2.primeIdealOf ⟨η, hη⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have emb := hU.fromSpec.isOpenEmbedding
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨η, hη⟩) = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have h2 : hU.fromSpec ⁻¹' ({η} : Set X) = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext Q
    exact ⟨fun h => emb.injective (h.trans h1.symm), fun h => (congrArg _ h).trans h1⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure ({η} : Set X)) = _
  have h3 := (emb.isOpenMap.preimage_closure_eq_closure_preimage emb.continuous {η}).trans
    (congrArg closure h2)
  exact (congrArg PrimeSpectrum.vanishingIdeal h3).trans
    ((PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _))

theorem exists_isLocalization_stalk {X : Scheme.{0}} (U : X.affineOpens) {y η : X} (hy : y ∈ U.1)
    (hη : η ∈ U.1) (hηy : η ⤳ y) (p : Ideal (X.presheaf.stalk y)) [p.IsPrime]
    (hp : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) y = p) :
    ∃ _ : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η),
      IsLocalization.AtPrime (X.presheaf.stalk η) p ∧ ∀ a : Γ(X, U.1),
        X.presheaf.germ U.1 η hη a =
          algebraMap (X.presheaf.stalk y) (X.presheaf.stalk η) (X.presheaf.germ U.1 y hy a) := by
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(X, U.1) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  let Pη := hU.primeIdealOf ⟨η, hη⟩
  have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
  have emb := hU.fromSpec.isOpenEmbedding
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact emb.isInducing.specializes_iff
  have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
  have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(X, U.1)) Pη.asIdeal :=
    Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
  rw [WMult.stalkId_eq_map_germ _ y U hy, ideal_vanishingIdeal_closure U hη] at hp
  have hPeq : Pη.asIdeal = p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) := by
    rw [← hp]
    exact (IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
      (X.presheaf.stalk y) Pη.isPrime hdisj).symm
  let T := Localization.AtPrime p
  have hT : IsLocalization.AtPrime T (p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Py.asIdeal.primeCompl) (S := X.presheaf.stalk y) (T := T) p
  have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
    have hsm : Pη.asIdeal.primeCompl =
        (Ideal.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) p).primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
    rw [hsm]; exact hT
  let ηU : U.1 := ⟨η, hη⟩
  let algη : Algebra Γ(X, U.1) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ηU
  have hlocη : IsLocalization.AtPrime (X.presheaf.stalk η) Pη.asIdeal :=
    hU.isLocalization_stalk ηU
  let φ : X.presheaf.stalk η ≃ₐ[Γ(X, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
  let algYη : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
    (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk y) T)).toAlgebra
  refine ⟨algYη, (IsLocalization.isLocalization_iff_of_ringEquiv (M := p.primeCompl)
      (S := T) φ.symm.toRingEquiv).mp inferInstance, fun a => ?_⟩
  have h1 := (φ.symm.commutes a).symm
  rw [IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk y) T] at h1
  exact h1

theorem germ_eq_unit_mul_monomial : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x → ∀ (i : B.ι) (hi : x ∈ B.U i), ∃ (n : ℕ) (g : Fin n → X.presheaf.stalk x) (e : {a : Fin r // x ∈ (Closeds.closure {z a})} ↪ Fin n) (u : (X.presheaf.stalk x)ˣ) (_ : Fintype {a : Fin r // x ∈ (Closeds.closure {z a})}), FinalTheorems.Rsp (X.presheaf.stalk x) n g ∧ (∀ a, FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a.1})) x = Ideal.span {g (e a)}) ∧ X.presheaf.germ _ x hi (s.f i) = u * ∏ a, g (e a) ^ ((divOfSec hB s hs).mult (z a.1)).toNat := by
  classical
  intro X _ _ B hB s hs r z _ hz hZ x hx i hi
  obtain ⟨hreg, n, g, e, hg, hI⟩ := hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVi⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
  let U : X.affineOpens := ⟨V, hV⟩
  have hVi' : V ≤ B.U i := hVi
  let t : Γ(X, V) := X.presheaf.map (homOfLE hVi').op (s.f i)
  have ht : ∀ (w : X) (hw : w ∈ V), X.presheaf.germ V w hw t =
      X.presheaf.germ _ w (hVi' hw) (s.f i) := fun w hw =>
    X.presheaf.germ_res_apply (homOfLE hVi') w hw _
  set γ := X.presheaf.germ _ x hi (s.f i) with hγ
  have hγ0 : γ ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))
  let J : Finset (Fin n) := Finset.univ.map e
  have hrad : (∏ j ∈ J, g j) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    let P : PrimeSpectrum Γ(X, V) := ⟨Q.comap (X.presheaf.germ V x hxV).hom, inferInstance⟩
    have htP : t ∈ P.asIdeal := by
      change X.presheaf.germ V x hxV t ∈ Q
      rw [ht]
      exact hQγ (Ideal.mem_span_singleton_self _)
    have hmem : hV.fromSpec P ∈ V := by
      have : hV.fromSpec P ∈ Set.range hV.fromSpec := ⟨P, rfl⟩
      rwa [hV.range_fromSpec] at this
    have hnz : hV.fromSpec P ∉ nonzeroLocus s := by
      rw [mem_nonzeroLocus_iff s i (hVi' hmem)]
      intro h
      have h' : hV.fromSpec P ∈ X.basicOpen t := by
        rw [Scheme.mem_basicOpen _ _ _ hmem, ht]
        exact (Scheme.mem_basicOpen _ _ _ _).1 h
      have h'' : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen t := h'
      rw [hV.fromSpec_preimage_basicOpen] at h''
      exact h'' htP
    have hc : hV.fromSpec P ∈ ((nonzeroLocus s : Set X)ᶜ) := hnz
    rw [hZ] at hc
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hc
    have hPx : hV.fromSpec P ⤳ x := by
      have h1 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have h2 : P ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
        rw [hV.primeIdealOf_eq_map_closedPoint]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
      have h3 := ((PrimeSpectrum.le_iff_specializes _ _).1 h2).map hV.fromSpec.continuous
      rwa [h1] at h3
    have hxa : x ∈ Closeds.closure {z a} := hPx.mem_closed isClosed_closure ha
    have hsup : hV.fromSpec P ∈
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})).support : Set X) := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact ha
    rw [WMult.mem_support_fromSpec_iff _ U hV] at hsup
    have h3 : Ideal.span {g (e ⟨a, hxa⟩)} ≤ Q := by
      rw [← hI ⟨a, hxa⟩, WMult.stalkId_eq_map_germ _ x U hxV]
      exact Ideal.map_le_iff_le_comap.mpr hsup
    exact Q.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _)))
      (h3 (Ideal.mem_span_singleton_self _))
  obtain ⟨u, m, -, hγu⟩ := eq_unit_mul_monomial g hg.1 hg.2 J hγ0 hrad
  refine ⟨n, g, e, u, inferInstance, hg, hI, ?_⟩
  have hord : ∀ a, ((divOfSec hB s hs).mult (z a.1)).toNat = m (e a) := by
    intro a
    have hsp : z a.1 ⤳ x := specializes_iff_mem_closure.2 a.2
    have hzV : z a.1 ∈ V := hsp.mem_open V.isOpen hxV
    have hpr : Prime (g (e a)) := prime_of_regular_params g hg.1 hg.2 _
    have hP : (Ideal.span {g (e a)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
    obtain ⟨alg, hloc, hgerm⟩ := exists_isLocalization_stalk U hxV hzV hsp _ (hI a)
    have h := WMult.ord_isLocalization_eq_exponent g hg.1 hg.2 J u m (e a)
      (Finset.mem_map_of_mem e (Finset.mem_univ _)) (X.presheaf.stalk (z a.1))
    rw [← hγu, hγ, ← ht x hxV, ← hgerm t, ht] at h
    rw [mult_divOfSec (hz _) (hVi' hzV), Int.toNat_natCast]
    exact (congrArg ENat.toNat h).trans (ENat.toNat_natCast _)
  rw [hγu, Finset.prod_map]
  exact congrArg _ (Finset.prod_congr rfl fun a _ => by rw [hord])

end GlobalTheory.SncForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSnc

open GlobalTheory.ShFam (LiesIn ev_eq_zero_iff isOpen_not_liesIn)

section Local

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem eventually_ev_eq (x : CxPts p σ) {U V : X.Opens} (hU : x.1 (IsLocalRing.closedPoint ℂ) ∈ U)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(X, U)) (g : Γ(X, V))
    (h : X.presheaf.germ U _ hU f = X.presheaf.germ V _ hV g) :
    ∀ᶠ y in 𝓝 x, ev p σ U f y = ev p σ V g y := by
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hres : resG X hWU f = resG X hWV g := he
  refine Filter.eventually_of_mem ((isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)) fun z hz => ?_
  rw [← ev_res hWU hz, ← ev_res hWV hz, hres]

theorem eventually_ev_ne_zero (x : CxPts p σ) {V : X.Opens} (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V)
    (g : Γ(X, V)) (h : IsUnit (X.presheaf.germ V _ hV g)) : ∀ᶠ y in 𝓝 x, ev p σ V g y ≠ 0 := by
  have hx : x ∈ ptsIn p σ (X.basicOpen g) := mem_ptsIn.2 ((X.mem_basicOpen g _ hV).2 h)
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds hx) fun z hz => ?_
  exact (mem_ptsIn_basicOpen (ptsIn_mono (X.basicOpen_le g) hz) g).1 hz

theorem eventually_ev_eq_zero_iff [IsLocallyNoetherian X] (x : CxPts p σ) (V : X.affineOpens)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) (g : Γ(X, V.1)) (C : Closeds X)
    (h : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal C) (x.1 (IsLocalRing.closedPoint ℂ)) =
      Ideal.span {X.presheaf.germ V.1 _ hV g}) :
    ∀ᶠ y in 𝓝 x, (ev p σ V.1 g y = 0 ↔ LiesIn y C) := by
  rw [WMult.stalkId_eq_map_germ _ _ V hV] at h
  obtain ⟨s, hs, H⟩ := GlobalTheory.IdealSpread.ideal_eq_span_of_germ X _ V _ hV g
    (IsLocallyNoetherian.component_noetherian V) h
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hs)) fun z hz => ?_
  rw [← ev_res (X.basicOpen_le s) hz]
  exact ev_eq_zero_iff (V := X.affineBasicOpen s) (H s le_rfl) hz

theorem mem_range_ptMap_closι (z : X) (y : CxPts p σ) :
    y ∈ Set.range (ptMap (closι z) rfl σ) ↔ LiesIn y (Closeds.closure {z}) := by
  have hr : Set.range (closι z) = (Closeds.closure {z} : Closeds X) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  constructor
  · rintro ⟨w, rfl⟩
    have : closι z (w.1 (IsLocalRing.closedPoint ℂ)) ∈ Set.range (closι z) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  · intro hy
    have : IsReduced (Sp ℂ) := inferInstanceAs (IsReduced (Spec _))
    have hle : Set.range y.1 ⊆ Set.range (closι z) := by
      rintro _ ⟨a, rfl⟩
      have ha : a = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      rw [hr, ha]
      exact hy
    have hk : (closι z).ker ≤ y.1.ker := ker_le_ker_of_range_subset_of_isReduced (closι z) y.1 hle
    have hl := IsClosedImmersion.lift_fac (closι z) y.1 hk
    exact ⟨⟨IsClosedImmersion.lift (closι z) y.1 hk, by rw [← Category.assoc, hl, y.2]⟩, Subtype.ext hl⟩

end Local

theorem exists_compatChart {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) (x : CxPts p σ)
    {N : Set (CxPts p σ)} (hN : N ∈ 𝓝 x) (V : X.affineOpens) (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) {n : ℕ}
    (G : Fin n → Γ(X, V.1))
    (hR : FinalTheorems.Rsp (X.presheaf.stalk (x.1 (IsLocalRing.closedPoint ℂ))) n (fun j => X.presheaf.germ V.1 _ hV (G j))) :
    ∃ (hn : n ≤ D) (ψ : OpenPartialHomeomorph (CxPts p σ) (Fin D → ℂ)), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ N ∧ ψ.source ⊆ ptsIn p σ V.1 ∧
      ∀ y ∈ ψ.source, ∀ j, ψ y (Fin.castLE hn j) = ev p σ V.1 (G j) y := by
  haveI : CharZero F := σ.charZero
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) (p := p) (σ := σ) x
  have hli := SncChart.linearIndependent_fderiv_params F X p D σ c x hc V hV n G hR
  have hxV : x ∈ ptsIn p σ V.1 := mem_ptsIn.2 hV
  have h0 : ∀ i, ev p σ V.1 (G i) x = 0 := by
    intro i
    by_contra hne
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hxV (G i)).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hV] at hb
    have hmem : X.presheaf.germ V.1 _ hV (G i) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨i, rfl⟩
    exact hmem hb
  have hn : n ≤ D := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V D) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F X p D σ c x hc V.1 hxV n G h0 hli
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.1 hN
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  refine ⟨hn, ψ, ?_, hψs ▸ ⟨hx0, hxO⟩, fun y hy => hON (hψs ▸ hy).2, fun y hy => hsub (hψs ▸ hy).1,
    fun y hy j => hev y (hψs ▸ hy).1 (Fin.castLE hn j) j.2⟩
  refine GlobalTheory.DivSec.isCompatChart_of_holAlong F X p σ D A hA ψ (fun j => ?_) ?_
  · intro V _ _ _ B' y hB' hy hm
    exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
  · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1

theorem isSNC_locSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  intro F _ X _ _ p σ D _ hsm A hA M s hs r z hz hco hzero hsnc x
  classical
  haveI := hsm
  have hxi := mem_pick (p := p) (σ := σ) M.φ.isLB x
  have hi := mem_ptsIn.1 hxi
  obtain ⟨n, g, e, u, inst, hR, hI, hf⟩ :=
    GlobalTheory.SncForm.germ_eq_unit_mul_monomial X M.B M.φ.isLB s hs r z hz hco hzero _ (hsnc _) (pick M.φ.isLB x) hi
  obtain ⟨V, hV, G', hG'⟩ := GlobalTheory.DivSec.exists_affine_germ_eq X (x.1 (IsLocalRing.closedPoint ℂ)) (n + 1)
    (Fin.cons (u : X.presheaf.stalk _) g)
  let G : Fin n → Γ(X, V.1) := fun j => G' j.succ
  have hG : ∀ j, X.presheaf.germ V.1 _ hV (G j) = g j := fun j => hG' j.succ
  have hU : X.presheaf.germ V.1 _ hV (G' 0) = u := hG' 0
  have e1 := eventually_ev_eq x hi hV (s.f (pick M.φ.isLB x))
    (G' 0 * ∏ a, G (e a) ^ ((divOfSec M.φ.isLB s hs).mult (z a.1)).toNat) (by
      rw [hf, map_mul, map_prod, hU]
      simp only [map_pow, hG])
  have e2 := eventually_ev_ne_zero x hV (G' 0) (hU ▸ u.isUnit)
  have e3 := Filter.eventually_all.2 fun a => eventually_ev_eq_zero_iff x V hV (G (e a)) _ (by rw [hG]; exact hI a)
  have e4 : ∀ᶠ y in 𝓝 x, ∀ a, ¬ LiesIn x (Closeds.closure {z a}) → ¬ LiesIn y (Closeds.closure {z a}) :=
    Filter.eventually_all.2 fun a => by
      by_cases h : LiesIn x (Closeds.closure {z a})
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · exact Filter.eventually_of_mem ((isOpen_not_liesIn _).mem_nhds h) fun y hy _ => hy
  have e5 : ∀ᶠ y in 𝓝 x, y ∈ M.φ.locPot.U x := (M.φ.locPot.isOpen_U x).mem_nhds (M.φ.locPot.mem_U x)
  obtain ⟨hn, ψ, hψ, hxψ, hN, hψV, hev⟩ := exists_compatChart hA x (e1.and (e2.and (e3.and (e4.and e5)))) V hV G
    (by rw [funext hG]; exact hR)
  let τ : Fin r → Option (Fin D) := fun a =>
    if h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a} then some (Fin.castLE hn (e ⟨a, h⟩)) else none
  refine ⟨ψ, hψ, hxψ, fun y hy => (hN hy).2.2.2.2, τ, ?_, ?_, ev p σ V.1 (G' 0), ?_, fun y hy => (hN hy).2.1, ?_⟩
  · intro a a' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with ha ha'
    have := Fin.castLE_injective hn ((Option.some.inj h1).trans (Option.some.inj h2).symm)
    exact congrArg Subtype.val (e.injective this)
  · intro a
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_range_ptMap_closι]
    refine and_comm.trans (and_congr_right fun hy => ?_)
    by_cases h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}
    · simp only [τ, dif_pos h, Option.some.injEq, exists_eq_left', hev y hy]
      exact ((hN hy).2.2.1 ⟨a, h⟩).symm
    · simp only [τ, dif_neg h, reduceCtorEq, false_and, exists_false, iff_false]
      exact (hN hy).2.2.2.1 a h
  · exact (hA.holoOn_iff hA.anRead ψ.open_source).2 ((hA.anRead.holoOn_ev V.1 (G' 0)).mono hψV)
  · intro y hy
    refine (hN hy).1.trans ?_
    rw [ev_mul, ev_eq (hψV hy) (∏ _, _), map_prod,
      ← Fintype.prod_subtype_mul_prod_subtype (fun a => x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a})]
    congr 1
    rw [Finset.prod_eq_one (s := Finset.univ)
      (f := fun a : {a // ¬ x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}} => _)
      (fun a _ => by simp only [τ, dif_neg a.2]), mul_one]
    refine Finset.prod_congr (by ext; simp) fun a _ => ?_
    simp only [τ, dif_pos a.2, map_pow, hev y hy, ev_eq (hψV hy)]

end GlobalTheory.SecSnc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  first | exact @GlobalTheory.SecSnc.isSNC_locSec | exact GlobalTheory.SecSnc.isSNC_locSec | (intros; apply GlobalTheory.SecSnc.isSNC_locSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZero
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncComp

theorem smooth_of_regular_stalk (K : Type) [Field K] [PerfectField K] (Y : Scheme.{0}) (q : Y ⟶ Sp K)
    [LocallyOfFiniteType q] (d : ℕ)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = d) :
    SmoothOfRelativeDimension d q := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  choose A _ _ j _ pt hj hq using exists_affine_chart_over q
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (.of (A y))) j (fun y => ⟨y, pt y, hj y⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d) 𝒰 fun (y : Y) => ?_
  change SmoothOfRelativeDimension d (j y ≫ q)
  have hft : LocallyOfFiniteType (spMap (algebraMap K (A y))) := by
    have : LocallyOfFiniteType (j y ≫ q) := inferInstance
    rwa [hq y] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType K (A y) := RingHom.finiteType_algebraMap.mp hft
  rw [hq y]
  refine RegGenSmooth.smooth_of_regular K (A y) d fun m hm => ?_
  let w : Spec (.of (A y)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have hw : IsClosed ({w} : Set (Spec (.of (A y)))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have hc : IsClosed ({j y w} : Set Y) := by
    have h1 := (j y).isOpenEmbedding.preimage_closedPoints
    have h2 : w ∈ (j y) ⁻¹' closedPoints Y := by rw [h1]; exact hw
    exact h2
  obtain ⟨h1, h2⟩ := h _ hc
  let e := (asIso ((j y).stalkMap w) ≪≫ Spec.stalkIso (.of _) w).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

theorem smooth_component : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  intro F _ _ X _ p e _ hsm r z hL a
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p (e + 1) hsm
  refine smooth_of_regular_stalk F _ _ e fun y hy => ?_
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})
  have hc : IsClosed ({closι (z a) y} : Set X) := by
    simpa using (closι (z a)).isClosedEmbedding.isClosedMap _ hy
  have hd := (ProperCut.ringKrullDim_stalk_eq p hc).trans hdim
  obtain ⟨hreg, n, t, ε, hR, hI⟩ := hL (closι (z a) y)
  have hmem : closι (z a) y ∈ Closeds.closure {z a} := by
    have := Vanishing.ι_mem_support I y
    have h := Scheme.IdealSheafData.coe_support_vanishingIdeal (Closeds.closure {z a})
    exact h.le this
  have hker : RingHom.ker ((closι (z a)).stalkMap y).hom = Ideal.span {t (ε ⟨a, hmem⟩)} :=
    (Vanishing.ker_stalkMap I y).trans (hI ⟨a, hmem⟩)
  have hm : t (ε ⟨a, hmem⟩) ∈ IsLocalRing.maximalIdeal _ := hR.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := isRegularLocalRing_quotient_of_not_mem_sq hm ((regular_params_spec t hR.1 hR.2).1 _)
  let φ := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closι (z a)).stalkMap_surjective y))
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv φ]
  rw [hd] at h2
  generalize ringKrullDim (X.presheaf.stalk (closι (z a) y) ⧸ Ideal.span {t (ε ⟨a, hmem⟩)}) = u at h2
  induction u using WithBot.recBotCoe with
  | bot => exact absurd h2 (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h2) (ENat.top_ne_coe _)
    | coe u =>
      have : u + 1 = e + 1 := by exact_mod_cast h2
      exact_mod_cast Nat.succ_injective this

end GlobalTheory.SncComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_snc_component_closure_charZero : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  first | exact @GlobalTheory.SncComp.smooth_component | exact GlobalTheory.SncComp.smooth_component | (intros; apply GlobalTheory.SncComp.smooth_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePoints
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncGenericPoints

theorem mem_vanishingIdeal_closure {X : Scheme.{0}} (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    (s : Γ(X, U.1)) (hs : ¬ IsUnit (X.presheaf.germ U.1 x hx s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hsq
  have hp : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact hsq
  have hq' : U.2.fromSpec q ∈ closure ({x} : Set X) := hq
  have hsp : x ⤳ U.2.fromSpec q := specializes_iff_mem_closure.2 hq'
  have hxs : x ∈ X.basicOpen s := hsp.mem_open (X.basicOpen s).isOpen hp
  exact hs ((X.mem_basicOpen s x hx).1 hxs)

theorem maximalIdeal_le_stalkId {X : Scheme.{0}} (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x := by
  intro a ha
  obtain ⟨V, hxV, f, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hle : W ≤ V := hWV
  have e : X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hle).op f) = X.presheaf.germ V x hxV f :=
    X.presheaf.germ_res_apply (homOfLE hle) x hxW f
  rw [← e] at ha ⊢
  generalize X.presheaf.map (homOfLE hle).op f = g at ha ⊢
  have hu : ¬ IsUnit (X.presheaf.germ W x hxW g) :=
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 ha)
  have hm := mem_vanishingIdeal_closure x ⟨W, hW⟩ hxW g hu
  have h1 : Ideal.map (X.presheaf.germ W x hxW).hom
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal ⟨W, hW⟩) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x :=
    le_iSup₂_of_le (f := fun (U : X.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (X.presheaf.germ U.1 x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U)) ⟨W, hW⟩ hxW le_rfl
  exact h1 (Ideal.mem_map_of_mem _ hm)

theorem coheight_eq_one_of_lSncAt {X : Scheme.{0}} {r : ℕ} (z : Fin r → X) (a : Fin r)
    (h : FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) (z a)) : Order.coheight (z a) = 1 := by
  obtain ⟨hreg, n, t, e, ht, hI⟩ := h
  have ha : z a ∈ (Closeds.closure {z a} : Closeds X) := subset_closure (Set.mem_singleton _)
  have hn : 1 ≤ n := (e ⟨a, ha⟩).pos
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) = Ideal.span {t (e ⟨a, ha⟩)} := by
    refine le_antisymm ((maximalIdeal_le_stalkId (z a)).trans (hI ⟨a, ha⟩).le) ?_
    rw [← ht.1]
    exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) ∈
      (Ideal.span {t (e ⟨a, ha⟩)}).minimalPrimes := by
    rw [← hm, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk (z a))
  have h2 := ringKrullDim_stalk_eq_coheight (z a)
  have h3 : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z a))).height = Order.coheight (z a) :=
    WithBot.coe_eq_coe.1 (h1.trans h2)
  have h4 : ((n : ℕ∞)) = Order.coheight (z a) := WithBot.coe_eq_coe.1 (ht.2.trans h2)
  refine le_antisymm (h3 ▸ hle) ?_
  rw [← h4]
  exact_mod_cast hn

theorem exists_genericPoints : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  intro F _ X _ p D hp hs T hT
  haveI : QuasiCompact p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    infer_instance
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨m, C, hC, -⟩ := GlobalTheory.SncComponents.exists_compList_effCartier F X p D T hT
  have hL := GlobalTheory.SncLocal.lSncAt_of_snc' X T m C hT hC
  have hz : ∀ a, ∃ z : X, closure {z} = (C a : Set X) := fun a =>
    QuasiSober.sober (hC.1 a) (C a).isClosed
  choose z hz using hz
  have hCz : (fun a => (Closeds.closure {z a} : Closeds X)) = C :=
    funext fun a => SetLike.coe_injective (hz a)
  have hL' : ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
    rw [hCz]; exact hL
  have hco : ∀ a, Order.coheight (z a) = 1 := fun a => coheight_eq_one_of_lSncAt z a (hL' _)
  have hU : (T : Set X) = ⋃ a, closure {z a} := by
    rw [← hC.2.1]; simp only [hz]
  refine ⟨m, z, fun a b hab => hC.2.2 a b ?_, hco, hU, fun w hw hw1 => ?_, hL'⟩
  · rw [← hz, ← hz, hab]
  · have hw' : w ∈ (T : Set X) := hw
    rw [hU] at hw'
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hw'
    have hsp : z a ⤳ w := specializes_iff_mem_closure.2 ha
    refine ⟨a, ?_⟩
    by_contra hne
    have hlt : w < z a := lt_of_le_not_ge hsp fun h =>
      hne ((show w ⤳ z a from h).antisymm hsp).eq
    have := Order.coheight_strictAnti hlt (by rw [hco a]; exact ENat.natCast_lt_top 1)
    rw [hco a, hw1] at this
    exact lt_irrefl _ this

end GlobalTheory.SncGenericPoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePointsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  first | exact @GlobalTheory.SncGenericPoints.exists_genericPoints | exact GlobalTheory.SncGenericPoints.exists_genericPoints | (intros; apply GlobalTheory.SncGenericPoints.exists_genericPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjective
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.PLSnc

theorem int_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Mix.int L (fun y => f y / 2) = Mix.int L f / 2 := by
  simp only [Mix.int, integral_div, sub_div]

theorem finsum_mult {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {B : LB X} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) {r : ℕ} {z : Fin r → X} (hz : Function.Injective z)
    (h : ∀ w : X, w ∉ nonzeroLocus s → Order.coheight w = 1 → ∃ a, w = z a) (g : X → ℝ) :
    ∑ᶠ w, ((divOfSec hB s hs).mult w : ℝ) * g w =
      ∑ a, ((((divOfSec hB s hs).mult (z a)).toNat : ℕ) : ℝ) * g (z a) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image z), Finset.sum_image fun a _ b _ e => hz e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (mult_divOfSec_nonneg _)]
  · intro w hw
    have h0 : (divOfSec hB s hs).mult w ≠ 0 := fun e => hw (by simp [e])
    obtain ⟨a, rfl⟩ := h w (fun e => notMem_supp_divOfSec.2 e (CartierDiv.mem_supp_of_mult_ne_zero h0))
      (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    simp

theorem poincareLelong_snc : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro F _ X _ _ p σ e hp hsm L M s hs hsnc u hu
  haveI : CharZero F := σ.charZero
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  let R := AnRead.all p σ (e + 1)
  have hA := R.isAlgAtlas_finAtlas
  generalize R.finAtlas = A at hA
  obtain ⟨r, z, hinj, hco, hT, hall, hl⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F X p (e + 1) hp hsm _ hsnc
  have hS := GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section F X p σ (e + 1) hp hsm A hA M s hs r z hinj hco hT hl
  choose B hB hBint using fun a => GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme F X (clos (z a)) p _ σ hp (closι (z a)) rfl e A hA
    (GlobalTheory.T.smooth_snc_component_closure_charZero F X p e hp hsm r z hl a)
  have pot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth R).1 N.cInf).isPotential hA
  have hv (y) : CInfAt (fun y => u y / 2) y :=
    ((hu y).const_mul (1 / 2)).congr (.of_forall fun z => by ring)
  have hvc : Continuous fun y => u y / 2 := continuous_iff_continuousAt.2 fun y => (hv y).continuousAt
  have key := poincareLelong A M.φ.locPot _ _ _ B (pot M)
    (M.φ.isSection_of_isAlgAtlas hA (R.secVal_mem_holSec s)) hS hB (fun y => u y / 2)
    ((hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y))
    (fun i => (L i).φ.locPot) fun i => pot _
  have e₁ : logNormSec M.φ.locPot (M.φ.locSec (secVal p σ s)) = M.logSec s := funext fun y => by
    rw [Weight.logNormSec_locSec, MLine.logSec]; ring
  have e₂ : Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      mInt A (Fin.cons (LocPot.ofFun fun y => u y / 2) fun i => (L i).φ.locPot) (M.logSec s) := by
    rw [(GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA _ _ (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1).2
      (GlobalTheory.T.integrable_logNormSection_mixedChernForms F X p σ _ hp hsm _ M s hs)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Weight.sameForm_ofFun A u
    · exact SameForm.refl _ _
  have e₃ : Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (fun y => u y / 2) =
      mInt A (Fin.cons M.φ.locPot fun i => (L i).φ.locPot) fun y => u y / 2 := by
    have h := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA (Fin.cons M L : Fin (e + 1) → MLine p σ) _ hvc.measurable
    rw [h.2 (h.1.2 (mIntegrableCont A _ (fun i => pot _) _ hvc))]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  have e₄ (a) : mInt (B a) (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val)
      ((fun y => u y / 2) ∘ Subtype.val) = cycInt L u (z a) / 2 :=
    (hBint a L _ hvc).trans (int_half _ _)
  rw [e₁, ← e₂, ← e₃, int_half] at key
  simp only [e₄] at key
  rw [key, finsum_mult M.φ.isLB s hs hinj (fun w hw => hall w hw), mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

end GlobalTheory.Mix.PLSnc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.Mix.PLSnc.poincareLelong_snc | exact GlobalTheory.Mix.PLSnc.poincareLelong_snc | (intros; apply GlobalTheory.Mix.PLSnc.poincareLelong_snc <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartAtSiegelBlowupPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowup
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped TensorProduct

namespace GlobalTheory.BlowSmooth

theorem formallySmooth_of_regular_fibre {A B : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsLocalRing B] (σ : A →+* B) [IsLocalHom σ] [PerfectField (ResidueField A)] (hf : σ.Flat) (he : σ.EssFiniteType)
    (hr : IsRegularLocalRing (B ⧸ (maximalIdeal A).map σ)) : σ.FormallySmooth := by
  algebraize [σ]
  have : IsLocalHom (algebraMap A B) := ‹_›
  let e : (B ⧸ (maximalIdeal A).map σ) ≃+* ResidueField A ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ maximalIdeal A)).toRingEquiv
  have : IsRegularLocalRing (ResidueField A ⊗[A] B) := .of_ringEquiv e
  have : Algebra.FormallySmooth (ResidueField A) (ResidueField A ⊗[A] B) :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _
  have : Algebra.FinitePresentation A (Algebra.EssFiniteType.subalgebra A B) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := A) (S := B)
    (Algebra.EssFiniteType.submonoid A B)

theorem isRegularLocalRing_quotient_of_flat {B R : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
    [IsLocalRing R] (φ : B →+* R) (hf : φ.Flat) (hm : (maximalIdeal B).map φ = maximalIdeal R) (I : Ideal B) (hI : I ≠ ⊤)
    (hr : IsRegularLocalRing (R ⧸ I.map φ)) : IsRegularLocalRing (B ⧸ I) := by
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let χ : (B ⧸ I) →+* (R ⧸ I.map φ) := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map
  have hcomm : (Ideal.Quotient.mk (I.map φ)).comp φ = χ.comp (Ideal.Quotient.mk I) := by
    ext a; simp [χ]
  refine (GlobalTheory.RegSmooth.isRegularLocalRing_of_flat_of_map_maximalIdeal' χ (GlobalTheory.Pat.flat_quotientMap_map φ hf I) ?_).1
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map φ)) Ideal.Quotient.mk_surjective, ← hm,
    ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
    Ideal.map_map, hcomm]

theorem perfectField_residueField {o : Type} [CommRing o] [IsDedekindDomain o] [CharZero o] [Algebra.FiniteType ℤ o]
    (q : Ideal o) [q.IsPrime] : PerfectField q.ResidueField := by
  obtain ⟨p, hp⟩ := CharP.exists q.ResidueField
  rcases CharP.char_is_prime_or_zero q.ResidueField p with h | rfl
  · have : Fact p.Prime := ⟨h⟩
    have hq : q ≠ ⊥ := by
      rintro rfl
      have h1 : algebraMap o (⊥ : Ideal o).ResidueField (p : o) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero _ p
      rw [Ideal.algebraMap_residueField_eq_zero, Ideal.mem_bot] at h1
      exact h.ne_zero (Nat.cast_eq_zero.1 h1)
    have : q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq
    have : Algebra.FiniteType ℤ q.ResidueField :=
      Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom ℤ o q.ResidueField)
        (Ideal.algebraMap_residueField_surjective q)
    let _ : Algebra (ZMod p) q.ResidueField := ZMod.algebra _ p
    have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := q.ResidueField) (RingHom.ext_int _ _)
    have : Algebra.FiniteType (ZMod p) q.ResidueField := .of_restrictScalars_finiteType ℤ _ _
    have : Module.Finite (ZMod p) q.ResidueField := finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.perfectField (ZMod p)
  · have : CharZero q.ResidueField := CharP.charP_to_charZero _
    infer_instance


set_option backward.isDefEq.respectTransparency false in
theorem formallySmooth_stalkMap {o : Type} [CommRing o] [IsDedekindDomain o] {S : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (hp : ∀ (q : Ideal o) [q.IsPrime], PerfectField q.ResidueField) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hξ : ξ ≫ s = spMap b) (hb : Function.Injective b)
    (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (hr : IsRegularLocalRing (R ⧸ ((maximalIdeal R).comap b).map b)) :
    (s.stalkMap (ξ (closedPoint R))).hom.FormallySmooth := by
  set y := ξ (closedPoint R) with hy
  let φ₀ : S.presheaf.stalk y →+* R := (Scheme.stalkClosedPointTo ξ).hom
  let σ := (s.stalkMap y).hom
  let L := Localization.AtPrime (s y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of o) (s y)
  let τ : L →+* S.presheaf.stalk y := σ.comp e.inv.hom
  let ρ : o →+* S.presheaf.stalk y := τ.comp (algebraMap o L)
  have h3 : (Sp o).fromSpecStalk (s y) = Spec.map e.inv ≫ spMap (algebraMap o L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (s y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := s y)).symm
  have hb' : b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk s (x := y)
    have key : spMap b = spMap (φ₀.comp ρ) := by
      rw [← hξ, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, τ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (s y).asIdeal = (maximalIdeal R).comap b := by
    have : s y = spMap b (closedPoint R) := by
      rw [hy, ← hξ, Scheme.Hom.comp_apply]
    rw [this]; rfl
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  have hφ : Function.Injective φ₀ := by
    have h1 : φ₀.Flat := het.1
    algebraize [φ₀]
    have : IsLocalHom (algebraMap (S.presheaf.stalk y) R) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo ξ).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := S.presheaf.stalk y) (B := R)
    exact FaithfulSMul.algebraMap_injective (S.presheaf.stalk y) R
  have : IsDomain (S.presheaf.stalk y) := hφ.isDomain φ₀
  have hρ : Function.Injective ρ := by
    rw [hb'] at hb
    exact Function.Injective.of_comp (f := φ₀) hb
  have hτ : τ.Flat := by
    algebraize [τ, ρ]
    have : FaithfulSMul o (S.presheaf.stalk y) := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ
    have : IsScalarTower o L (S.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
    exact (Module.flat_iff_of_isLocalization L (s y).asIdeal.primeCompl (S.presheaf.stalk y)).2 inferInstance
  have hess : τ.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.FiniteType.of_surjective _ e.commRingCatIsoToRingEquiv.symm.surjective).essFiniteType
      (LocallyOfFiniteType.stalkMap s y)
  have : IsLocalHom e.inv.hom := isLocalHom_of_isIso e.inv
  have : IsLocalHom τ := RingHom.isLocalHom_comp _ _
  have : PerfectField (ResidueField L) := hp (s y).asIdeal
  have hI : ((maximalIdeal L).map τ).map φ₀ = ((maximalIdeal R).comap b).map b := by
    rw [← hq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hb']
  have hne : (maximalIdeal L).map τ ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap τ).ge)
  have hreg := isRegularLocalRing_quotient_of_flat φ₀ het.1 het.2.1 _ hne (hI ▸ hr)
  have hs := formallySmooth_of_regular_fibre τ hτ hess hreg
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso e.inv (s.stalkMap y)).1 hs

theorem smoothOfRelativeDimension_of_dense {U X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (n : ℕ) (hn : SmoothOfRelativeDimension n (j ≫ f)) : SmoothOfRelativeDimension n f := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose r W hW hr using H1.exists_dim f
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  obtain ⟨_, hu, u, rfl⟩ := hj.inter_open_nonempty _ (W x).2 ⟨x, hW x⟩
  have h₁ : SmoothOfRelativeDimension (0 + r x) ((j ∣_ W x) ≫ (W x).ι ≫ f) := have := hr x; inferInstance
  have h₂ : SmoothOfRelativeDimension (0 + n) ((j ⁻¹ᵁ W x).ι ≫ j ≫ f) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
  have e := H1.dim_unique _ h₁ h₂ ⟨u, hu⟩
  rw [zero_add, zero_add] at e
  exact e ▸ hr x

theorem smoothOfRelativeDimension_blowup : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow
  have hiz : i ≫ z = F.s := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, h, -⟩, -⟩ := hmin
    exact h
  obtain ⟨hproj, hdense, hji⟩ : IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i := by
    obtain ⟨_, -, -, -, -, h₁, h₂, h₃, -⟩ := hblow
    exact ⟨h₁, h₂, h₃⟩
  have hjs : j ≫ π ≫ z = F.s := by rw [← Category.assoc, hji, hiz]
  have : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have : IsProper (π ≫ z) := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  have : LocallyOfFinitePresentation (π ≫ z) := inferInstance
  have : Smooth (π ≫ z) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
    rintro x -
    obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, rfl⟩ :=
      GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
    have : IsCommMonObj G₁ := hfam.1.comm
    obtain ⟨het, -⟩ :=
      GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap GlobalTheory.T.chartSeparation_data_defined_over_centre_field g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
    obtain ⟨-, -, hinj, -, -, hreg⟩ := TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
    have hξ : ξ ≫ π ≫ z = spMap C.b := by
      have h1 : jK C.R ≫ ξ ≫ π ≫ z = jK C.R ≫ spMap C.b := by
        rw [← Category.assoc, ← hy, Category.assoc, hjs, hfam.2.2.2.2]
      obtain ⟨c, hc⟩ := Spec.map_surjective (ξ ≫ π ≫ z)
      rw [← hc, jK, spMap, ← Spec.map_comp, ← Spec.map_comp] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      rw [← hc, spMap]
      congr 1
      ext a
      exact IsFractionRing.injective C.R (FractionRing C.R) (congr($h2 a))
    exact formallySmooth_stalkMap (π ≫ z) (fun q _ => perfectField_residueField q) C.b ξ hξ hinj het hreg
  exact smoothOfRelativeDimension_of_dense (π ≫ z) j hdense _ (hjs ▸ F.smooth)

end GlobalTheory.BlowSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowupStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_blowAt_comp : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) := by
  first | exact @GlobalTheory.BlowSmooth.smoothOfRelativeDimension_blowup | exact GlobalTheory.BlowSmooth.smoothOfRelativeDimension_blowup | (intros; apply GlobalTheory.BlowSmooth.smoothOfRelativeDimension_blowup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.GoodVal

theorem GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  intro g n F S j _ R _ _ _ ξ G₁ _ _ y A₁ _ i₁ β hG hA hB hy p hp
  have : IsNoetherianRing R := inferInstance
  let K := FractionRing R
  by_cases hp0 : p.asIdeal = ⊥
  · have hAprop : IsProper A₁.hom := MorphismProperty.of_isPullback (P := @IsProper) hB.1 F.univ.ab.proper
    refine abLocusOne _ G₁ hG K (jK R) (by rw [← hA.1.isoPullback_inv_snd]; infer_instance) ⟨(⊥ : PrimeSpectrum K), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = p.asIdeal
    rw [hp0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · have := p.isPrime
    obtain ⟨T, hT, gT, hg, hgp⟩ := exists_dvr_centre (K := K) (L := K) p.asIdeal hp0
    have hc : spMap (algebraMap T K) ≫ spMap gT = jK R := by
      rw [← spMap_comp, hg]
    have hginj : Function.Injective gT := by
      refine Function.Injective.of_comp (f := algebraMap T K) ?_
      rw [← RingHom.coe_comp, hg]
      exact (algebraMap K K).injective.comp (IsFractionRing.injective R K)
    have hcl : spMap gT (IsLocalRing.closedPoint T) = p := PrimeSpectrum.ext hgp
    have hr : Set.range (spMap gT ≫ ξ) ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      by_cases hq : q.asIdeal = ⊥
      · have hq' : q = spMap (algebraMap T K) (⊥ : PrimeSpectrum K) := by
          apply PrimeSpectrum.ext
          change q.asIdeal = Ideal.comap (algebraMap T K) ⊥
          rw [hq]; exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective T K)).symm
        refine ⟨y (⊥ : PrimeSpectrum K), ?_⟩
        rw [hq']
        have e : spMap (algebraMap T K) ≫ spMap gT ≫ ξ = y ≫ j := by rw [hy, ← Category.assoc, hc]
        have e' := (congrArg (fun f : Sp K ⟶ S => f (⊥ : PrimeSpectrum K)) e).symm
        first | exact e' | (dsimp only at e'; rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e'; exact e')
      · have hq' : q = IsLocalRing.closedPoint T :=
          PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime))
        rw [hq']
        have e : (spMap gT ≫ ξ) (IsLocalRing.closedPoint T) = ξ p := by rw [← hcl]; rfl
        rw [e]; exact hp
    haveI := hT
    let yT : Sp T ⟶ F.X := IsOpenImmersion.lift j (spMap gT ≫ ξ) hr
    have hyT : yT ≫ j = spMap gT ≫ ξ := IsOpenImmersion.lift_fac _ _ _
    have hyK : spMap (algebraMap T K) ≫ yT = y := by
      rw [← cancel_mono j, Category.assoc, hyT, ← Category.assoc, hc, hy]
    have hid : IsPullback (𝟙 F.univ.A.left) F.univ.A.hom F.univ.A.hom (𝟙 F.X) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    have := F.univ.ab.smooth
    have := F.univ.ab.proper
    have := F.univ.ab.geomConnected
    obtain ⟨hBs, hB'⟩ := isSemiAbelian_pullback_of_range_subset F.univ.A hid yT (by
      rintro _ ⟨x, rfl⟩; exact ⟨yT x, rfl⟩)
    have hH := IsSemiAbelian.pullback (spMap gT) G₁ hG
    have hPB := ((isGrpPullback_pullback ((Over.pullback yT).obj F.univ.A) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback F.univ.A yT)).congr hyK rfl
    obtain ⟨a, ha, -⟩ := grpPullback_iso hPB hB
    have hPG := ((isGrpPullback_pullback ((Over.pullback (spMap gT)).obj G₁) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback G₁ (spMap gT))).congr hc rfl
    obtain ⟨b, hb, -⟩ := grpPullback_iso hA hPG
    have hE : IsMonHom (a ≪≫ b).hom := inferInstanceAs (IsMonHom (a.hom ≫ b.hom))
    obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hBs hH (a ≪≫ b).hom hE
    obtain ⟨Ψ, ⟨-, hΨ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hH hBs (a ≪≫ b).inv inferInstance
    have hx := (abLocus_pullback abLocusOne hG (isGrpPullback_pullback G₁ (spMap gT)).1
      (IsLocalRing.closedPoint T)).2 (abLocus_subset_of_extends hBs hH _ Φ Ψ hΦ hΨ (hB' _))
    rw [hcl] at hx
    exact hx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  first | exact @GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | exact GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | (intros; apply GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdEqChart

theorem boundary_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → ∀ (m : ℕ) (t : Fin m → R), IsRelParam b t → (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ k, t k ∉ p.asIdeal) → (∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ k, t k} := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy hrad m t ht hab
  have key : ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal := fun p =>
    ⟨fun h => (hab p).1 (GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart g n F S j R ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p h),
     fun h => GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion g n F S j R b ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p ((hab p).2 h)⟩
  refine ⟨key, GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span S j.opensRange R ξ _ (GlobalTheory.T.isRadical_span_prod_relativeRegularParameters _ R b m t ht) (fun p => ?_) hrad⟩
  rw [Scheme.Hom.coe_opensRange]
  exact key p

end GlobalTheory.BdEqChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletion
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartPre

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem eq_of_jK_comp_eq {R o : Type} [CommRing R] [IsDomain R] [CommRing o] {u v : Sp R ⟶ Sp o}
    (h : jK R ≫ u = jK R ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  have h' : u ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = v ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  congr 1
  ext a
  exact IsFractionRing.injective R (FractionRing R) (congrArg (fun f => f.hom a) h')

theorem preChart_of_isEtaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  intro g hg φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy het hfu
  obtain ⟨J, -, -, -, -, hP, -, hji, -, -, hval⟩ := hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hM
  obtain ⟨hsa, hab, hgen, hmum, hbase⟩ := hF
  obtain ⟨hreg, hch, -, -, hrel, -⟩ := GlobalTheory.TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, -⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  haveI : IsProper (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : S.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ z)]
    infer_instance⟩
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hc : IsAdicComplete (maximalIdeal C.R) C.R := C.compl.2.1
  have hξ : ξ ≫ π ≫ z = spMap C.b := eq_of_jK_comp_eq (by
    rw [← hbase, ← Category.assoc, ← hy, Category.assoc, ← Category.assoc j, hji, hiz])
  have hrad := GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ (Scheme.stalkClosedPointTo ξ).hom hc het hfu
  obtain ⟨hb₁, hb₂⟩ := GlobalTheory.BdEqChart.boundary_eq g n F S j C.R C.b ξ G₁ y ((Over.pullback (jK C.R)).obj G₁)
    (pullback.fst G₁.hom (jK C.R)) α₁ hsa (isGrpPullback_pullback G₁ (jK C.R)) hgen hy hrad C.m C.t hrel hab
  haveI : Module.Free ℤ C.Q.X := Module.Free.of_equiv C.e.toIntLinearEquiv.symm
  have hnat : ∀ k, ∃ c : ℕ, φ.evalZ ((n : ℤ) • C.δ k) = c := fun k =>
    (hφ C.Q.X hrk).exists_nat (Submodule.smul_mem _ _ (hcone.mem k)) fun w =>
      mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
  choose c hcn using hnat
  have ha : ∀ k, ((d * c k : ℕ) : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := fun k => by rw [hcn, Nat.cast_mul]
  have hBD := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F S j φ hφ d BD.idealSheaf hval C.R hc C.b ξ C.Q G₁ y α₁ hsa hgen
    hy.symm hmum C.m C.t C.δ (fun k => d * c k) hrel hab hcone hdef hmono ha
  exact ⟨C.R, inferInstance, hreg, inferInstance, C.b, ξ, C.m, C.t, C.Q, C.δ, fun k => d * c k, G₁, inferInstance, y, α₁,
    ⟨hc, hch, hξ, rfl, het, hfu⟩, ⟨hrel, hb₂, hb₁⟩, ⟨hsa, hab, hy, hgen⟩, ⟨hmum, hrk, hcone, hdef, hmono⟩, ha, hBD⟩

end GlobalTheory.TChartPre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preChart_of_tautologicalChart_etaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  first | exact @GlobalTheory.TChartPre.preChart_of_isEtaleCompletion | exact GlobalTheory.TChartPre.preChart_of_isEtaleCompletion | (intros; apply GlobalTheory.TChartPre.preChart_of_isEtaleCompletion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowup
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin

namespace GlobalTheory.AllChart

theorem preChart_all : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, PreChart F (π ≫ z) j φ BD d x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow x
  obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, hx⟩ :=
    GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
  have : IsCommMonObj G₁ := hfam.1.comm
  obtain ⟨het, hsep⟩ :=
    GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap GlobalTheory.T.chartSeparation_data_defined_over_centre_field g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
  have h := GlobalTheory.T.preChart_of_tautologicalChart_etaleCompletion g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy het hsep
  rwa [hx] at h

end GlobalTheory.AllChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowupStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preChart_siegel_normalizedBlowup : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, PreChart F (π ≫ z) j φ BD d x := by
  first | exact @GlobalTheory.AllChart.preChart_all | exact GlobalTheory.AllChart.preChart_all | (intros; apply GlobalTheory.AllChart.preChart_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalBlowupSmoothWithSemiAbelianCharts
namespace GlobalTheory.SiegJoin

theorem chartSt5_holds : ChartSt5 :=
  fun g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j _ BD hM hB =>
    ⟨GlobalTheory.T.smoothOfRelativeDimension_blowAt_comp g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB,
      GlobalTheory.T.exists_preChart_siegel_normalizedBlowup g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB⟩

end GlobalTheory.SiegJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalBlowupSmoothWithSemiAbelianChartsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimalBlowup_smooth_with_semiAbelianCharts : GlobalTheory.SiegJoin.ChartSt5 := by
  first | exact @GlobalTheory.SiegJoin.chartSt5_holds | exact GlobalTheory.SiegJoin.chartSt5_holds | (intros; apply GlobalTheory.SiegJoin.chartSt5_holds <;> assumption)
end

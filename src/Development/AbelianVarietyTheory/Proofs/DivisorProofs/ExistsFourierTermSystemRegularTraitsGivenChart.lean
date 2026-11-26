module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMembersClassSumsDeeperLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupLevelCoverEveryPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleCoverChartAtFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleCoverChartAtFieldPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.ChartAt

theorem mem_genericPoints_of_forall_specializes {X : Scheme.{0}} (ε : X) (h : ∀ z, z ⤳ ε → z = ε) :
    ε ∈ genericPoints X := by
  have hc : irreducibleComponent ε ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents ε
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := ε)) isClosed_irreducibleComponent
  have e : ξ = ε := h ξ (hξ.specializes mem_irreducibleComponent)
  subst e
  change closure {ξ} ∈ irreducibleComponents X
  rw [hξ.def]
  exact hc

theorem forall_specializes_of_flat {X Y : Scheme.{0}} (g : Y ⟶ X) [Flat g] (ε : Y) (h : ∀ z, z ⤳ ε → z = ε) :
    ∀ z, z ⤳ g ε → z = g ε := by
  intro z hz
  obtain ⟨z', hz', e⟩ := Flat.generalizingMap g hz
  rw [← e, h z' hz']

theorem forall_specializes_fromSpec {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(Y, U))
    (hP : P.asIdeal ∈ minimalPrimes Γ(Y, U)) : ∀ z, z ⤳ hU.fromSpec P → z = hU.fromSpec P := by
  intro z hz
  have hr : z ∈ Set.range hU.fromSpec := hz.mem_open hU.fromSpec.isOpenEmbedding.isOpen_range ⟨P, rfl⟩
  obtain ⟨Q, rfl⟩ := hr
  have h1 : Q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 hz
  have h2 : (show PrimeSpectrum Γ(Y, U) from Q).asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h1
  have h3 := hP.2 ⟨PrimeSpectrum.isPrime Q, bot_le⟩ h2
  rw [show Q = P from PrimeSpectrum.ext (le_antisymm h2 h3)]

theorem exists_chart_at : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := by
  intro n N X Y Z sX sY q i hi hn hN hsX hsY hq he hs K _ y'
  let pt : Sp K := closedPoint (CommRingCat.of K)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q (y' pt))) isOpen_univ
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have hU : IsAffineOpen (q ⁻¹ᵁ V₀) := hV₀.preimage q
  set U := q ⁻¹ᵁ V₀ with hUdef
  have hrange : Set.range y' ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨w, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim w pt]
    exact hxV
  let χ : Γ(Y, U) →+* K := (Spec.preimage (IsOpenImmersion.lift hU.fromSpec y' hrange)).hom
  have hχ : spMap χ ≫ hU.fromSpec = y' := by
    have : spMap χ = IsOpenImmersion.lift hU.fromSpec y' hrange := Spec.map_preimage _
    rw [this, IsOpenImmersion.lift_fac]
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨P₀, hP₀, hPχ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal Γ(Y, U))) (J := RingHom.ker χ) bot_le
  obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(Y, U), P.asIdeal = P₀ := ⟨⟨P₀, hP₀.1.1⟩, rfl⟩
  have hmax := forall_specializes_fromSpec hU P hP₀
  have hgen : (sY (hU.fromSpec P)).asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY (hU.fromSpec P) := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    rw [← forall_specializes_of_flat sY _ hmax b hb]
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hsm : ψ.Smooth := by
    have : Smooth (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  haveI : Algebra.Smooth (cycAway N) Γ(Y, U) := hsm
  haveI : IsDedekindDomain (cycAway N) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N
  have hic : IsIntegrallyClosed (Γ(Y, U) ⧸ P.asIdeal) := isIntegrallyClosed_quotient_of_mem_minimalPrimes
    (fun m _ => isDomain_and_isIntegrallyClosed_atPrime_of_smooth (cycAway N) m _) hP₀
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω :=
    ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  have hsurj : Function.Surjective f.rangeRestrict.toRingHom := f.rangeRestrict_surjective
  have hkerR : RingHom.ker f.rangeRestrict.toRingHom = P.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hφker, Subtype.ext_iff]
    rfl
  let χR : f.range →+* K := RingHom.liftOfSurjective f.rangeRestrict.toRingHom hsurj ⟨χ, hkerR.le.trans hPχ⟩
  have hχR : χR.comp f.rangeRestrict.toRingHom = χ := RingHom.liftOfSurjective_comp _ _ _
  have hfin : IsFinite (spMap f.rangeRestrict.toRingHom) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_surjective _ hsurj)
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    spMap χR, i ''ᵁ V₀, spMap f.rangeRestrict.toRingHom ≫ hU.isoSpec.inv ≫ (q ∣_ V₀) ≫ (i.isoImage V₀).hom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hV₀.image_of_isOpenImmersion i, inferInstance, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · exact IsIntegrallyClosed.of_equiv
      ((Ideal.quotEquivOfEq hkerR.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj))
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · rw [← Category.assoc, ← hχ, ← hχR, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) ∈ genericPoints X
    rw [hw]
    exact mem_genericPoints_of_forall_specializes _ (forall_specializes_of_flat q _ hmax)
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    have h1 := GlobalTheory.Poinc.Chart.stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec
      (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) (fun z => by
        obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact ⟨a, c, rfl⟩) _ rfl
    have e2 : spMap f.range.val.toRingHom ≫ (spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec) ≫ q ≫ i =
        (spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) ≫ hU.fromSpec ≫ q) ≫ i := by
      rw [← e]; simp only [Category.assoc]
    rw [e2, Scheme.Hom.stalkMap_comp]
    exact h1.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  · simp only [Category.assoc]
    rw [Scheme.Hom.isoImage_hom_ι, ← Category.assoc (q ∣_ V₀), morphismRestrict_ι, Category.assoc,
      ← Category.assoc hU.isoSpec.inv, hU.isoSpec_inv_ι]

end GlobalTheory.Poinc.ChartAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleCoverChartAtFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_etale_cover_chart_at_field_point : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := by
  first | exact @GlobalTheory.Poinc.ChartAt.exists_chart_at | exact GlobalTheory.Poinc.ChartAt.exists_chart_at | (intros; apply GlobalTheory.Poinc.ChartAt.exists_chart_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteChartMapToNormalFiniteModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteChartMapToNormalFiniteModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.ModelAt

open GlobalTheory.Points GlobalTheory.ZH.RatModel

theorem isIntegral_valMap {C : Type} [CommRing C] {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    (f : Sp C ⟶ V) [IsFinite f] (h : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V) : (valMap (f ≫ V.ι) V h).hom.IsIntegral := by
  have e := specMap_valMap_fromSpec hV (f ≫ V.ι) h
  have e2 : Spec.map (valMap (f ≫ V.ι) V h) = f ≫ hV.isoSpec.hom := by
    rw [← cancel_mono hV.fromSpec, e, Category.assoc, ← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (valMap (f ≫ V.ι) V h)) := by rw [e2]; infer_instance
  exact ((IsFinite.SpecMap_iff _).1 this).to_isIntegral

theorem mem_of_isIntegralElem {o Ω A : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing A]
    (S : Subalgebra o Ω) [IsFractionRing S Ω] [IsIntegrallyClosed S] (σ : A →+* Ω) (hσ : ∀ a, σ a ∈ S) {x : Ω}
    (hx : σ.IsIntegralElem x) : x ∈ S := by
  have h1 : (algebraMap S Ω).IsIntegralElem x := by
    obtain ⟨p, hp, h0⟩ := hx
    refine ⟨p.map (σ.codRestrict S hσ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral S x from h1)
  exact hy ▸ y.2

theorem exists_map_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  intro o Ω _ _ _ M Z π hn hπ R hR hic V f hV hf hpt
  have hg : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V := fun w _ => (f w).2
  have hpV : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ V := by
    rw [hpt]
    exact fun w _ => hg (x := _) trivial
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hne : ((π ⁻¹ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨M.pt (IsLocalRing.closedPoint Ω), hpV (x := IsLocalRing.closedPoint Ω) trivial⟩
  haveI : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, c, hc, h⟩ := hR z
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, h⟩
  have hα := isIntegral_valMap hV f hg
  have hβ : (π.app V).hom.IsIntegral := (π.finite_app V hV).to_isIntegral
  have hcomm : ∀ a, M.res _ hne ((π.app V).hom a) = (((valMap (f ≫ V.ι) V hg).hom a : R) : Ω) := fun a => by
    rw [res_apply, valF_eq_valR, ← valR_comp, hpt, valR_spMap_comp _ _ _ hg, valR_eq _ _ hg]
    rfl
  have hσ : (M.res _ hne).comp (π.app V).hom = R.val.toRingHom.comp (valMap (f ≫ V.ι) V hg).hom :=
    RingHom.ext hcomm
  have h1 : ∀ c, M.res _ hne c ∈ R := fun c =>
    mem_of_isIntegralElem R ((M.res _ hne).comp (π.app V).hom) (fun a => by
      rw [RingHom.comp_apply, hcomm]; exact Subtype.prop _) (by
      obtain ⟨p, hp, h0⟩ := hβ c
      exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, h0, map_zero]⟩)
  have h2 : ∀ r : R, ∃ c, M.res _ hne c = r := fun r => by
    have : (r : Ω) ∈ M.ringOn (π ⁻¹ᵁ V : M.Z.Opens) := mem_ringOn.2 fun z hz => by
      have := isIntegrallyClosed_O hn z
      refine mem_of_isIntegralElem (M.O z) ((M.res _ hne).comp (π.app V).hom) (fun a => by
        rw [RingHom.comp_apply, res_apply]; exact valF_mem_O hz _) ?_
      obtain ⟨p, hp, h0⟩ := hα r
      refine ⟨p, hp, ?_⟩
      rw [hσ]
      exact (Polynomial.hom_eval₂ p _ R.val.toRingHom r).symm.trans (by rw [h0, map_zero])
    obtain ⟨c, hc⟩ := (mem_ringOn_iff_exists hne).1 this
    exact ⟨c, (M.res_apply _ hne c).trans hc⟩
  let ψ : Γ(M.Z, π ⁻¹ᵁ V) ⟶ CommRingCat.of R := CommRingCat.ofHom ((M.res _ hne).codRestrict R h1)
  have hφ := le_preimage_specMap_fromSpec hW ψ
  refine ⟨Spec.map ψ ≫ hW.fromSpec, ?_, fun P a b hb => ?_⟩
  · refine ext_of_valR hV hφ hg fun a => ?_
    rw [valR_comp, valR_eq _ _ hφ, valMap_specMap_fromSpec, valR_eq _ _ hg]
    exact Subtype.ext (hcomm a)
  · have hz : (Spec.map ψ ≫ hW.fromSpec) P ∈ π ⁻¹ᵁ V := hφ (x := P) trivial
    obtain ⟨a', ha'⟩ := h2 a
    obtain ⟨b', hb'⟩ := h2 b
    have hbz : (Spec.map ψ ≫ hW.fromSpec) P ∈ M.Z.basicOpen b' := by
      change Spec.map ψ P ∈ hW.fromSpec ⁻¹ᵁ M.Z.basicOpen b'
      rw [hW.fromSpec_preimage_basicOpen]
      change ψ.hom b' ∉ P.asIdeal
      rwa [show ψ.hom b' = b from Subtype.ext hb']
    have hu := ((isUnit_O_iff _).1 ((isUnit_valF_iff hz b').2 hbz)).2
    rw [← ha', ← hb', res_apply, res_apply, div_eq_mul_inv]
    exact mul_mem (valF_mem_O hz a') hu

end GlobalTheory.Poinc.ModelAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteChartMapToNormalFiniteModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_chart_map_to_normal_finite_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  first | exact @GlobalTheory.Poinc.ModelAt.exists_map_model | exact GlobalTheory.Poinc.ModelAt.exists_map_model | (intros; apply GlobalTheory.Poinc.ModelAt.exists_map_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupLevelCoverEveryPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.SetupCov
open GlobalTheory.PoincChart

theorem chartAt : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := GlobalTheory.T.exists_finite_etale_cover_chart_at_field_point

theorem modelAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := GlobalTheory.T.exists_finite_chart_map_to_normal_finite_model

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := _root_.GlobalTheory.Poinc.GDeep.big_ge g n hn B


set_option maxHeartbeats 1000000 in
theorem exists_setup_cov : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro g hg n hn ho F Z z i _ hproj hZn hiz hden W hW hT l hl hln j₀
  have hlo : Odd l := Odd.of_dvd_nat ho hln
  obtain ⟨k, j₁, hk, -, hj₁, big⟩ := exists_big_ge (8 * g) l hl.two_le 0
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n l (2 * (j₀ + j₁ + k)) F hg hn ho hl hln (by omega)
  refine ⟨j₀ + j₁ + k, F'.X, q, by omega, hqfin, hqsurj, fun K _ y' => ?_⟩
  have hl3 : 3 ≤ l := by
    have h2 := hl.two_le
    have : l ≠ 2 := fun e => by rw [e] at hlo; exact absurd hlo (by decide)
    omega
  have hk3 : 3 ≤ (l ^ (2 * (j₀ + j₁ + k))) ^ 2 :=
    le_trans (le_trans hl3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := hlo.pow.pow
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, x, yR, V, f, hRfg, hfrac, hRic, hxs, hyR, hgen, hst, hV, hf, hfV⟩ :=
    chartAt n (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2) F.X F'.X Z F.s F'.s q i inferInstance (by omega)
      (Nat.mul_pos (by omega) (pow_pos (pow_pos hl.pos _) _)) inferInstance inferInstance hqfin hqet hqsurj K y'
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) x t' hxs
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ x t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (x ≫ q) := sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q x ψ hsh' hψ hψL
  have := t.ab.comm
  have hS : ZH.HypS t.A t.L := ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩
  have hu : IsUnit (l : cycAway (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    ((dvd_pow_self l (by omega : 2 * (j₀ + j₁ + k) ≠ 0)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  haveI : NeZero ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := ⟨by have := hl.pos; positivity⟩
  obtain ⟨lev₀, -⟩ := GlobalTheory.ThetaSysOfObj.exists_level R t
  have e : (l ^ (2 * (j₀ + j₁ + k))) ^ 2 = (l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2 := by ring
  obtain ⟨lev, -⟩ : ∃ lev : Out.Level t.pol ((l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2)
      (unitOn (Units.map (algebraMap _ R).toMonoidHom b.ζ)), True := by
    rw [← e]; exact ⟨lev₀, trivial⟩
  obtain ⟨S, ρ, hR, φ, hreg, -, hNS, hrS, hgS, hpb, hL, -⟩ :=
    GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime _ Ω R hRfg hfrac (yR (IsLocalRing.closedPoint K)).asIdeal (yR (IsLocalRing.closedPoint K)).isPrime t.pol l k (2 * (j₀ + j₁))
      b.ζ hl hlo hk (by omega) hu hS lev
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hbase : spMap R.val.toRingHom ≫ x ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ) := by
    rw [hqs, ← Category.assoc x, hxs]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hp0 : (spMap R.val.toRingHom ≫ x ≫ q ≫ i) ≫ z = spMap ((algebraMap _ Ω).comp κ) := by
    simp only [Category.assoc, hiz]
    exact hbase
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) _ Ω κ ((IsFinite.SpecMap_iff _).1 hfin) Z z
    inferInstance inferInstance inferInstance _ hp0 hst
  obtain ⟨φM, hφπ, hφreg⟩ := modelAt _ Ω M Z π hMn hπ R hfrac hRic V f hV hf (by rw [hcomp, hfV])
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hsharp : SharpOver F W ρ.P (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) :=
    sharpOver_pullback _ _ _ _ F W _ _ t.pol ρ.P (x ≫ q) _ φ hsh hpb hL
  refine ⟨Setup.mk _ Ω S ρ (big (2 * (j₀ + j₁)) (by omega) _ Ω S (hgS.trans ?_) hNS hrS)
    (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) hsharp
    (fun w => by rw [← Category.assoc, ef]; exact hgen w) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ
    (by rw [hcomp]; simp only [Category.assoc]; rw [← Category.assoc (spMap S.R.val.toRingHom), ef]) hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) inferInstance hiz hden
    hW hT κ (by rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]; exact hbase),
    yR ≫ φM, ?_, ?_, ?_⟩
  · rfl
  · show S.r * S.N = _
    rw [hrS, hNS]; ring
  · show (yR ≫ φM) ≫ π = _
    rw [Category.assoc, hφπ, hfV, ← Category.assoc, hyR]
  · intro a ha
    change a ∈ S.R at ha
    obtain ⟨a', b', hb', e⟩ := hreg a ha
    change a ∈ M.O ((yR ≫ φM) (IsLocalRing.closedPoint K))
    rw [e]
    exact hφreg _ a' b' hb'

end GlobalTheory.Poinc.SetupCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupLevelCoverEveryPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSetup_levelCover_every_point : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.Poinc.SetupCov.exists_setup_cov | exact GlobalTheory.Poinc.SetupCov.exists_setup_cov | (intros; apply GlobalTheory.Poinc.SetupCov.exists_setup_cov <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinedDegenerationDataFiniteExtensionLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedPullbackInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedPullbackInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.RefPull

open GlobalTheory.HalfBC

theorem refines_pull : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  intro V V₀ V₁ _ _ _ _ _ _ Q ρ₀ D₀ e₀ hρ₀ H ρ D₁ hD hρ
  obtain ⟨β₀, β₂₀, w₀, pb₀, sq₀, gen₀, c₀, tau₀⟩ := H
  have gp := pull_grp hD
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  have hΛ₁ : (abelian₂ D₁.P.A D₁.P.L).IsLB := DVR.linComb_isLB _ D₁.P.isLB _ _
  obtain ⟨w', T⟩ := exists_comp hΛ₀ w₀ (lamIso gp hD.w) ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen)) hΛQ hΛ₁
  set β : D₁.P.A.left ⟶ D₀.P.A.left := hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf ρ) with hβ
  let gam : FractionRing V₀ →+* FractionRing V₁ := GlobalTheory.ArcPull.fracMap hρ
  have hgam : ∀ r, gam (algebraMap V₀ _ r) = algebraMap V₁ _ (ρ r) := GlobalTheory.ArcPull.fracMap_algebraMap hρ
  have sgam := gam_comm ρ gam hgam
  obtain ⟨κ₁, hκ₁, hκu⟩ := exists_kappa ρ₀ ρ gam hgam hρ₀
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D₁.P.A).left) (z : Z) J J₁ J', Good Q.M.L z J → Good D₀.P.L z J₁ →
      Good D₁.P.L z J' → lamVal w' p z J J' = lamVal w₀ (p ≫ sqOf gp) z J J₁ *
        ∏ I, gw hD.w (p ≫ lamφ D₁.P.A I) z (J₁ ((p ≫ lamφ D₁.P.A I) ≫ β)) (J' (p ≫ lamφ D₁.P.A I)) ^ lamε I := by
    intro Z p z J J₁ J' hJ hJ₁ hJ'
    have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)) (fun I => J' (p ≫ lamφ D₁.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D₁.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw w₀ (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂₀ ≫ lamφ Q.B I))
        (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      simp only [Category.assoc]
    · rw [gw_lamIso gp hD.w p z _ _ (fun I => by
        have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)
        rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
        exact this) (fun I => hJ' (p ≫ lamφ D₁.P.A I))]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc]
  refine ⟨β ≫ β₀, sqOf gp ≫ β₂₀, w', ?_, ⟨?_, ?_⟩, (isGen_iff _).2 (T.pgen_comp hΛ₀ ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen))), ?_, ?_⟩
  · exact (IsGrpPullback.comp gp pb₀).congr (spMap_comp_spMap' ρ₀ ρ) rfl
  · rw [Category.assoc, sq₀.1, ← Category.assoc, (isSquare_sqOf gp).1, Category.assoc]
  · rw [Category.assoc, sq₀.2, ← Category.assoc, (isSquare_sqOf gp).2, Category.assoc]
  · intro a
    show (D₁.c a).left ≫ β ≫ β₀ = spMap (ρ.comp ρ₀) ≫ (Q.c (e₀ (hD.xe a))).left
    rw [← Category.assoc, hβ, hD.c_pr, Category.assoc, c₀, ← Category.assoc, spMap_comp_spMap']
  · intro κ hκ a b z J J' hJ hJ'
    obtain rfl := hκu κ hκ
    choose J₁ hJ₀ using fun χ : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (χ z)
    have hJ₁ : Good D₀.P.L z J₁ := hJ₀
    let g₀ : (TK V₁).left ⟶ (TK V₀).left := spMap gam
    have hx : ∀ χ, D₁.xK χ ≫ β = g₀ ≫ D₀.xK (hD.xe χ) := fun χ => by
      show (jK V₁ ≫ (D₁.c χ).left) ≫ β = spMap gam ≫ jK V₀ ≫ (D₀.c (hD.xe χ)).left
      rw [Category.assoc, hβ, hD.c_pr, ← Category.assoc, ← sgam, Category.assoc]
    have hP : (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left ≫ sqOf gp =
        g₀ ≫ (lift (toUnit (TK V₀) ≫ D₀.c (hD.xe a)) (toUnit (TK V₀) ≫ D₀.c (hD.xe b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst D₀.P.A D₀.P.A).left = _ ≫ (fst D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact hx a
      · show _ ≫ (snd D₀.P.A D₀.P.A).left = _ ≫ (snd D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact hx b
    have t₁ := tau₀ κ₁ hκ₁ (hD.xe a) (hD.xe b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (D₀.tau (hD.xe a) (hD.xe b)) (g₀ ≫ 𝟙 _) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D₀.tau (hD.xe a) (hD.xe b)) (𝟙 _) (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J₁ hJ₁).2.2.1 _)
    have nQ : val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (g₀ ≫ κ₁) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) κ₁ (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κ₁ g₀ z J hJ).2.2.1 _)
    rw [Category.comp_id] at n₁
    have A := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp w₀ g₀ _ z J J₁ hJ hJ₁).symm nQ.symm))
    let h : ((TK V₁).left ⟶ D₁.P.A.left) → ((TK V₁).left.presheaf.stalk z)ˣ :=
      fun q => gw hD.w q z (J₁ (q ≫ β)) (J' q)
    have tv := GlobalTheory.ArcPull.tau_val hD g₀ (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' a b
    have K := (key _ (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
      (congrArg₂ (· * ·) (congrArg (fun q => lamVal w₀ q z J J₁) hP)
        (prod_lam (DVR.cP D₁ (TK V₁) a) (DVR.cP D₁ (TK V₁) b) h))
    have o₀ : ∀ x, h (DVR.cP D₁ (TK V₁) x).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (D₁.xK x) := fun _ => rfl
    have o₁ : h (1 : TK V₁ ⟶ D₁.P.A).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (1 : TK V₁ ⟶ D₁.P.A).left := rfl
    rw [← DVR.cPoint_add] at K
    simp only [o₀, o₁] at K
    simp only [Category.id_comp] at tv
    rw [K]
    show _ = _ * val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (spMap gam ≫ κ₁) z J
    apply Additive.ofMul.injective
    have eA := congrArg Additive.ofMul A
    have eT := congrArg Additive.ofMul tv
    simp only [ofMul_mul, ofMul_inv] at eA eT ⊢
    linear_combination (norm := abel) eA - eT

end GlobalTheory.RefPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedPullbackInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinesPolarised_pullback_injective : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  first | exact @GlobalTheory.RefPull.refines_pull | exact GlobalTheory.RefPull.refines_pull | (intros; apply GlobalTheory.RefPull.refines_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinedDegenerationDataFiniteExtensionLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.SharpExt

theorem spMap_comp_ext {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_refined_ext_lift : ∀ g n : ℕ, ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ (Y : Scheme.{0}) (q : Y ⟶ F.X), IsFinite q → Surjective q → ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X) (y : Sp (FractionRing V₁) ⟶ F.X) (y' : Sp (FractionRing V₁) ⟶ Y), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Refines Q ρ D₀.toPre e₀ ∧ y ≫ i = jK V₁ ≫ spMap ρ ≫ ξ ∧ y' ≫ q = y := by
  intro g n F Z i W hW V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hq hs
  obtain ⟨V₀, _, _, _, ρ₀, r, D₀, e₀, hCN₀, hinj₀, hfin₀, -, -, hRef₀, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised V Q m t δ hU.1 hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hpos
  obtain ⟨G', _, _, A', U', y₀, α, α₂, -, hy₀, -⟩ := hU.2 V₀ ρ₀ hCN₀ hinj₀ hfin₀ D₀ e₀ hRef₀
  obtain ⟨L, _, _, _, yL, hyL⟩ := GlobalTheory.T.exists_lift_fieldPoint_finite_surjective_after_extension (FractionRing V₀) F.X Y y₀ q hq hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN₁, hinj, hfin, hloc, hσ⟩ := GlobalTheory.T.exists_finite_local_extension_with_embedded_field_extension V₀ hCN₀ L
  haveI : IsNoetherianRing V₀ := hCN₀.1
  have hR : AdmBase V₀ (maximalIdeal V₀) := ⟨hCN₀.1, inferInstance, hCN₀.2.1, hCN₀.2.2.1⟩
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V₀ _ hR D₀
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of V₁))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of V₁))) = genericPoint (Spec (CommRingCat.of V₀)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D₁, hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg GlobalTheory.polBaseChange_holds GlobalTheory.globalFns_holds V₀ V₁ _ _ ρ
    (map_maximalIdeal_le ρ) D₀ Wo hψ hgen
  have hfr : GlobalTheory.Mum.GenDesc.fracMap ρ hinj = σ.comp (algebraMap (FractionRing V₀) L) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V₀) (RingHom.ext fun x => ?_)
    simp [GlobalTheory.Mum.GenDesc.fracMap_algebraMap, hσ]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ.comp ρ₀, D₁, hD.xe.trans e₀,
    spMap (GlobalTheory.Mum.GenDesc.fracMap ρ hinj) ≫ y₀, spMap σ ≫ yL, hCN₁, hinj.comp hinj₀, hfin.comp hfin₀,
    GlobalTheory.T.refinesPolarised_pullback_injective Q ρ₀ D₀.toPre e₀ hinj₀ hRef₀ ρ D₁.toPre hD hinj, ?_, ?_⟩
  · rw [Category.assoc, hy₀, spMap_comp_ext ρ₀ ρ]
    simp only [Category.assoc]
    rw [← Category.assoc (jK V₁) (spMap ρ), GlobalTheory.Mum.GenDesc.jK_comp_spMap ρ hinj]
    simp only [Category.assoc]
  · rw [Category.assoc, hyL, hfr, spMap_comp_ext]
    simp only [Category.assoc]

end GlobalTheory.Poinc.Sep.SharpExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinedDegenerationDataFiniteExtensionLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_degenerationData_finiteExtension_lift : ∀ g n : ℕ, ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ (Y : Scheme.{0}) (q : Y ⟶ F.X), IsFinite q → Surjective q → ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X) (y : Sp (FractionRing V₁) ⟶ F.X) (y' : Sp (FractionRing V₁) ⟶ Y), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Refines Q ρ D₀.toPre e₀ ∧ y ≫ i = jK V₁ ≫ spMap ρ ≫ ξ ∧ y' ≫ q = y := by
  first | exact @GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift | exact GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift | (intros; apply GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem exists_setup_regAt_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ev ∧ RegAt X₁ z₁ ev ∧ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧ Refines Q ρ D₀.toPre e₀ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU l hl hln j₀
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := GlobalTheory.T.exists_thetaSetup_levelCover_every_point g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth l hl hln j₀
  obtain ⟨V₁, _, _, _, ρ, D₀, e₀, y, y', hcn, hinj, hfin, href, hy, hy'⟩ :=
    GlobalTheory.T.exists_refined_degenerationData_finiteExtension_lift g n F Z i W hW V Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hqf hqs
  obtain ⟨X₁, yM, hrN, hyM, hreg⟩ := hB (FractionRing V₁) y'
  obtain ⟨z₁, ev, hloc, he1, he2⟩ := GlobalTheory.T.exists_stalk_lift_finite_cover_normal_local V₁ hcn.2.1 X₁.M.Z Z X₁.π X₁.fin (spMap ρ ≫ ξ) yM
    (by rw [hyM, ← Category.assoc, hy', hy])
  refine ⟨j, X₁, z₁, V₁, inferInstance, inferInstance, inferInstance, ρ, ev, D₀, e₀, hj, hrN, hcn, hinj, hfin, hloc, ?_, he1,
    href⟩
  intro a ha
  rw [he2]
  exact hreg a ha

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSetup_primePowerLevel_regular_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ev ∧ RegAt X₁ z₁ ev ∧ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧ Refines Q ρ D₀.toPre e₀ := by
  first | exact @GlobalTheory.Poinc.Sep.exists_setup_regAt_chart | exact GlobalTheory.Poinc.Sep.exists_setup_regAt_chart | (intros; apply GlobalTheory.Poinc.Sep.exists_setup_regAt_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.Sep.exists_isAct : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  intro g n F W Z i X₁
  obtain ⟨c, hc, pr, h1, h2, h3⟩ := X₁.sharp
  choose act hact using fun a : Matrix (Fin 8) (Fin 8) ℤ =>
    (h2 X₁.ρ.P.A fun u => (List.ofFn fun v => pr v ^ a u v).prod).exists
  exact ⟨act, c, hc, pr, h1, h2, h3, hact⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificatiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighthPowerMatrixAction_thetaCompactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  exact @GlobalTheory.Poinc.Sep.exists_isAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.Poinc.Sep.nonempty_uMem_trait {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (hZ : IsNormalScheme Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (hact : IsAct X₁ act)
    (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V) (h₁ : IsLocalHom ev) (h₂ : RegAt X₁ z₁ ev)
    (h₃ : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i) :
    Nonempty (UMem X₁ z₁ act T.V ev T.D.toPre.X ![T.ϖ] ![T.β]) := by
  haveI := X₁.imm
  obtain ⟨hτ, h0, -, -⟩ := GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T
  have hcn : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj hZ X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8
    X₁.thetaInt X₁ z₁ act hact T.V (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β]
    (fun k => by rw [Subsingleton.elim k 0]; exact T.irr.ne_zero)
    (fun k => by rw [Subsingleton.elim k 0]; exact T.symm)
    (fun k => by rw [Subsingleton.elim k 0]; exact h0) hτ T.V (RingHom.id _) hcn Function.injective_id
    (RingHom.Finite.id _) T.D (AddEquiv.refl _) (GlobalTheory.PolDeg.Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb ev h₁ h₂ h₃
  exact ⟨𝔪⟩

theorem _root_.GlobalTheory.Poinc.Sep.exists_vPre_traits_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) (c₀ : Φ.Q), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ ∧ IsChartMemberP X₁ z₁ Φ ((l ^ j) ^ 2) Q ξ t δ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((l ^ j) ^ 2) ∧ Φ.ClassSums ((l ^ j) ^ 2) := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsymm hnn hpos hτ ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, V₁, _, _, _, ρ, ev, D₀, e₀, hj, hN, hcn, hinj, hfin, hloc, hreg, hcomp, href⟩ :=
    GlobalTheory.T.exists_thetaSetup_primePowerLevel_regular_chart g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsymm hnn hpos hτ ξ hξ l hl hln j₀
  have hdom := (GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁).1
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_eighthPowerMatrixAction_thetaCompactification g n F W Z i X₁
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  obtain ⟨G₀, _, _, A₀, U₀, y₀, α, α₂, hsemi, hy₀, hcart, hsq, hlb⟩ := hξ.2 V₁ ρ hcn hinj hfin D₀ e₀ href
  obtain ⟨𝔪₀, hsharp⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact V Q m t δ
    (fun k => (ht k).2) hsymm hnn hτ V₁ ρ hcn hinj hfin D₀ e₀ href G₀ A₀ U₀ y₀ α α₂ hsemi hcart hsq hlb ev hloc hreg
    (by rw [hcomp, hy₀])
  have hζ : IsUnit (zetaAway n) := by
    rw [← cycBase_ζ (show n ≠ 0 by omega)]
    exact Units.isUnit _
  have hρ : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V V₁ := hfin
    haveI : FaithfulSMul V V₁ := (faithfulSMul_iff_algebraMap_injective V V₁).2 hinj
    exact (inferInstance : IsLocalHom (algebraMap V V₁))
  let Tr : Type 1 := Σ T : Trait F, {e : X₁.M.Z.presheaf.stalk z₁ →+* T.V // IsLocalHom e ∧ RegAt X₁ z₁ e ∧
    jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i}
  let VV : Option Tr → Type := fun y => match y with | none => V₁ | some T => T.1.V
  letI iR : ∀ y, CommRing (VV y) := fun y => match y with
    | none => inferInstanceAs (CommRing V₁) | some T => inferInstanceAs (CommRing T.1.V)
  haveI iD : ∀ y, IsDomain (VV y) := fun y => match y with
    | none => inferInstanceAs (IsDomain V₁) | some T => inferInstanceAs (IsDomain T.1.V)
  haveI iL : ∀ y, IsLocalRing (VV y) := fun y => match y with
    | none => inferInstanceAs (IsLocalRing V₁) | some T => inferInstanceAs (IsLocalRing T.1.V)
  let EV : ∀ y, X₁.M.Z.presheaf.stalk z₁ →+* VV y := fun y => match y with | none => ev | some T => T.2.1
  let XX : Option Tr → Type := fun y => match y with | none => Q.X | some T => T.1.D.toPre.X
  letI iA : ∀ y, AddCommGroup (XX y) := fun y => match y with
    | none => inferInstanceAs (AddCommGroup Q.X) | some T => inferInstanceAs (AddCommGroup T.1.D.toPre.X)
  haveI iF : ∀ y, Module.Free ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Free ℤ Q.X) | some T => inferInstanceAs (Module.Free ℤ T.1.D.toPre.X)
  haveI iG : ∀ y, Module.Finite ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Finite ℤ Q.X) | some T => inferInstanceAs (Module.Finite ℤ T.1.D.toPre.X)
  let MM : Option Tr → ℕ := fun y => match y with | none => m | some _ => 1
  let tt : ∀ y, Fin (MM y) → VV y := fun y => match y with | none => fun k => ρ (t k) | some T => ![T.1.ϖ]
  let dd : ∀ y, Fin (MM y) → LinearMap.BilinForm ℤ (XX y) := fun y => match y with | none => δ | some T => ![T.1.β]
  let 𝔪 : ∀ y, UMem X₁ z₁ act (VV y) (EV y) (XX y) (tt y) (dd y) := fun y => match y with
    | none => 𝔪₀
    | some T => (nonempty_uMem_trait hnorm X₁ z₁ act hact T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2).some
  have hlab : Set.range (Subtype.val : X₁.S.HH X₁.M z₁ → X₁.S.Gam) = X₁.S.HH X₁.M z₁ := Subtype.range_val
  choose u hu₁ hu₂ hu₃ using fun y => GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hx₀ (VV y) (EV y) (XX y) (MM y) (tt y) (dd y)
    (𝔪 y) (X₁.S.HH X₁.M z₁) Subtype.val hlab
  let Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁) :=
    { posW := X₁.posW
      Y := Option Tr
      V := VV
      cn := fun y => (𝔪 y).cn
      ev := EV
      ev_loc := fun y => (𝔪 y).loc
      X := XX
      rank_le := fun y => match y with
        | none => hrk
        | some T => (GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T.1).2.2.2 (by omega) hζ
      m := MM
      t := tt
      t_mem := fun y => match y with
        | none => fun k => ⟨map_nonunit ρ _ (ht k).1, fun h => (ht k).2 (hinj (h.trans (map_zero ρ).symm))⟩
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact ⟨T.1.irr.not_isUnit, T.1.irr.ne_zero⟩
      δ := dd
      bal := fun y => match y with
        | none => fun k => mem_balForms_int.2 (hsymm k)
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact mem_balForms_int.2 T.1.symm
      nonneg := fun y => match y with
        | none => hnn
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact (GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T.1).2.1
      pos := fun y => match y with
        | none => hpos
        | some T => fun x hx => ⟨(0 : Fin 1), (GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T.1).2.2.1 x hx⟩
      Q := X₁.S.HH X₁.M z₁
      u := u
      u_unit := hu₂ }
  have hgeo : IsGeo X₁ z₁ act x₀ Φ Subtype.val := ⟨hx₀, hlab, fun y => ⟨𝔪 y, hu₁ y⟩⟩
  refine ⟨j, X₁, z₁, hdom, Φ, none, ρ, AddEquiv.refl _, Equiv.refl _, ⟨x₀, AddSubgroup.subset_closure hx₀⟩, hj, ?_, ?_,
    fun y => hu₃ y _ rfl, ?_, ?_, ?_⟩
  · intro T e h₁ h₂ h₃
    refine ⟨some ⟨T, e, h₁, h₂, h₃⟩, RingHom.id _, AddEquiv.refl _, rfl, inferInstanceAs (IsPrincipalIdealRing T.V),
      Function.injective_id, inferInstanceAs (IsLocalHom (RingHom.id T.V)), rfl, fun k => ?_⟩
    rw [Subsingleton.elim (α := Fin 1) k 0]
    exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hinj, hfin, hcomp, fun k => ⟨rfl, fun _ _ => rfl⟩, 𝔪₀.D.toPre, 𝔪₀.e₈, hsharp, ?_⟩
    rw [← hN]
    exact GlobalTheory.T.memberTerms_isThetaTerms_torsionFrames g n F W Z i X₁ z₁ act x₀ hx₀ V₁ ev Q.X m _ δ 𝔪₀ _ Subtype.val hlab _ (hu₁ none)
  · rintro (_ | T) h
    · rfl
    · exact absurd rfl h
  · rw [← hN]
    exact GlobalTheory.T.thetaSystem_classSums_values_of_functions g n F W Z i X₁ z₁ act x₀ Φ _ hgeo
  · rw [← hN]
    exact GlobalTheory.T.uniformisedMembers_classSums_deeper_levels g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact x₀ Φ _ hgeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) (c₀ : Φ.Q), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ ∧ IsChartMemberP X₁ z₁ Φ ((l ^ j) ^ 2) Q ξ t δ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((l ^ j) ^ 2) ∧ Φ.ClassSums ((l ^ j) ^ 2) := by
  first | exact @GlobalTheory.Poinc.Sep.exists_vPre_traits_chart | exact GlobalTheory.Poinc.Sep.exists_vPre_traits_chart | (intros; apply GlobalTheory.Poinc.Sep.exists_vPre_traits_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Poinc.Sep.exists_chartMember_traitsR : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, hdom, Φ, y, ρ, e, h, c₀, hj, hR, hC, hU, hM, hE, hCS⟩ :=
    GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln
      (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (l ^ j) ^ 2 := by
    have h2 : 2 ≤ l ^ j := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hU y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hM y₁ h₁).trans (hM y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁, z₁, (Φ.rescale v).toVSys ((l ^ j) ^ 2) hLam' hFour', y, ρ, e, h,
    le_trans (le_max_left _ _) hj, hR, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, e₈, hS, hT⟩ := hC
  refine ⟨h1, h2, h3, h4, D, e₈, hS, ?_⟩
  have h0 : Φ.term y (fun a => e.symm ((0 : Fin 8 → Q.X) a)) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun a => e.symm ((0 : Fin 8 → Q.X) a)) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((l ^ j) ^ 2) (Fin 8 → Q.X) Φ.Q e₈
    (fun mu c => Φ.term y (fun a => e.symm (mu a)) c) (v y) c₀ hT h0
  refine cast (congrArg (fun T : (Fin 8 → Q.X) → Φ.Q → Φ.V y => IsThetaTerms D ((l ^ j) ^ 2) e₈ T) ?_) this
  funext mu c
  show Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun a => e.symm (mu a)) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
  exact mul_right_comm _ _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourierTermSystem_regular_traits_given_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  first | exact @GlobalTheory.Poinc.Sep.exists_chartMember_traitsR | exact GlobalTheory.Poinc.Sep.exists_chartMember_traitsR | (intros; apply GlobalTheory.Poinc.Sep.exists_chartMember_traitsR <;> assumption)
end

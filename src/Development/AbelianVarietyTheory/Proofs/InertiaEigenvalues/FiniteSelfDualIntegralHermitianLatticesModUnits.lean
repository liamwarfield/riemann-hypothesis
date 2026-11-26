module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.NormUnits

theorem group_fg_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, CommGroup (G i)]
    (hG : ∀ i, Group.FG (G i)) : Group.FG (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose S hS using fun i => Group.fg_iff.mp (hG i)
  refine Group.fg_iff.mpr ⟨⋃ i, Pi.mulSingle i '' S i, ?_,
    Set.finite_iUnion fun i => (hS i).2.image _⟩
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_prod_mulSingle x]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hx : x i ∈ Subgroup.closure (S i) := by rw [(hS i).1]; trivial
  have h1 : Pi.mulSingle i (x i) ∈ (Subgroup.closure (S i)).map (MonoidHom.mulSingle G i) :=
    ⟨x i, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  exact Subgroup.closure_mono (fun y hy => Set.mem_iUnion.2 ⟨i, hy⟩) h1

theorem isIntegral_of_forall_quot {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [IsArtinianRing A] [IsReduced A] (x : A)
    (hx : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal x)) :
    IsIntegral O x := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum A)
  choose p hpm hp using hx
  refine ⟨∏ I, p I, monic_prod_of_monic _ _ fun I _ => hpm I, ?_⟩
  rw [← aeval_def]
  apply (IsArtinianRing.equivPi A).injective
  funext J
  rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply, map_prod, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ J) ?_
  have h2 := aeval_algHom_apply (Ideal.Quotient.mkₐ O J.asIdeal) x (p J)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h2
  rw [← h2, aeval_def]
  exact hp J

theorem units_quot_intUnits_fg : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L]
    [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) →
    ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A]
    [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  intro K hL A _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K.E A
  have := Fintype.ofFinite (MaximalSpectrum A)

  have hfg : ∀ I : MaximalSpectrum A,
      Group.FG ((A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K.E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact hL (A ⧸ I.asIdeal)
  have hP := group_fg_pi (fun I : MaximalSpectrum A =>
    (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) hfg
  let ψ : Aˣ →* ∀ I : MaximalSpectrum A, (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal) :=
    MonoidHom.pi fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hsurj : Function.Surjective ψ := by
    intro c
    choose u hu using fun I => QuotientGroup.mk'_surjective _ (c I)
    let e := IsArtinianRing.equivPi A
    refine ⟨Units.map (e.symm : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) →* A)
      (MulEquiv.piUnits.symm u), ?_⟩
    funext I
    rw [← hu I]
    change QuotientGroup.mk' _ _ = _
    congr 1
    ext
    have h3 : ∀ z : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal,
        Ideal.Quotient.mk I.asIdeal (e.symm z) = z I := fun z => by
      rw [← IsArtinianRing.equivPi_apply A (e.symm z) I]
      exact congrFun (e.apply_symm_apply z) I
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [h3]
    rfl
  have hker : ψ.ker ≤ intUnits K.O A := by
    intro t ht
    have hI : ∀ I : MaximalSpectrum A,
        Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom t ∈ intUnits K.O (A ⧸ I.asIdeal) :=
      fun I => (QuotientGroup.eq_one_iff _).mp (congrFun (MonoidHom.mem_ker.mp ht) I)
    refine ⟨NormUnits.isIntegral_of_forall_quot _ fun I => (hI I).1,
      NormUnits.isIntegral_of_forall_quot _ fun I => ?_⟩
    have := (hI I).2
    rwa [Units.coe_map_inv] at this
  haveI : Group.FG (Aˣ ⧸ ψ.ker) :=
    Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map ψ.ker (intUnits K.O A) (MonoidHom.id _) fun t ht => hker ht) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨QuotientGroup.mk y, rfl⟩

end GlobalTheory.UnitLemma.NormUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) → ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A] [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  first | exact @GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | exact GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | (intros; apply GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExt
open GlobalTheory.UnitLemma Polynomial IsDedekindDomain

noncomputable section
namespace GlobalTheory.FieldUnitsQuotFG

theorem fg_quot_ker {G S : Type} [CommGroup G] [Finite S] (φ : G →* (S → Multiplicative ℤ)) :
    Group.FG (G ⧸ φ.ker) := by
  let e : (S → ℤ) ≃+ Additive (S → Multiplicative ℤ) :=
    { toFun := fun f => Additive.ofMul (fun v => Multiplicative.ofAdd (f v))
      invFun := fun g v => Multiplicative.toAdd (Additive.toMul g v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) := Module.Finite.equiv e.toIntLinearEquiv
  have h1 : φ.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (Subgroup.toAddSubgroup φ.range)]
    exact (Submodule.fg_iff_addSubgroup_fg _).1 (IsNoetherian.noetherian _)
  haveI : Group.FG φ.range := (Group.fg_iff_subgroup_fg _).2 h1
  exact Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective

variable (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
  [FiniteDimensional K.E L]

theorem finite_spec [IsDedekindDomain (integralClosure K.O L)] :
    Finite (HeightOneSpectrum (integralClosure K.O L)) := by
  set C := integralClosure K.O L
  have hinj : Function.Injective (algebraMap K.O C) := by
    intro a b h
    have h2 : algebraMap K.O L a = algebraMap K.O L b := by
      rw [IsScalarTower.algebraMap_apply K.O C L a, h, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply K.O K.E L, IsScalarTower.algebraMap_apply K.O K.E L] at h2
    exact IsFractionRing.injective K.O K.E ((algebraMap K.E L).injective h2)
  set I := Ideal.map (algebraMap K.O C) (IsLocalRing.maximalIdeal K.O)
  have hI : I ≠ 0 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    intro h0
    have : algebraMap K.O C ϖ ∈ I :=
      Ideal.mem_map_of_mem _ (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at this
    exact hϖ.ne_zero (hinj (this.trans (map_zero _).symm))
  have hall : ∀ v : HeightOneSpectrum C, v.asIdeal ∣ I := by
    intro v
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    have hp : (v.asIdeal.comap (algebraMap K.O C)).IsPrime := Ideal.comap_isPrime _ _
    have hne : v.asIdeal.comap (algebraMap K.O C) ≠ ⊥ := by
      intro h
      exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    have hmax := hp.isMaximal hne
    rw [IsLocalRing.eq_maximalIdeal hmax]
  have := Ideal.finite_factors hI
  have huniv : (Set.univ : Set (HeightOneSpectrum C)) = {v | v.asIdeal ∣ I} := by
    ext v; simp [hall v]
  exact Set.finite_univ_iff.1 (huniv ▸ this)

def valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    Lˣ →* (HeightOneSpectrum (integralClosure K.O L) → Multiplicative ℤ) :=
  Pi.monoidHom fun v => WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) : L →* WithZero (Multiplicative ℤ)))

theorem valHom_apply [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L]
    (x : Lˣ) (v : HeightOneSpectrum (integralClosure K.O L)) :
    ((valHom K L x v : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.valuation L (x : L) := by
  show ((WithZero.unitsWithZeroEquiv (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) :
    L →* WithZero (Multiplicative ℤ)) x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

theorem ker_valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    (valHom K L).ker = intUnits K.O L := by
  ext x
  rw [MonoidHom.mem_ker]
  have key : ∀ y : L, IsIntegral K.O y ↔
      ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L y ≤ 1 := by
    intro y
    constructor
    · intro hy v
      have : y = algebraMap (integralClosure K.O L) L ⟨y, hy⟩ := rfl
      rw [this]
      exact v.valuation_le_one _
    · intro h
      obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L y h
      rw [← hc]
      exact c.2
  have h1 : valHom K L x = 1 ↔ ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L (x : L) = 1 := by
    rw [funext_iff]
    refine forall_congr' fun v => ?_
    rw [← valHom_apply, Pi.one_apply]
    constructor
    · intro h
      rw [h, WithZero.coe_one]
    · intro h
      exact WithZero.coe_injective (h.trans WithZero.coe_one.symm)
  rw [h1]
  show _ ↔ IsIntegral K.O (x : L) ∧ IsIntegral K.O ((x⁻¹ : Lˣ) : L)
  rw [key, key]
  constructor
  · intro h
    refine ⟨fun v => (h v).le, fun v => ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
  · rintro ⟨ha, hb⟩ v
    apply le_antisymm (ha v)
    have hx : v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc 1 = v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) := hx.symm
      _ ≤ v.valuation L (x : L) * 1 := by gcongr; exact hb v
      _ = v.valuation L (x : L) := mul_one _

theorem fg_units_quot : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
    [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  intro K L _ _ _ _ _
  haveI : IsDedekindDomain (integralClosure K.O L) := integralClosure.isDedekindDomain K.O K.E L
  haveI : IsFractionRing (integralClosure K.O L) L := integralClosure.isFractionRing_of_finite_extension K.E L
  haveI := finite_spec K L
  rw [← ker_valHom K L]
  exact fg_quot_ker _

end GlobalTheory.FieldUnitsQuotFG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  first | exact @GlobalTheory.FieldUnitsQuotFG.fg_units_quot | exact GlobalTheory.FieldUnitsQuotFG.fg_units_quot | (intros; apply GlobalTheory.FieldUnitsQuotFG.fg_units_quot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnits
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NormUnits

theorem fg_quot_intUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    Group.FG (B.Aˣ ⧸ intUnits K.O B.A) := fun K B hP =>
  haveI := GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP
  GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra K (GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext K) B.A (GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP)

theorem exists_finset_sq_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : Group.FG (G ⧸ N)) :
    ∃ F : Finset G, ∀ u : G, u ^ 2 ∈ N → ∃ f ∈ F, u * f⁻¹ ∈ N := by
  let M := Additive (G ⧸ N)
  haveI : AddGroup.FG M := inferInstance
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let K2 : Submodule ℤ M := LinearMap.ker (LinearMap.lsmul ℤ M 2)
  haveI : Module.Finite ℤ K2 := Module.IsNoetherian.finite ℤ K2
  haveI : Finite K2 := Module.finite_of_fg_torsion K2 (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, by
    apply Subtype.ext; have h := x.2; rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at h
    simpa using h⟩)
  let r : K2 → G := fun k => Quotient.out (Additive.toMul (k : M))
  refine ⟨(Set.finite_range r).toFinset, fun u hu => ?_⟩
  have hk : (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) ∈ K2 := by
    show (2 : ℤ) • (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) = 0
    rw [← ofMul_zpow]
    show Additive.ofMul ((QuotientGroup.mk u : G ⧸ N) ^ (2 : ℤ)) = Additive.ofMul 1
    congr 1
    rw [zpow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]; exact hu
  refine ⟨r ⟨_, hk⟩, by simp, ?_⟩
  have h1 : (QuotientGroup.mk (r ⟨_, hk⟩) : G ⧸ N) = QuotientGroup.mk u := by
    simp only [r]; exact Quotient.out_eq' _
  have := QuotientGroup.eq.mp h1.symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

theorem exists_finset_normUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ,
    (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  intro K B hP
  let N : Subgroup B.Aˣ := B.T ⊔ intUnits K.O B.A
  have hFG : Group.FG (B.Aˣ ⧸ N) :=
    haveI := fg_quot_intUnits K B hP
    Group.fg_of_surjective (f := QuotientGroup.map (intUnits K.O B.A) N (MonoidHom.id _) le_sup_right)
      (fun q => QuotientGroup.induction_on q fun x => ⟨QuotientGroup.mk x, rfl⟩)
  obtain ⟨F, hF⟩ := exists_finset_sq_mem N hFG
  refine ⟨F, fun u ⟨w, hw, hwu⟩ => ?_⟩
  let su : B.Aˣ := Units.map (B.σ : B.A →* B.A) u
  have hsu : (su : B.A) = B.σ u := rfl
  have ht : u * su⁻¹ ∈ B.T := by
    show ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A) = 1
    have h1 : B.σ ((su⁻¹ : B.Aˣ) : B.A) * u = 1 := by
      have : B.σ ((su⁻¹ : B.Aˣ) : B.A) * B.σ (su : B.A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rwa [hsu, B.σ_σ] at this
    calc ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A)
        = (B.σ ((su⁻¹ : B.Aˣ) : B.A) * u) * ((su : B.A) * ((su⁻¹ : B.Aˣ) : B.A)) := by
          simp only [Units.val_mul, map_mul]; rw [hsu]; ring
      _ = 1 := by rw [h1, Units.mul_inv, one_mul]
  have hsq : u ^ 2 ∈ N := by
    have : u ^ 2 = (u * su⁻¹) * w := by
      ext; rw [Units.val_mul, hwu, ← hsu]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul]
      calc (u : B.A) ^ 2 = (u : B.A) * u * (((su⁻¹ : B.Aˣ) : B.A) * su) := by rw [Units.inv_mul, mul_one, sq]
        _ = _ := by ring
    rw [this]; exact N.mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hw)
  obtain ⟨f, hfF, hf⟩ := hF u hsq
  obtain ⟨t, htT, z, hz, htz⟩ := Subgroup.mem_sup.mp hf
  refine ⟨f, hfF, t, htT, ?_⟩
  have : u * f⁻¹ * t⁻¹ = z := by rw [← htz, mul_comm t z, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]; exact hz

end GlobalTheory.NormUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnitsStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_cosets_integral_norm_units : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) → ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  first | exact @GlobalTheory.NormUnits.exists_finset_normUnits | exact GlobalTheory.NormUnits.exists_finset_normUnits | (intros; apply GlobalTheory.NormUnits.exists_finset_normUnits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntUnitOfMulLat
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.HullClasses

variable {K : UQ} (B : InvAlg K)

abbrev abelian₂ : Submodule K.O B.A := Subalgebra.toSubmodule (integralClosure K.O B.A)

lemma mem_mulLat {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t y : A) (L : Submodule O A) :
    y ∈ mulLat O t L ↔ ∃ z ∈ L, t * z = y := by
  simp [mulLat]

lemma mulLat_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : A) (L : Submodule O A) :
    mulLat O (s * t) L = mulLat O s (mulLat O t L) := by
  ext y; simp only [mem_mulLat]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨t * z, ⟨z, hz, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by ring⟩

lemma mulLat_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O 1 L = L := by
  ext y; simp [mem_mulLat]

lemma mulLat_le_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (r s t : A) (L : Submodule O A)
    (h : mulLat O s L ≤ mulLat O t L) : mulLat O (r * s) L ≤ mulLat O (r * t) L := by
  rw [mulLat_mul, mulLat_mul]; exact Submodule.map_mono h

lemma one_mem_Lam : (1 : B.A) ∈ abelian₂ B := by
  simp [abelian₂]

lemma mem_Lam_iff (y : B.A) : y ∈ abelian₂ B ↔ IsIntegral K.O y := by
  simp [abelian₂, mem_integralClosure_iff]

lemma mulLat_intUnit (u : B.Aˣ) (hu : u ∈ intUnits K.O B.A) : mulLat K.O (u : B.A) (abelian₂ B) = abelian₂ B := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := (mem_mulLat _ _ _).1 hy
    rw [mem_Lam_iff] at hz ⊢
    exact hu.1.mul hz
  · intro y hy
    refine (mem_mulLat _ _ _).2 ⟨((u⁻¹ : B.Aˣ) : B.A) * y, ?_, ?_⟩
    · rw [mem_Lam_iff] at hy ⊢
      exact hu.2.mul hy
    · rw [← mul_assoc, Units.mul_inv, one_mul]

lemma intUnit_of_mulLat (v : B.Aˣ) (h : mulLat K.O (v : B.A) (abelian₂ B) = abelian₂ B) : v ∈ intUnits K.O B.A := by
  have h1 : (v : B.A) ∈ abelian₂ B := by
    rw [← h]; exact (mem_mulLat _ _ _).2 ⟨1, one_mem_Lam B, mul_one _⟩
  have h2 : (1 : B.A) ∈ mulLat K.O (v : B.A) (abelian₂ B) := by rw [h]; exact one_mem_Lam B
  obtain ⟨z, hz, hvz⟩ := (mem_mulLat _ _ _).1 h2
  have hz' : ((v⁻¹ : B.Aˣ) : B.A) = z := by
    calc ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) * ((v : B.A) * z) := by rw [hvz, mul_one]
      _ = z := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [mem_Lam_iff] at h1 hz
  exact ⟨h1, hz' ▸ hz⟩

lemma isLat_mulLat (u : B.Aˣ) {L : Submodule K.O B.A} (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    ext y; simp [mulLat]
  rw [this, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y; exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp⟩

lemma sigma_algebraMap (c cb : K.O) (h : K.c (algebraMap K.O K.E c) = algebraMap K.O K.E cb) :
    B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, h, ← IsScalarTower.algebraMap_apply]

lemma key (x : B.A) (c cb : K.O) (hc : B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb) (a b : B.Aˣ)
    (h4 : ∀ y ∈ mulLat K.O (a : B.A) (abelian₂ B), ∀ z ∈ mulLat K.O (a : B.A) (abelian₂ B),
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
    (h3 : ∀ y, (∀ z ∈ mulLat K.O (b : B.A) (abelian₂ B), B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (b : B.A) (abelian₂ B)) :
    mulLat K.O (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a)) (abelian₂ B) ≤
      mulLat K.O ((b : B.A) * B.σ b) (abelian₂ B) := by
  intro y hy
  obtain ⟨l, hl, rfl⟩ := (mem_mulLat _ _ _).1 hy
  have hb : B.σ (b : B.A) * B.σ ((b⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hy' : algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a) * l * B.σ ((b⁻¹ : B.Aˣ) : B.A) ∈
      mulLat K.O (b : B.A) (abelian₂ B) := by
    apply h3
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (mem_mulLat _ _ _).1 hz
    have := h4 _ ((mem_mulLat _ _ _).2 ⟨l, hl, rfl⟩) _ ((mem_mulLat _ _ _).2 ⟨m, hm, rfl⟩)
    convert this using 1
    unfold InvAlg.herm
    congr 1
    simp only [map_mul, hc]
    linear_combination (x * algebraMap K.O B.A c * algebraMap K.O B.A cb * (a : B.A) * B.σ (a : B.A) * l *
      B.σ m) * hb
  obtain ⟨n, hn, hbn⟩ := (mem_mulLat _ _ _).1 hy'
  refine (mem_mulLat _ _ _).2 ⟨n, hn, ?_⟩
  linear_combination B.σ (b : B.A) * hbn +
    (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a) * l) * hb

end GlobalTheory.HullClasses

noncomputable section
namespace GlobalTheory.HullClasses

theorem finite_mod_T_of (K : UQ) (B : InvAlg K)
    (hPr : ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
      ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)))
    (hNu : ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A)
    (hBe : ∀ (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
      {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite)
    (x : B.A) (c : K.O) (hc0 : c ≠ 0) :
    ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  classical
  obtain ⟨cb, hcb⟩ := K.c_int c
  have hσc := sigma_algebraMap B c cb hcb
  have hcb0 : cb ≠ 0 := by
    rintro rfl
    rw [map_zero, map_eq_zero_iff _ K.c.injective] at hcb
    exact hc0 ((IsFractionRing.injective K.O K.E) (by rw [hcb, map_zero]))
  set d : K.O := c * cb with hd
  have hd0 : d ≠ 0 := mul_ne_zero hc0 hcb0
  have hdd0 : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hDu : IsUnit (algebraMap K.O B.A d) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine (IsUnit.mk0 _ ?_).map _
    rw [Ne, ← map_zero (algebraMap K.O K.E)]
    exact (IsFractionRing.injective K.O K.E).ne hd0
  set D : B.Aˣ := hDu.unit
  have hDc : (D : B.A) = algebraMap K.O B.A d := hDu.unit_spec
  let σU : B.Aˣ →* B.Aˣ := Units.map B.σ.toMonoidHom
  have hσU : ∀ a : B.Aˣ, ((σU a : B.Aˣ) : B.A) = B.σ (a : B.A) := fun a => rfl
  let Nu : B.Aˣ → B.Aˣ := fun a => a * σU a
  have hNuc : ∀ a, ((Nu a : B.Aˣ) : B.A) = (a : B.A) * B.σ (a : B.A) := fun a => by simp [Nu, hσU]
  let Λ := abelian₂ B
  let adm : B.Aˣ → Prop := fun a =>
    (∀ y, (∀ z ∈ mulLat K.O (a : B.A) Λ, B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (a : B.A) Λ) ∧
    (∀ y ∈ mulLat K.O (a : B.A) Λ, ∀ z ∈ mulLat K.O (a : B.A) Λ,
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
  by_cases hex : ∃ a₀ : B.Aˣ, IsLat K.O K.E (mulLat K.O (a₀ : B.A) Λ) ∧ adm a₀
  swap
  · refine ⟨∅, Set.finite_empty, by simp, ?_⟩
    intro J hJ hst h3 h4
    obtain ⟨a, rfl⟩ := hPr J hJ hst
    exact (hex ⟨a, hJ, h3, h4⟩).elim
  obtain ⟨a₀, hJ₀, hadm₀⟩ := hex
  have hΛ : IsLat K.O K.E Λ := by
    have := isLat_mulLat B a₀⁻¹ hJ₀
    rwa [← mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulLat_one] at this
  let Mf : B.Aˣ → Submodule K.O B.A := fun a => mulLat K.O ((D * Nu a * (Nu a₀)⁻¹ : B.Aˣ) : B.A) Λ
  let Bset := {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (d * d)) Λ ≤ M ∧ M ≤ Λ}
  have hcancel : ∀ a : B.Aˣ, mulLat K.O (((a⁻¹ : B.Aˣ) : B.A) * a) Λ = Λ := fun a => by
    rw [Units.inv_mul, mulLat_one]
  have hM : ∀ a, adm a → Mf a ∈ Bset := by
    intro a ha
    have k1 := key B x c cb hσc a a₀ ha.2 hadm₀.1
    have k2 := key B x c cb hσc a₀ a hadm₀.2 ha.1
    constructor
    · have := mulLat_le_mul (((D * (Nu a₀)⁻¹ : B.Aˣ) : B.A)) _ _ Λ k2
      convert this using 2
      · rw [map_mul, ← hDc, ← hNuc]
        simp only [Units.val_mul]
        calc (D : B.A) * D = D * D * (((Nu a₀)⁻¹ : B.Aˣ) * (Nu a₀ : B.A)) := by rw [Units.inv_mul, mul_one]
          _ = _ := by ring
      · rw [← hNuc]; simp only [Units.val_mul, Mf]; ring
    · have := mulLat_le_mul ((((Nu a₀)⁻¹ : B.Aˣ)) : B.A) _ _ Λ k1
      rw [← hNuc, ← hNuc, hcancel] at this
      convert this using 2
      simp only [Units.val_mul]; rw [hDc, hd]; ring
  let gch : Submodule K.O B.A → B.Aˣ := fun M => if h : ∃ a, adm a ∧ Mf a = M then h.choose else 1
  obtain ⟨F, hF⟩ := hNu
  refine ⟨(fun p : Submodule K.O B.A × B.Aˣ => mulLat K.O ((gch p.1 * p.2 : B.Aˣ) : B.A) Λ) ''
    (Bset ×ˢ (F : Set B.Aˣ)), ((hBe Λ hΛ (d * d) hdd0).prod F.finite_toSet).image _, ?_, ?_⟩
  · rintro J ⟨p, -, rfl⟩
    exact isLat_mulLat B _ hΛ
  intro J hJ hst h3 h4
  obtain ⟨a, rfl⟩ := hPr J hJ hst
  have ha : adm a := ⟨h3, h4⟩
  have hex' : ∃ a', adm a' ∧ Mf a' = Mf a := ⟨a, ha, rfl⟩
  have hg : gch (Mf a) = hex'.choose := dif_pos hex'
  obtain ⟨ha', hMa'⟩ := hex'.choose_spec
  set a' := hex'.choose

  have hv : Nu a * (Nu a')⁻¹ ∈ intUnits K.O B.A := by
    apply intUnit_of_mulLat
    have e1 : ((Nu a * (Nu a')⁻¹ : B.Aˣ) : B.A) =
        (((D * Nu a' * (Nu a₀)⁻¹)⁻¹ : B.Aˣ) : B.A) * ((D * Nu a * (Nu a₀)⁻¹ : B.Aˣ) : B.A) := by
      rw [← Units.val_mul]; congr 1; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
    rw [e1, mulLat_mul]
    change mulLat K.O _ (Mf a) = Λ
    rw [← hMa']
    change mulLat K.O _ (mulLat K.O _ Λ) = Λ
    rw [← mulLat_mul, hcancel]
  set u : B.Aˣ := a * a'⁻¹
  have hu : ∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u := by
    refine ⟨_, hv, ?_⟩
    rw [← hNuc]; congr 1; simp only [Nu, u, map_mul, map_inv]; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
  obtain ⟨f, hf, t, ht, hw⟩ := hF u hu
  refine ⟨t⁻¹, B.T.inv_mem ht, ⟨(Mf a, f), ⟨hM a ha, hf⟩, ?_⟩⟩
  have e2 : t⁻¹ * a = a' * f * (u * f⁻¹ * t⁻¹) := by simp only [u]; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
  show mulLat K.O ((gch (Mf a) * f : B.Aˣ) : B.A) Λ = mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (a : B.A) Λ)
  rw [hg, ← mulLat_mul, ← Units.val_mul, e2, Units.val_mul (a' * f), mulLat_mul _ _ Λ, mulLat_intUnit B _ hw]

end GlobalTheory.HullClasses
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSelfDualIntegralHermitianLatticesModUnits
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullClasses

theorem exists_unit_mulLat_mem_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x →
    ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S :=
  fun K B hsep x _ _ c hc0 =>
    finite_mod_T_of K B (GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra K B hsep) (GlobalTheory.T.exists_finset_cosets_integral_norm_units K B hsep) (GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B) x c hc0

end GlobalTheory.HullClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧ ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) → (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) → ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  first | exact @GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | exact GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | (intros; apply GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice <;> assumption)
end

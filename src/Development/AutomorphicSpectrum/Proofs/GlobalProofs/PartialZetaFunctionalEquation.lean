module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  have hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s := fun w ↦ by
    have hr : w.IsReal := IsTotallyReal.isReal w
    have hp := infiniteParams_eq_zero χ hχ w
    simp [HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau,
      HeckeCharacter.infiniteWeight, hp]
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  rw [HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const,
    Finset.card_univ, hcard]

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem discrNormConductor_eq_dF_of_unramified :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker → χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  intro F _ _ χ hχ
  have htop : χ.conductor = ⊤ := by
    have h := (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans hχ)
    rw [Ideal.dvd_iff_le, top_le_iff] at h
    exact h
  rw [HeckeCharacter.discrNormConductor, htop, Ideal.absNorm_top, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF]
  simp

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardOpenSubgroupLeKerInv
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem standardOpenSubgroup_le_ker_inv (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    standardOpenSubgroup F ≤ (χ⁻¹).toIdele.ker := by
  intro x hx
  have hx' : χ.toIdele x = 1 := h hx
  show (χ⁻¹).toIdele x = 1
  rw [HeckeCharacter.toIdele_apply] at hx' ⊢
  change (χ _)⁻¹ = 1
  rw [hx', inv_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors NNReal

namespace GlobalTheory.CompanionTheory.PartialZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F] {χ : HeckeCharacter F}

theorem conductor_eq_top (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have hd : χ.conductor ∣ ⊤ := by
    refine (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine h ((mem_standardOpenSubgroup_iff_toFinite_mem _).2 ?_)
    rw [toFinite_ofFinite]
    have hx' : x ∈ idealLevel (⊤ : Ideal (𝓞 F)) := hx
    rw [idealLevel, mem_finiteLevel] at hx'
    rw [mem_finiteLevel]
    intro v
    have hv := hx' v
    have h0 : multiplicity v.asIdeal (⊤ : Ideal (𝓞 F)) = 0 :=
      multiplicity_eq_zero_of_not_dvd fun hdv ↦ v.isPrime.ne_top (by
        rwa [Ideal.dvd_iff_le, top_le_iff] at hdv)
    rw [h0] at hv
    exact hv
  rwa [Ideal.dvd_iff_le, top_le_iff] at hd

theorem infiniteWeight_eq_zero (h : standardOpenSubgroup F ≤ χ.toIdele.ker)
    (w : InfinitePlace F) : χ.infiniteWeight w = 0 := by
  have hp : χ.infiniteParams w = (0, 0) := by
    refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
    have h1 : χ.infiniteComponent w a = 1 := h (infiniteEmbedding_mem_standardOpenSubgroup w a)
    simp [h1]
  rw [HeckeCharacter.infiniteWeight, hp]

theorem idealUnit_eq_one {I : Ideal (𝓞 F)} (hI : I = ⊤) (h : I ≠ ⊥) : idealUnit I h = 1 := by
  subst hI
  ext
  simp [idealUnit]

theorem finiteFourier_eq (h : χ.conductor = ⊤) {δ : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    finiteFourier F χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) := by
  have hE : IsEmpty χ.conductorPrimes := ⟨fun v ↦ by
    have hv := χ.mem_conductorPrimes.1 v.2
    rw [h, Ideal.dvd_iff_le, top_le_iff] at hv
    exact v.1.isPrime.ne_top hv⟩
  rw [χ.finiteFourier_finiteTestFun_inv_eq hδ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]

theorem discr_sqrt_mul (h : χ.conductor = ⊤) :
    (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) * (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  have hd : χ.discrNormConductor = |(discr F : ℝ)| := by
    rw [HeckeCharacter.discrNormConductor, h, Ideal.absNorm_top]
    simp
  have hpos : 0 < |(discr F : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hs : ((NNReal.sqrt ‖discr F‖₊ : ℝ≥0) : ℝ) = Real.sqrt |(discr F : ℝ)| := by
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hcp : ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos.le]
    norm_num
  have hne : ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
  have hinv : (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)⁻¹ := by
    rw [← hs]
    simp
  rw [hd, hcp, hinv, inv_mul_cancel₀ hne]

theorem rootNumber_eq_coeff_different (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)) := by
  have hc := conductor_eq_top h
  have hδ := χ.toFractionalIdeal_conductorDifferentIdele
  have hcop : IsCoprime (differentIdeal ℤ (𝓞 F)) χ.conductor := by
    rw [hc, ← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hmem : ofFinite χ.conductorDifferentIdele ∈ primeToLevel χ.conductor := by
    refine mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩
    rw [hc, Ideal.dvd_iff_le, top_le_iff] at hv
    exact absurd hv v.isPrime.ne_top
  have hval : χ.coeff (differentIdeal ℤ (𝓞 F)) =
      (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) := by
    rw [χ.coeff_of_mem ⟨differentIdeal_ne_bot, hcop⟩]
    congr 1
    refine χ.idealCharacter_apply hmem _ ?_
    rw [hδ, idealUnit_eq_one hc, one_mul]
    rfl
  rw [hval, HeckeCharacter.rootNumber, HeckeCharacter.fourierConst, finiteFourier_eq hc hδ]
  simp only [infiniteWeight_eq_zero h, Int.natAbs_zero, pow_zero, Finset.prod_const_one, one_mul]
  linear_combination (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * discr_sqrt_mul hc

end

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationOfUnramified
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem fe_of_parts (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HeckeCharacter F)
    (hD : χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F)
    (hG : ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hG' : ∀ s : ℂ, (χ⁻¹).gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hR : χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * χ.continuedLFunction s =
      χ.coeff (differentIdeal ℤ (𝓞 F)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * (χ⁻¹).continuedLFunction (1 - s)) := by
  have nz : ∀ t : ℂ, (∀ n : ℕ, t ≠ -2 * n) → Complex.Gammaℝ t ≠ 0 := by
    intro t ht h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.1 h0
    exact ht n (by rw [hn]; ring)
  have key := χ.continuedLFunction_functional_equation (s := s)
    (by rw [hG]; exact pow_ne_zero _ (nz s h1))
    (by rw [hG']; exact pow_ne_zero _ (nz _ h2))
  rw [hG, hG', hD, hR] at key
  exact key

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHeckeCharacterOfClassGroup
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

variable {F : Type} [Field F] [NumberField F]

noncomputable def classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    ClassGroup (𝓞 F) →* Circle where
  toFun c := AddChar.circleEquivComplex.symm ψ (Additive.ofMul c)
  map_one' := by
    rw [ofMul_one]
    exact AddChar.map_zero_eq_one _
  map_mul' a b := by
    rw [ofMul_mul]
    exact AddChar.map_add_eq_mul _ _ _

theorem coe_classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (c : ClassGroup (𝓞 F)) :
    (classCircle ψ c : ℂ) = ψ (Additive.ofMul c) := by
  rfl

theorem continuous_comp_toClassGroup (φ : ClassGroup (𝓞 F) →* Circle) :
    Continuous (φ.comp (IdeleClassGroup.toClassGroup (K := F))) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : IsOpen ((IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F))) :=
    IdeleClassGroup.isOpenMap_mk (K := F) _ (isOpen_standardOpenSubgroup F)
  have h1 : (1 : IdeleClassGroup F) ∈ (IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F)) :=
    ⟨1, (standardOpenSubgroup F).one_mem, map_one _⟩
  rw [ContinuousAt, map_one]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hU.mem_nhds h1] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.comp_apply, IdeleClassGroup.toClassGroup_mk, IdeleGroup.toClassGroup_apply, hx1,
    map_one, map_one]

noncomputable def classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) : HeckeCharacter F where
  toMonoidHom := (classCircle ψ).comp IdeleClassGroup.toClassGroup
  continuous_toFun := continuous_comp_toClassGroup _

theorem classHecke_toIdele (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (x : IdeleGroup F) :
    (classHecke ψ).toIdele x = classCircle ψ (IdeleGroup.toClassGroup x) :=
  rfl

theorem standardOpenSubgroup_le_ker (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    standardOpenSubgroup F ≤ (classHecke ψ).toIdele.ker := by
  intro x hx
  have h1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.mem_ker, classHecke_toIdele, IdeleGroup.toClassGroup_apply, h1, map_one, map_one]

theorem idealLevel_top : idealLevel (⊤ : Ideal (𝓞 F)) = finiteLevel 0 := by
  show finiteLevel (fun v => multiplicity v.asIdeal (⊤ : Ideal (𝓞 F))) = finiteLevel 0
  congr 1
  funext v
  rw [Pi.zero_apply]
  apply multiplicity_eq_zero_of_not_dvd
  intro h
  exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))

theorem conductor_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    (classHecke ψ).conductor = ⊤ := by
  have hne : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  have hle : Subgroup.map ofFinite (idealLevel (⊤ : Ideal (𝓞 F))) ≤ (classHecke ψ).toIdele.ker := by
    rintro _ ⟨z, hz, rfl⟩
    apply standardOpenSubgroup_le_ker ψ
    rw [mem_standardOpenSubgroup_iff_ord]
    intro v
    rw [idealLevel_top] at hz
    apply ord_eq_zero_of_mem_unitsLevel (n := 0)
    rw [← finiteComponent_toFinite, toFinite_ofFinite]
    exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hz v)
  have hd := ((classHecke ψ).map_idealLevel_le_ker_iff hne).mp hle
  exact top_le_iff.mp (Ideal.le_of_dvd hd)

theorem coeff_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (classHecke ψ).coeff J =
      ψ (Additive.ofMul (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩)) := by
  have hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (classHecke ψ).coeff v.asIdeal =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) := by
    intro v
    have hv : ¬ v.asIdeal ∣ (classHecke ψ).conductor := by
      rw [conductor_classHecke]
      intro h
      exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
    rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv]
    obtain ⟨x, hx, hxI⟩ := exists_mem_primeToLevel (primeIdealUnit_mem_idealsPrimeTo hv)
    have heq : (primeIdealUnit v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
        FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
      Units.ext (by rw [coe_primeIdealUnit, FractionalIdeal.coe_mk0])
    rw [HeckeCharacter.idealCharacter_apply _ hx ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ hxI,
      classHecke_toIdele, coe_classCircle, IdeleGroup.toClassGroup_apply, hxI, heq, ClassGroup.mk_mk0]
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 F) => ∀ hI : I ≠ ⊥,
      (classHecke ψ).coeff I =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))) J ?_ ?_ ?_ hJ
  · intro h
    exact absurd Ideal.zero_eq_bot h
  · intro x hx hx0
    obtain rfl := Ideal.isUnit_iff.mp hx
    have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hx0⟩ : (Ideal (𝓞 F))⁰) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [HeckeCharacter.coeff_top, h1, map_one, ofMul_one, AddChar.map_zero_eq_one]
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact ha
    have hp0 : p ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact hp.ne_zero
    have hv := hprime ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hmk : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 F))⁰) =
        ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha'⟩ :=
      Subtype.ext rfl
    rw [HeckeCharacter.coeff_mul, ih ha', hmk, map_mul, ofMul_mul, AddChar.map_add_eq_mul]
    congr 1

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConductorEqTopOfStandardOpen
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem conductor_eq_top_of_standardOpen {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have h1 : χ.conductor ∣ (⊤ : Ideal (𝓞 F)) :=
    (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans h)
  rw [← Ideal.one_eq_top] at h1
  exact Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1)

theorem toIdele_inv_apply {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (x : IdeleGroup F) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

theorem coeff_inv_mul_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
    standardOpenSubgroup F ≤ χ.toIdele.ker → ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      (χ⁻¹).coeff J * χ.coeff J = 1 := by
  intro F _ _ χ hχ J hJ
  have hc : χ.conductor = ⊤ := conductor_eq_top_of_standardOpen χ hχ
  have hc' : (χ⁻¹).conductor = ⊤ := by
    refine conductor_eq_top_of_standardOpen _ fun x hx ↦ ?_
    have h1 : χ.toIdele x = 1 := hχ hx
    rw [MonoidHom.mem_ker, toIdele_inv_apply, h1, inv_one]
  have h1 : J ≠ ⊥ ∧ IsCoprime J χ.conductor :=
    ⟨hJ, by rw [hc, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  have h2 : J ≠ ⊥ ∧ IsCoprime J (χ⁻¹).conductor :=
    ⟨hJ, by rw [hc', ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  obtain ⟨x, hx, hxJ⟩ := exists_mem_primeToLevel (idealUnit_mem_idealsPrimeTo h1.1 h1.2)
  have hx' : x ∈ primeToLevel (χ⁻¹).conductor := by rw [hc', ← hc]; exact hx
  rw [HeckeCharacter.coeff_of_mem _ h1, HeckeCharacter.coeff_of_mem _ h2,
    HeckeCharacter.idealCharacter_apply _ hx _ hxJ,
    HeckeCharacter.idealCharacter_apply _ hx' _ hxJ, toIdele_inv_apply, ← Circle.coe_mul,
    inv_mul_cancel, Circle.coe_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleSectionMemStandardOpenSubgroup
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem moduleSection_mem_standardOpenSubgroup {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (t : {r : ℝ // 0 < r}) :
    moduleSection w t ∈ standardOpenSubgroup F := by
  have h1 : ∀ s : {r : ℝ // 0 < r}, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((moduleSection w s : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro s v
    rw [← coe_finiteProj]
    simp [moduleSection, finiteProj_infiniteEmbedding]
  rw [mem_standardOpenSubgroup]
  intro v
  refine ⟨?_, ?_⟩
  · rw [h1]; exact one_mem _
  · rw [← map_inv, h1]; exact one_mem _

theorem differentiableOn_continuedLFunction :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker →
        DifferentiableOn ℂ χ.continuedLFunction {1}ᶜ := by
  intro F _ _ χ hU
  by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F,
      (χ.toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := h
    let w : InfinitePlace F := Classical.arbitrary _
    have hs : ∀ t : {x : ℝ // 0 < x}, χ.toIdele (moduleSection w t) = 1 := fun t ↦
      MonoidHom.mem_ker.1 (hU (moduleSection_mem_standardOpenSubgroup w t))
    have h0 : archExponent w χ = 0 := archExponent_unique w χ fun t ↦ by simp [hs t]
    have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
    have hd := HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ
    simpa [hτ0] using hd
  · exact (χ.differentiable_continuedLFunction h).differentiableOn

end GlobalTheory.CompanionTheory.PartialZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumAddCharOfMulMulOfMulInv
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem sum_addChar_ofMul_mul_ofMul_inv (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (a b : G) :
    ∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      ψ (Additive.ofMul (a * b⁻¹)) := by
    intro ψ
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite]
  have hc : Fintype.card (Additive G) = Fintype.card G :=
    Fintype.card_congr Additive.ofMul.symm
  simp only [hc, ofMul_eq_zero, mul_inv_eq_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

noncomputable section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CompanionTheory.PartialZeta
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

theorem coeff_inv_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (J : (Ideal (𝓞 F))⁰) :
    ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) = ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) := by
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have h1 := coeff_inv_mul_coeff F (classHecke ψ) (standardOpenSubgroup_le_ker ψ) J hJ
  rw [coeff_classHecke ψ J hJ] at h1
  have h2 : ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 J)) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel, ofMul_one, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

def zetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).continuedLFunction s

def zetaOfClassInv (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).continuedLFunction s

theorem isPartialZeta_of_indicator {ι : Type} [Fintype ι] (χ : ι → HeckeCharacter F) (c : ι → ℂ)
    (C : ClassGroup (𝓞 F)) (hU : ∀ i, standardOpenSubgroup F ≤ (χ i).toIdele.ker)
    (horth : ∀ J : (Ideal (𝓞 F))⁰,
      (ClassGroup.mk0 J = C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 1) ∧
      (ClassGroup.mk0 J ≠ C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 0)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (fun s => ∑ i, c i * (χ i).continuedLFunction s) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => (differentiableOn_continuedLFunction F (χ i) (hU i)).const_mul (c i)
  · have h1 : HasSum (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (∑ i, c i * (χ i).continuedLFunction s) := by
      refine hasSum_sum fun i _ => ?_
      rw [(χ i).continuedLFunction_eq hs]
      exact ((χ i).hasSum_LFunction hs).mul_left (c i)
    have hfac : ∀ I : Ideal (𝓞 F),
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) =
          (∑ i, c i * (χ i).coeff I) * (Ideal.absNorm I : ℂ) ^ (-s) := fun I => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    let g : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → Ideal (𝓞 F) :=
      fun J => (J.1 : Ideal (𝓞 F))
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have hsupp : ∀ I ∉ Set.range g,
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) = 0 := by
      intro I hI
      by_cases hbot : I = ⊥
      · subst hbot
        simp
      · let J : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
        have hJ : ClassGroup.mk0 J ≠ C := fun h => hI ⟨⟨J, h⟩, rfl⟩
        rw [hfac, show I = (J : Ideal (𝓞 F)) from rfl, (horth J).2 hJ, zero_mul]
    have h2 := (hg.hasSum_iff hsupp).2 h1
    have h3 : (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s))) ∘ g =
        fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) := funext fun J => by
      simp only [Function.comp_apply]
      rw [hfac, show g J = (J.1 : Ideal (𝓞 F)) from rfl, (horth J.1).1 J.2, one_mul]
    rw [h3] at h2
    exact h2

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem isPartialZeta_zetaOfClass (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClass C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => classHecke ψ) _ C (fun ψ => standardOpenSubgroup_le_ker ψ) fun J => ?_
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if ClassGroup.mk0 J = C then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_classHecke ψ J hJ]
    ring_nf
  rw [e]
  constructor
  · intro h
    rw [if_pos h, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg h, mul_zero]

theorem isPartialZeta_zetaOfClassInv (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClassInv C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => (classHecke ψ)⁻¹) _ C
    (fun ψ => standardOpenSubgroup_le_ker_inv F _ (standardOpenSubgroup_le_ker ψ)) fun J => ?_
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if C = ClassGroup.mk0 J then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_inv_classHecke ψ J, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [if_pos h.symm, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg (Ne.symm h), mul_zero]

theorem functionalEquation_classHecke [IsTotallyReal F] (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * (classHecke ψ).continuedLFunction s =
      ψ (Additive.ofMul (ClassGroup.mk0 D)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * ((classHecke ψ)⁻¹).continuedLFunction (1 - s)) := by
  have hU := standardOpenSubgroup_le_ker ψ
  have h := fe_of_parts F (classHecke ψ) (discrNormConductor_eq_dF_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ (standardOpenSubgroup_le_ker_inv F _ hU))
    (rootNumber_eq_coeff_different F _ hU) s h1 h2
  rw [← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂

theorem GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation := by
  intro F _ _ _ C C' D hD hC
  refine ⟨GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv C',
    GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClassInv C', fun s h1 h2 => ?_⟩
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have h := GlobalTheory.CompanionTheory.Hypotheses₂.functionalEquation_classHecke ψ D hD s h1 h2
  have e : ψ (Additive.ofMul C⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 D)) = ψ (Additive.ofMul C') := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, ← hC, inv_mul_cancel_left]
  calc _ = ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F *
          (GlobalTheory.CompanionTheory.PartialZeta.classHecke ψ).continuedLFunction s) := by ring
    _ = _ := by
      rw [h, ← e]
      ring

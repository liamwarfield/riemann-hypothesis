module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEnlargeByUniformiserRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteEtaleOriginKeyLemmaEssFinitStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetween
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfMonic
open Polynomial

namespace GlobalTheory.MonicRootRange

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (h : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  set f := algebraMap T (FractionRing T)
  have hinj : Function.Injective f := IsFractionRing.injective T (FractionRing T)
  have hb0 : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hn : 1 ≤ p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hdeg : q.natDegree = p.natDegree := by
    have := congrArg natDegree hq
    rwa [natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0] at this
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; omega
  have hc0 : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)
  obtain ⟨w, hw⟩ := h q.integralNormalization (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  refine ⟨f w / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero] at key
  have h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0 :=
    (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)
  rw [← eval_map, hq, hsmul, eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left hb0

end GlobalTheory.MonicRootRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetween
open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.LocAcycEmbed

theorem exists_eq_of_aeval_eq_zero {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ x : K, aeval x f = 0 →
      ∃ t : T, algebraMap T K t = x := by
  intro n
  induction n with
  | zero =>
    intro f hf hn x hx
    have h1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hn
    subst h1
    simp at hx
  | succ n ih =>
    intro f hf hn x hx
    obtain ⟨r, hr⟩ := hT f hf (by omega)
    have hfg : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.2 hr
    have hg : (f /ₘ (X - C r)).Monic := by
      apply Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r)
      rw [hfg]; exact hf
    have hgn : (f /ₘ (X - C r)).natDegree = n := by
      have := Polynomial.Monic.natDegree_mul (monic_X_sub_C r) hg
      rw [hfg, natDegree_X_sub_C] at this
      omega
    rw [← hfg, map_mul] at hx
    rcases mul_eq_zero.1 hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      rw [sub_eq_zero] at h
      exact h.symm
    · exact ih _ hg hgn x h

theorem isIntegrallyClosed_of_absIntClosed (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨f, hf, h⟩ := hx
  exact exists_eq_of_aeval_eq_zero hT _ f hf rfl x (by rw [aeval_def]; exact h)

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  first
  | exact @_root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing
  | exact _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing
  | (apply _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing ..)

end GlobalTheory.LocAcycEmbed

namespace GlobalTheory.LocAcycEmbed

theorem essFiniteType_int_of_finite_localization {A C A₁ : Type} [CommRing A] [CommRing C] [CommRing A₁]
    [Algebra A C] [Algebra C A₁] [Algebra.EssFiniteType ℤ A] [Module.Finite A C] (M : Submonoid C)
    [IsLocalization M A₁] : Algebra.EssFiniteType ℤ A₁ := by
  haveI : IsScalarTower ℤ A C := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_intCast (algebraMap ℤ C), eq_intCast (algebraMap ℤ A), map_intCast])
  haveI : IsScalarTower ℤ C A₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_intCast (algebraMap ℤ A₁), eq_intCast (algebraMap ℤ C), map_intCast])
  haveI : Algebra.EssFiniteType A C := Algebra.EssFiniteType.of_finiteType A C
  haveI : Algebra.EssFiniteType C A₁ := Algebra.EssFiniteType.of_isLocalization A₁ M
  haveI : Algebra.EssFiniteType ℤ C := Algebra.EssFiniteType.comp ℤ A C
  exact Algebra.EssFiniteType.comp ℤ C A₁

theorem exists_fractionRing_hom {C A₁ : Type} [CommRing C] [IsDomain C] [CommRing A₁] [IsDomain A₁]
    [Algebra C A₁] (L : Type) [Field L] [Algebra C L] [IsFractionRing C L]
    (hinj : Function.Injective (algebraMap C A₁)) :
    ∃ κ : L →+* FractionRing A₁,
      κ.comp (algebraMap C L) = (algebraMap A₁ (FractionRing A₁)).comp (algebraMap C A₁) := by
  have hg : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp (algebraMap C A₁)) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hinj
  refine ⟨IsFractionRing.lift (A := C) (K := L) hg, ?_⟩
  exact IsLocalization.lift_comp _

end GlobalTheory.LocAcycEmbed

namespace GlobalTheory.LocAcycEmbed

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_normal_local_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  intro T _ _ _ hT A _ _ _ _ _ _ i hi L _ _ _ _
  haveI : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed T hT
  haveI : IsAlgClosed (FractionRing T) := isAlgClosed_fractionRing T hT
  have hgi : Function.Injective ((algebraMap T (FractionRing T)).comp i) :=
    (IsFractionRing.injective T (FractionRing T)).comp hi
  let φ : FractionRing A →+* FractionRing T := IsFractionRing.lift hgi
  letI : Algebra (FractionRing A) (FractionRing T) := φ.toAlgebra
  let σ : L →ₐ[FractionRing A] FractionRing T := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra A L := ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : IsScalarTower A (FractionRing A) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAL : Function.Injective (algebraMap A L) :=
    (algebraMap (FractionRing A) L).injective.comp (IsFractionRing.injective A (FractionRing A))
  have h1 : (algebraMap T (FractionRing T)).comp i = (σ : L →+* FractionRing T).comp (algebraMap A L) := by
    ext a
    show algebraMap T (FractionRing T) (i a) = σ (algebraMap (FractionRing A) L (algebraMap A (FractionRing A) a))
    rw [σ.commutes]
    show _ = φ (algebraMap A (FractionRing A) a)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let C := integralClosure A L
  haveI : Module.Finite A C := IsIntegralClosure.finite A (FractionRing A) L C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  haveI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension (FractionRing A) L
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have hint : ∀ x : C, ∃ t : T, algebraMap T (FractionRing T) t = σ (x : L) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := x.2
    apply exists_eq_of_aeval_eq_zero hT _ (f.map i) (hf.map i) rfl
    rw [aeval_def, eval₂_map, h1]
    have := Polynomial.hom_eval₂ f (algebraMap A L) (σ : L →+* FractionRing T) (x : L)
    rw [hfx, map_zero] at this
    exact this.symm
  choose ct hct using hint
  have hinjT := IsFractionRing.injective T (FractionRing T)
  let c : C →+* T :=
    { toFun := ct
      map_one' := hinjT (by rw [hct]; simp)
      map_mul' := fun x y => hinjT (by rw [hct, map_mul, hct, hct]; simp)
      map_zero' := hinjT (by rw [hct]; simp)
      map_add' := fun x y => hinjT (by rw [hct, map_add (f := _), hct, hct]; simp) }
  have hc : ∀ x, algebraMap T (FractionRing T) (c x) = σ (x : L) := hct
  have hcinj : Function.Injective c := by
    intro x y h
    have := congrArg (algebraMap T (FractionRing T)) h
    rw [hc, hc] at this
    exact Subtype.ext ((σ : L →+* FractionRing T).injective this)
  have hci : c.comp (algebraMap A C) = i := by
    ext a
    apply hinjT
    rw [RingHom.comp_apply, hc]
    exact (RingHom.congr_fun h1 a).symm
  let P : Ideal C := (maximalIdeal T).comap c
  haveI : P.IsPrime := Ideal.comap_isPrime c _
  have hunit : ∀ y : P.primeCompl, IsUnit (c y) := fun y => by
    by_contra h
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let i₁ : Localization.AtPrime P →+* T := IsLocalization.lift hunit
  let j : A →+* Localization.AtPrime P := (algebraMap C (Localization.AtPrime P)).comp (algebraMap A C)
  have hAC : Function.Injective (algebraMap A C) := fun x y h => hAL (congrArg Subtype.val h)
  have hCA₁ : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  have hj : Function.Injective j := hCA₁.comp hAC
  have hi₁ : Function.Injective i₁ :=
    (IsLocalization.lift_injective_iff hunit).2 fun x y =>
      ⟨fun h => congrArg c (hCA₁ h), fun h => congrArg _ (hcinj h)⟩
  have hloc : IsLocalHom i₁ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime P) P.primeCompl x
    have e1 := IsLocalization.mk'_spec (Localization.AtPrime P) a s
    have e2 : IsUnit (c a) := by
      rw [← IsLocalization.lift_eq (S := Localization.AtPrime P) hunit a, ← e1, map_mul, IsLocalization.lift_eq (S := Localization.AtPrime P) hunit]
      exact hx.mul (hunit s)
    have ha : a ∈ P.primeCompl := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) e2
    exact isUnit_of_mul_isUnit_left (e1 ▸ IsLocalization.map_units (Localization.AtPrime P) ⟨a, ha⟩)
  have hcomp : i₁.comp j = i := by
    ext a
    show i₁ (algebraMap C _ (algebraMap A C a)) = i a
    rw [IsLocalization.lift_eq]
    exact RingHom.congr_fun hci a
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P)
  obtain ⟨κ, hκ⟩ := exists_fractionRing_hom (A₁ := Localization.AtPrime P) L hCA₁
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    essFiniteType_int_of_finite_localization (A := A) (C := C) P.primeCompl, j, i₁, hj, hi₁, hloc, hcomp, κ, ?_⟩
  ext a
  exact RingHom.congr_fun hκ (algebraMap A C a)

end GlobalTheory.LocAcycEmbed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetweenStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_between_alt : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  first | (exact @GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (exact GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (intros; apply GlobalTheory.LocAcycEmbed.exists_normal_local_between  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosure
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlargePoint

theorem enlarge_point : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
  obtain ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ := hFits
  have hu : ∀ y : Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A),
      IsUnit (((algebraMap A (FractionRing A)).comp ρ) (y : Localization.AtPrime QA)) := by
    rintro ⟨y, a, ha, rfl⟩
    have h1 : ρ (algebraMap A (Localization.AtPrime QA) a) = a := by
      simpa using congrArg (fun f => f a) hRet.1
    simp only [RingHom.comp_apply, h1]
    exact IsLocalization.map_units (FractionRing A) (⟨a, ha⟩ : nonZeroDivisors A)
  let ρK : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* FractionRing A := IsLocalization.lift hu
  have hρK : ρK.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap A (FractionRing A)).comp ρ := IsLocalization.lift_comp hu
  obtain ⟨L, _, _, _, _, σL, hσL⟩ := GlobalTheory.T.zmodTorsor_exists_point_finite_separable _ (FractionRing A) ρK DA q hq actA hTor
  obtain ⟨A₁, _, _, _, _, _, _, j, i₁, hj, hi₁, hl₁, hji, κ, hκ⟩ := GlobalTheory.T.exists_normal_local_between_alt T hAIC A i hi L
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, ρ₁, hF₁, hR₁, β, h, hβ, hh, hσ⟩ :=
    GlobalTheory.T.exists_baseChange_fittingDatum_retraction T O P φ hφ hSH hP q hq A i EA QA jA ψA DA actA ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ ρ hRet
      A₁ j i₁ hj hi₁ hl₁ hji
  obtain ⟨σ₁, hσ₁⟩ := hσ (κ.comp σL) (by
    ext x
    have h1 := congrArg (fun f => f (algebraMap (Localization.AtPrime QA)
      (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) x)) hσL
    have h2 := congrArg (fun f => f x) hρK
    have h3 := congrArg (fun f => f (ρ x)) hκ
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3])
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hF₁, ⟨ρ₁, hR₁, ?_⟩, β, h, hβ, hh⟩
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Localization.AtPrime QA₁) DA₁
  refine ⟨σ₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Localization.AtPrime QA₁) DA₁).subtype, ?_⟩
  ext r
  exact congrArg (fun f => f r) hσ₁

end GlobalTheory.KeyOriginEnlargePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosureStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_base_separable_point_integralClosure : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (exact GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (intros; apply GlobalTheory.KeyOriginEnlargePoint.enlarge_point  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOrigin
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem enlarge_good : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  have hF : GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA :=
    ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩
  obtain ⟨A₁, _, _, _, _, _, _, i₁, EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, act₁, hF₁,
    ⟨ρ₁, hR₁, -⟩, β₁, h₁, hβ₁, hh₁⟩ := GlobalTheory.T.enlarge_strictHenselisation_retract_mod T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF
  obtain ⟨A₂, _, _, _, _, _, _, i₂, EA₂, _, _, _, _, _, QA₂, _, jA₂, ψA₂, DA₂, _, _, act₂, hF₂,
    ⟨ρ₂, hR₂, hpt₂⟩, β₂, h₂, hβ₂, hh₂⟩ :=
    GlobalTheory.T.enlarge_base_separable_point_integralClosure T O hT P φ hφ hsh hP q hq0 hqT A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ act₁ hF₁ ρ₁ hR₁
  obtain ⟨A₃, _, _, _, _, _, _, i₃, EA₃, _, _, _, _, _, QA₃, _, jA₃, ψA₃, DA₃, _, _, act₃, hF₃,
    ⟨ρ₃, hR₃, hgood⟩, β₃, h₃, hβ₃, hh₃⟩ :=
    GlobalTheory.T.etale_enlarge_by_uniformiser_roots T O hT P φ hφ hsh hP q hq0 hqT A₂ i₂ EA₂ QA₂ jA₂ ψA₂ DA₂ act₂ hF₂ ρ₂ hR₂ hpt₂
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    EA₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₃, inferInstance,
    hF₃.2.2.2.1, hF₃.2.2.1, ρ₃, hR₃.1, hR₃.2.1, jA₃, ψA₃, hF₃.2.2.2.2.2.1, DA₃, inferInstance,
    inferInstance, act₃, hF₃.2.2.2.2.2.2, hgood, β₃.comp (β₂.comp β₁), h₃.comp (h₂.comp h₁), ?_, ?_⟩
  · ext x
    have a1 := RingHom.congr_fun hβ₁ x
    have a2 := RingHom.congr_fun hβ₂ (β₁ x)
    have a3 := RingHom.congr_fun hβ₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a3, a2, a1]
  · ext x
    have a1 := RingHom.congr_fun hh₁ x
    have a2 := RingHom.congr_fun hh₂ (β₁ x)
    have a3 := RingHom.congr_fun hh₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a1, a2, a3]

end GlobalTheory.KeyOriginEnlarge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOriginStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictHenselisation_enlarge_good_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_good) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_good) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_good  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointClosureFiniteEtaleStrictHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointClosureFiniteEtaleStrictHenselian
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale :
    ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : _root_.GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (_root_.GlobalTheory.LocAcyc.GenFib A R) D → _root_.GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  intro A R O B _ _ _ _ _ _ _ _ _ _ j β ψ hψ D _ _ hfin hE
  letI : Algebra R D := (_root_.GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI : Algebra R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) :=
    _root_.GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨hEfin, hEet, hEnt⟩ := hE
  haveI := hEfin
  haveI := hEet
  haveI := hEnt
  haveI := hfin
  letI : Algebra R O := j.toAlgebra
  haveI : Module.Free R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) := Module.free_of_flat_of_isLocalRing
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := _root_.GlobalTheory.KeyOriginNoeth.closure A R D)
    ⟨RingHom.ker (algebraMap R (ResidueField O)), RingHom.ker_isPrime _⟩
  have hq' : Ideal.comap (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)) q.asIdeal =
      RingHom.ker (algebraMap R (ResidueField O)) := congrArg PrimeSpectrum.asIdeal hq
  obtain ⟨φ₀⟩ := _root_.GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed q.asIdeal hq'
  obtain ⟨φ, -⟩ := (_root_.GlobalTheory.EtaleHensel.bijective_residue_comp R
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) O).2 φ₀
  letI : Algebra (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  haveI : IsScalarTower R (_root_.GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalization ((Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D))) D := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map
        (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D)
    · intro d
      obtain ⟨⟨m, hm⟩, hmint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) d
        (Algebra.IsIntegral.isIntegral (R := _root_.GlobalTheory.LocAcyc.GenFib A R) d)
      refine ⟨⟨⟨m • d, hmint⟩, ⟨algebraMap R _ m, m, hm, rfl⟩⟩, ?_⟩
      show d * algebraMap R D m = m • d
      rw [Algebra.smul_def, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  have hσ : ∀ r : R, β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r)) =
      ψ (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R) r) := by
    intro r
    rw [φ.commutes]
    exact (RingHom.congr_fun hψ r).symm
  have hunits : ∀ y : (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)), IsUnit ((β.comp φ.toRingHom) y) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    show IsUnit (β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) s)))
    rw [hσ]
    exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map ψ
  refine ⟨IsLocalization.lift (S := D) hunits, ?_⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  ext r
  have hr : algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D (algebraMap R _ r) =
      algebraMap (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D
        (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r) := rfl
  simp only [RingHom.comp_apply]
  rw [hr, IsLocalization.lift_eq]
  exact hσ r

end GlobalTheory.KeyOriginNoeth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointClosureFiniteEtaleStrictHenselianStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian : ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D → GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (exact GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNorm
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem torsor_point_of_essFiniteType : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  obtain ⟨A', _, _, _, _, _, _, EA', _, _, _, _, _, QA', _, hQ', hq', ρ', hρ1, hρ2, jA', ψA', hψ', DA', _, _,
    actA', htor', hgood', β, h, hβ1, hβ2⟩ :=
    GlobalTheory.T.strictHenselisation_enlarge_good_at_origin T O hT P φ hφ hsh hP q hq0 hqT A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htor
  have hce := GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType A' EA' QA' hQ' ρ' hρ1 hρ2 q hq0 hq' DA' actA' htor' hgood'
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsSepClosed (ResidueField O) := hsh.2.1
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian A' (Localization.AtPrime QA') O (GlobalTheory.LocAcyc.GenFib T O) jA'
    (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)) ψA' hψ' DA' htor'.1 hce
  refine ⟨σ'.comp h, ?_⟩
  rw [RingHom.comp_assoc, hβ2, ← RingHom.comp_assoc, hσ', hβ1]

end GlobalTheory.KeyOriginNoeth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNormStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  first | (exact @GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (exact GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (intros; apply GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType  <;> assumption)
end

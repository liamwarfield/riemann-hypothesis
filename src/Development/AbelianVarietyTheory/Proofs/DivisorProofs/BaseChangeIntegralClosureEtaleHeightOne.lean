module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalLocalRingEtaleBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTorsorEtaleHeightOneAbhyankar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAtPrimeEtaleCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePointsBaseChange
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem exists_point_ext (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D]
    (ρ : R →+* A) (hρA : ρ.comp (algebraMap A R) = RingHom.id A)
    (h : GlobalTheory.KeyOriginEnlarge.PointAtZero A R D ρ) :
    ∃ S : D →+* FractionRing A,
      S.comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = (algebraMap A (FractionRing A)).comp ρ := by
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨s, hs⟩ := h
  letI : Algebra (GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  let g : A →+* GlobalTheory.KeyOriginNoeth.closure A R D :=
    (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)).comp (algebraMap A R)
  let M : Submonoid (GlobalTheory.KeyOriginNoeth.closure A R D) := (nonZeroDivisors A).map g
  have hg : ∀ a : A, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) =
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) := fun _ => rfl
  have hR : ∀ r : R, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D
      (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) = GlobalTheory.KeyOriginNoeth.baseHom A R D r :=
    fun _ => rfl
  haveI : IsLocalization M D :=
    { map_units := by
        rintro ⟨_, a, ha, rfl⟩
        show IsUnit (algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a))
        rw [hg]
        exact (IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R)
          (⟨algebraMap A R a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))).map
          (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D)
      surj := fun d => by
        obtain ⟨a, ha, hd⟩ := GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure A R D {d}
        refine ⟨(⟨_, hd d (Finset.mem_singleton_self d)⟩,
          ⟨g a, a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩), ?_⟩
        show d * algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) = _
        rw [hg, mul_comm]
        rfl
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [Subtype.ext hxy]⟩ }
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => congrArg (fun w => w a) hρA
  have hsr : ∀ r : R, s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) =
      algebraMap A (FractionRing A) (ρ r) := fun r => congrArg (fun w => w r) hs
  have hu : ∀ y : M, IsUnit (s y) := by
    rintro ⟨_, a, ha, rfl⟩
    show IsUnit (s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a)))
    rw [hsr, hρa]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A (FractionRing A))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A (FractionRing A) h0)
  refine ⟨IsLocalization.lift (M := M) (S := D) hu, ?_⟩
  apply RingHom.ext; intro r
  rw [RingHom.comp_apply, ← hR, IsLocalization.lift_eq, hsr]
  rfl

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem pointAtZero_bc : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ f i i₁ hf EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit DA _ _ q actA
    hq htor hpt
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htor.1
  obtain ⟨S, hS⟩ := exists_point_ext A (Localization.AtPrime QA) DA ρ hρA hpt

  have hfK : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp f) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hf
  let φ : FractionRing A →+* FractionRing A₁ := IsFractionRing.lift hfK
  have hφ : ∀ a : A, φ (algebraMap A (FractionRing A) a) = algebraMap A₁ (FractionRing A₁) (f a) :=
    fun a => IsFractionRing.lift_algebraMap hfK a

  have hρ₁a : ∀ a : A₁, reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) a) = a :=
    fun a => congrArg (fun w => w a) (reduceLoc_algebraMap f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
  have hu₀ : ∀ y : Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁),
      IsUnit (((algebraMap A₁ (FractionRing A₁)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) y) := by
    rintro ⟨_, a, ha, rfl⟩
    simp only [RingHom.coe_comp, Function.comp_apply, hρ₁a]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A₁ (FractionRing A₁))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A₁ (FractionRing A₁) h0)
  let u : GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) →+* FractionRing A₁ :=
    IsLocalization.lift hu₀
  have hu : ∀ r, u (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r) =
      algebraMap A₁ (FractionRing A₁) (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit r) :=
    fun r => IsLocalization.lift_eq hu₀ r

  let v : DA →+* FractionRing A₁ := φ.comp S
  have huv : u.comp (fibBC f i i₁ EA QA jA hcomp hj hf) =
      v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    simp only [RingHom.coe_comp, Function.comp_apply, fibBC_algebraMap, hu]
    have h1 := congrArg (fun w => w r) (reduceLoc_locBC f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
    have h2 := congrArg (fun w => w r) hS
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    rw [h1]
    show _ = φ (S (GlobalTheory.KeyOriginNoeth.baseHom A _ DA r))
    rw [h2, hφ]

  letI : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) (FractionRing A₁) :=
    (v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).toAlgebra
  let W₁ : BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA →+* FractionRing A₁ :=
    (Algebra.TensorProduct.productMap
      (⟨(u : Over (fibBC f i i₁ EA QA jA hcomp hj hf) →+* FractionRing A₁), fun r =>
        congrArg (fun w => w r) huv⟩ :
          Over (fibBC f i i₁ EA QA jA hcomp hj hf) →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)]
            FractionRing A₁)
      (⟨v, fun _ => rfl⟩ : DA →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] FractionRing A₁)).toRingHom
  have hW : ∀ y, W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA) y) = u y := by
    intro y
    show W₁ ((show Over (fibBC f i i₁ EA QA jA hcomp hj hf) from y) ⊗ₜ (1 : DA)) = u y
    refine (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans ?_
    rw [map_one, mul_one]
    rfl
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
  refine ⟨W₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)).subtype, ?_⟩
  apply RingHom.ext; intro r
  show W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r)) = _
  rw [hW, hu]
  rfl

end GlobalTheory.KeyOriginBC
end
end

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_at_prime_etale_compat : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  first | (exact @GlobalTheory.KeyOriginBC.pointAtZero_bc) | (exact GlobalTheory.KeyOriginBC.pointAtZero_bc) | (intros; apply GlobalTheory.KeyOriginBC.pointAtZero_bc  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanX
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanX
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC

theorem ker_reduceLoc_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  intro T O _ _ _ _ _ _ A A₁ _ _ f i i₁ EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit hker
  have hψ : ∀ p : A₁[X], algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) p =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) p) :=
    fun _ => rfl
  have hC : ∀ c : A₁, algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) c =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) (C c)) := by
    intro c
    rw [IsScalarTower.algebraMap_apply A₁ (Ext f EA), IsScalarTower.algebraMap_apply A₁ A₁[X] (Ext f EA)]
    rfl
  have hlocX : locBC f i i₁ EA QA jA hcomp hj (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) Polynomial.X) := by
    rw [IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA), locBC_algebraMap]
    have h1 : inclE f EA (algebraMap A[X] EA Polynomial.X) =
        algebraMap A[X] (Ext f EA) Polynomial.X :=
      (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).commutes _
    rw [h1, Algebra.TensorProduct.algebraMap_apply, algebraMap_polyOver, Polynomial.map_X]
    rfl
  have hpol : ∀ q : A₁[X],
      Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X})
        (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) q)) =
      Ideal.Quotient.mk _ (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (Polynomial.eval 0 q)) := by
    intro q
    rw [hC, Ideal.Quotient.eq, ← map_sub, ← map_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := q)
    rw [hr, map_mul, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : (Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X}) :
        Loc₁ f i i₁ EA QA jA hcomp hj →+* _) =
      (Ideal.Quotient.mk _).comp ((algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) := by
    apply IsLocalization.ringHom_ext (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply, reduceLoc, IsLocalization.lift_eq]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p x =>
      rw [reduce_tmul]
      dsimp only
      have hsplit : (p ⊗ₜ[A[X]] x : Ext f EA) =
          algebraMap A₁[X] (Ext f EA) p * inclE f EA x := by
        show (p ⊗ₜ[A[X]] x : Ext f EA) = (p ⊗ₜ[A[X]] (1 : EA)) * ((1 : PolyOver f) ⊗ₜ[A[X]] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      simp only [map_mul]
      congr 1
      · exact hpol p
      · rw [← locBC_algebraMap, ← locBC_algebraMap_base]
        have hmem : algebraMap EA (Localization.AtPrime QA) x -
            algebraMap A (Localization.AtPrime QA) (ρ (algebraMap EA (Localization.AtPrime QA) x)) ∈
              RingHom.ker ρ := by
          rw [RingHom.mem_ker, map_sub]
          have := congrArg (fun w => w (ρ (algebraMap EA (Localization.AtPrime QA) x))) hρA
          simp only [RingHom.comp_apply, RingHom.id_apply] at this
          rw [this, sub_self]
        rw [hker, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, hlocX]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h := congrArg (fun w => w x) key
    simp only [RingHom.comp_apply, hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X) = 0
    rw [hψ, reduceLoc, IsLocalization.lift_eq,
      show algebraMap A₁[X] (Ext f EA) Polynomial.X = (@id (PolyOver f) Polynomial.X) ⊗ₜ[A[X]] (1 : EA)
        from rfl, reduce_tmul]
    show Polynomial.eval 0 (Polynomial.X : A₁[X]) * _ = 0
    rw [Polynomial.eval_X, zero_mul]

end GlobalTheory.KeyOriginBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanXStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_baseChangedReduction_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  first | (exact @GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X) | (exact GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X) | (intros; apply GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOne
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC


set_option maxHeartbeats 800000 in
theorem etale_bc : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
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
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA
    hFits ρ hρ hpt a ha0 ha A₁ _ _ _ _ _ _ f i₁ hf hi₁ hloc₁ hcomp hK
  obtain ⟨-, -, hqA, -, hj, hψ, htor⟩ := hFits
  obtain ⟨hρA, hρker, hρmod⟩ := hρ
  have hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0 := by
    rw [← RingHom.mem_ker, hρker]; exact Ideal.subset_span rfl
  have hmax := comap_maximalIdeal_eq_origin P φ hφ hsh hP
  set β := fibBC f i i₁ EA QA jA hcomp hj hf with hβ
  have hcong := reduce_sub_glue_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hρmod
  have hunit := isUnit_reduce f i i₁ EA QA jA hcomp hj ρ hρA hρX hmax hloc₁ hcong
  refine ⟨Ext f EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ideal₁ f i i₁ EA QA jA hcomp hj, inferInstance, locMap f i i₁ EA QA jA hcomp hj,
    fibMap f i i₁ EA QA jA hcomp hj hi₁, BC β DA, inferInstance, inferInstance, bcAct β DA q actA,
    ⟨hi₁, hloc₁, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, β, inclD β DA, ?_,
    inclD_algebraMap β DA⟩
  · simpa using hqA.map f
  · exact comap_ideal₁_eq_origin f i i₁ EA QA jA hcomp hj hmax hloc₁
  · apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj),
      locMap_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [glue_tmul]
    change algebraMap T[X] O (Polynomial.map i₁ p) * _ = _
    simp
  · exact RingHom.ext fun x => by simp only [fibMap, IsLocalization.lift_eq, RingHom.comp_apply]
  · exact isZTorsor_bc β DA q hq actA htor
  · apply RingHom.ext; intro x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁ (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    simp only [reduceLoc, IsLocalization.lift_eq, algebraMap_ext, reduce_tmul]
    change Polynomial.eval 0 (Polynomial.C x) * _ = _
    simp
  · exact GlobalTheory.T.ker_baseChangedReduction_eq_span_X T O A A₁ f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hρker
  · exact reduceLoc_sub_locMap_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hcong
  · exact GlobalTheory.T.localization_at_prime_etale_compat T O A A₁ f i i₁ hf EA QA jA hcomp hj ρ hρA hρX hunit DA q actA hq htor hpt
  · intro P₁ _ hP₁
    by_cases h : algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁
    · exact GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 hK P₁ hP₁ h
    · exact GlobalTheory.T.normal_local_ring_etale_base_change T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 ha P₁ h
  · have hloc : (locMap f i i₁ EA QA jA hcomp hj).comp (locBC f i i₁ EA QA jA hcomp hj) = jA := by
      apply IsLocalization.ringHom_ext QA.primeCompl
      apply RingHom.ext; intro x
      simp [locBC_algebraMap, locMap_algebraMap, glue_inclE]
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, hβ, fibBC_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply ψA, hψ]
    simp only [fibMap, IsLocalization.lift_eq, RingHom.comp_apply]
    rw [← RingHom.comp_apply (locMap f i i₁ EA QA jA hcomp hj), hloc]

end GlobalTheory.KeyOriginBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOneStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_integralClosure_etale_height_one : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
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
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  first | (exact @GlobalTheory.KeyOriginBC.etale_bc) | (exact GlobalTheory.KeyOriginBC.etale_bc) | (intros; apply GlobalTheory.KeyOriginBC.etale_bc  <;> assumption)
end

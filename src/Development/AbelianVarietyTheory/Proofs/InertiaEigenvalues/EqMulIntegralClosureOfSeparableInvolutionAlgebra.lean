module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra
noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLat

theorem isIntegral_pi' {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

section General

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]


variable (E) in
include E in
theorem exists_mul_isIntegral (y : A) : ∃ c : O, c ≠ 0 ∧ IsIntegral O (algebraMap O A c * y) := by
  have : Algebra.IsAlgebraic O A :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := A)).mpr inferInstance
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := O) y).exists_integral_multiple
  exact ⟨c, hc, by rwa [Algebra.smul_def] at h⟩

end General

section General2

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]


variable (E) in
include E in
theorem exists_mul_le_integral (J : Submodule O A) (hJ : J.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ z ∈ J, IsIntegral O (algebraMap O A c * z) := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose f hf0 hf using fun y : A => exists_mul_isIntegral (O := O) E y
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 fun y _ => hf0 y, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase s f hy, map_mul, mul_comm (algebraMap O A (f y)), mul_assoc]
    exact isIntegral_algebraMap.mul (hf y)
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | smul o x _ hx => rw [mul_smul_comm]; exact hx.smul o

theorem eq_mulLat_of_isPrincipalIdealRing [IsPrincipalIdealRing (integralClosure O A)]
    (J : Submodule O A) (hJ : IsLat O E J) (hst : ∀ a ∈ integralClosure O A, ∀ y ∈ J, a * y ∈ J) :
    ∃ a : Aˣ, J = mulLat O (a : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_mul_le_integral E J hJ.1
  set Λ := integralClosure O A

  have hcu : IsUnit (algebraMap O A c) := by
    rw [IsScalarTower.algebraMap_apply O E A]
    refine (IsUnit.mk0 _ ?_).map _
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  set C := algebraMap O A c
  let I : Ideal Λ :=
    { carrier := {l | ∃ z ∈ J, (l : A) = C * z}
      add_mem' := by
        rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
        exact ⟨x + y, J.add_mem hx hy, by rw [Subalgebra.coe_add, hax, hby, mul_add]⟩
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro a b ⟨x, hx, hbx⟩
        refine ⟨(a : A) * x, hst _ a.2 _ hx, ?_⟩
        rw [smul_eq_mul, Subalgebra.coe_mul, hbx]; ring }
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ l : Λ, l ∈ I ↔ ∃ m : Λ, m * b = l := by
    intro l; rw [hb]; exact Ideal.mem_span_singleton'
  have key : ∀ z, z ∈ J ↔ ∃ l ∈ Λ, C * z = b * l := by
    intro z; constructor
    · intro hz
      obtain ⟨m, hm⟩ := (hmemI ⟨C * z, hc z hz⟩).1 ⟨z, hz, rfl⟩
      have h2 := congrArg Subtype.val hm
      simp only [Subalgebra.coe_mul] at h2
      exact ⟨m, m.2, by rw [← h2, mul_comm]⟩
    · rintro ⟨l, hl, hzl⟩
      obtain ⟨z0, hz0, hbz0⟩ : b ∈ I := by rw [hb]; exact Ideal.mem_span_singleton_self b
      have : C * z = C * (l * z0) := by rw [hzl, hbz0]; ring
      rw [hcu.mul_left_cancel this]
      exact hst l hl z0 hz0

  have hbu : IsUnit (b : A) := by
    have hle : (J : Set A) ⊆ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      intro z hz
      obtain ⟨l, _, hzl⟩ := (key z).1 hz
      refine ⟨hcu.unit⁻¹ * l, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      calc (b : A) * (↑hcu.unit⁻¹ * l) = ↑hcu.unit⁻¹ * (b * l) := by ring
        _ = z := by rw [← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    have h1 : (1 : A) ∈ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      have := Submodule.span_le.2 hle
      rw [hJ.2] at this
      exact this Submodule.mem_top
    obtain ⟨w, hw⟩ := h1
    exact isUnit_iff_exists_inv.2 ⟨w, by simpa using hw⟩
  refine ⟨hcu.unit⁻¹ * hbu.unit, ?_⟩
  ext z
  rw [key z]
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule,
    Units.val_mul, IsUnit.unit_spec]
  constructor
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [mul_assoc, ← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [← hzl, ← mul_assoc, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

end General2

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra E A] [Algebra O A]
    [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O E (A ⧸ I.asIdeal)
    infer_instance
  haveI : Finite (MaximalSpectrum A) := inferInstance
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
    ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  intro K B hsep J hJ hst
  haveI : IsReduced B.A := ⟨fun a ha => Centraliser.eq_zero_of_isNilpotent B hsep a ha⟩
  haveI := isPrincipalIdealRing_integralClosure (O := K.O) (E := K.E) (A := B.A)
  exact eq_mulLat_of_isPrincipalIdealRing J hJ hst

end GlobalTheory.UnitLemma.PrincipalLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | exact GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | (intros; apply GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemOfSpanEqTop
namespace GlobalTheory.DenominatorOfSpan

open GlobalTheory.UnitLemma

theorem exists_smul_mem_of_span_eq_top {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (L : Submodule O A) (hL : Submodule.span E (L : Set A) = ⊤) (x : A) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set A) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul e y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have hs' : e * algebraMap O E (s : O) = algebraMap O E n := hs
    refine ⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩
    have h1 : (s : O) • e • y = n • y := by
      rw [← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.smul_mem n hay

theorem exists_denominator {K : UQ} (B : InvAlg K) (L : Submodule K.O B.A)
    (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L :=
  exists_smul_mem_of_span_eq_top L hL x

end GlobalTheory.DenominatorOfSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.Sandwich

theorem exists_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O)
    (ha : a ∈ IsLocalRing.maximalIdeal O) (d : O) (hd : d ≠ 0) : ∃ k : ℕ, d ∣ a ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have h1 : ϖ ∣ a := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ] at ha
    exact Ideal.mem_span_singleton.1 ha
  exact hk.dvd.trans (pow_dvd_pow_of_dvd h1 k)

theorem eventually_pow_mul_mem {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) (S : Submodule O A)
    (x : A) (d : O) (hd : d ≠ 0) (hx : d • x ∈ S) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → algebraMap O A a ^ n * x ∈ S := by
  obtain ⟨k, c, hc⟩ := exists_dvd_pow a ha d hd
  refine ⟨k, fun n hn => ?_⟩
  have e : algebraMap O A a ^ n * x = (a ^ (n - k) * c) • (d • x) := by
    rw [smul_smul, Algebra.smul_def, ← map_pow]
    congr 2
    rw [mul_assoc, mul_comm c d, ← hc, ← pow_add, Nat.sub_add_cancel hn]
  rw [e]
  exact S.smul_mem _ hx

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma.Sandwich

variable {K : UQ} (B : InvAlg K)

theorem exists_smul_isIntegral (x : B.A) : ∃ d : K.O, d ≠ 0 ∧ IsIntegral K.O (d • x) := by
  have h : IsAlgebraic K.E x := Algebra.IsAlgebraic.isAlgebraic x
  have h' : IsAlgebraic K.O x := (IsFractionRing.isAlgebraic_iff K.O K.E B.A).2 h
  obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
  exact ⟨d, hd, hi⟩

theorem exists_smul_mem (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.DenominatorOfSpan.exists_denominator
  | exact _root_.GlobalTheory.DenominatorOfSpan.exists_denominator
  | (apply _root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorOfSpan.exists_denominator ..)

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma.Sandwich

variable {K : UQ} (B : InvAlg K)

theorem exists_aeval (hP : B.P.Separable) (x : B.A) : ∃ f : K.E[X], x = aeval B.g f := by
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  refine ⟨∑ i, C (e.repr x i) * X ^ (i : ℕ), ?_⟩
  conv_lhs => rw [← e.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, he, Algebra.smul_def]

theorem traceForm_nondegenerate (hP : B.P.Separable) : (Algebra.traceForm K.E B.A).Nondegenerate := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply] using hw y)
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply, mul_comm] using hw y)

theorem integral_sub (hP : B.P.Separable) (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O)
    (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L := by
  classical
  have hnd := traceForm_nondegenerate B hP
  let b0 := Module.finBasis K.E B.A
  choose d hd0 hdi using fun i => exists_smul_isIntegral B (b0 i)
  have hu : ∀ i, IsUnit (algebraMap K.O K.E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral K.O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let bd := (Algebra.traceForm K.E B.A).dualBasis hnd b
  choose c hc0 hc using fun i => exists_smul_mem B L hL (bd i)
  choose k hk using fun i => eventually_pow_mul_mem a ha L (bd i) (c i) (hc0 i) (hc i)
  refine ⟨Finset.univ.sup k, fun n hn y hy => ?_⟩
  have hrep := bd.sum_repr y
  have hint : ∀ i, ∃ o : K.O, algebraMap K.O K.E o = bd.repr y i := by
    intro i
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A _ (hy.mul (hb i)))
  choose o ho using hint
  rw [← hrep, Finset.mul_sum]
  refine L.sum_mem fun i _ => ?_
  rw [← ho i, algebraMap_smul, mul_smul_comm]
  exact L.smul_mem _ (hk i n ((Finset.le_sup (Finset.mem_univ i)).trans hn))

theorem sub_integral (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O) (L : Submodule K.O B.A) (hL : L.FG) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ x : B.A, ∃ k : ℕ, ∀ n, k ≤ n →
      algebraMap K.O B.A a ^ n * x ∈ Subalgebra.toSubmodule (integralClosure K.O B.A) := by
    intro x
    obtain ⟨d, hd, hi⟩ := exists_smul_isIntegral B x
    exact eventually_pow_mul_mem a ha _ x d hd hi
  choose k hk using hk
  refine ⟨s.sup k, fun n hn y hy => ?_⟩
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hk x n ((Finset.le_sup hx).trans hn)
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [mul_add]; exact hx.add hz
  | smul r x _ hx => rw [mul_smul_comm, Algebra.smul_def]; exact isIntegral_algebraMap.mul hx

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma

theorem lattice_sandwich : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a →
    ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧
        ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  intro K B hB a ha L hL
  obtain ⟨m₁, h₁⟩ := Sandwich.integral_sub B hB.2 a ha.2.1 L hL.2
  obtain ⟨m₂, h₂⟩ := Sandwich.sub_integral B a ha.2.1 L hL.1
  exact ⟨max m₁ m₂, fun n hn => ⟨h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn)⟩⟩

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElementsStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLattice_sandwich_between_integral_elements : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧ ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  first | exact @GlobalTheory.UnitLemma.lattice_sandwich | exact GlobalTheory.UnitLemma.lattice_sandwich | (intros; apply GlobalTheory.UnitLemma.lattice_sandwich <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAlmostOntoOfLevels
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AlmostTrace

variable {l : ℕ} [Fact l.Prime]

theorem Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  unfold Ks Kinf
  exact sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ l ^ i = 1}
    {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} fun x hx => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _

theorem Ks_mono (K : FinExt l) : Monotone (Ks K) := by
  intro i j hij
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ l ^ i = 1}
    {x : Om l | x ^ l ^ j = 1} fun x hx => ?_) _
  obtain ⟨c, hc⟩ := pow_dvd_pow l hij
  have hx' : x ^ l ^ i = 1 := hx
  show x ^ l ^ j = 1
  rw [hc, pow_mul, hx', one_pow]

theorem Kinf_eq_iSup (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by
  refine le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)
  have h0 : K0 K ≤ Ks K 0 := by
    unfold Ks
    exact le_sup_left
  unfold Kinf
  refine sup_le (h0.trans (le_iSup (Ks K) 0)) ?_
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨j, hj⟩
  have hx : x ∈ Ks K j := by
    unfold Ks
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _)
      (IntermediateField.subset_adjoin _ _ hj)
  exact le_iSup (Ks K) j hx

theorem exists_mem_Ks (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  rw [Kinf_eq_iSup] at hx
  have h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hx
  rw [IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion] at h
  exact h

theorem Hinf_le_Gj (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by
  unfold Hinf Gj
  exact IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)

theorem exists_Gj_subset (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by
  have hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l))) := fun i =>
    InfiniteGalois.fixingSubgroup_isClosed (Ks K i)
  have hanti : Antitone fun i => ((Gj K i : Set (GQ l))) := fun i j hij =>
    IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)
  have hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅ := by
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hσU, hσ⟩
    apply hσU
    apply hH
    show σ ∈ (Kinf K).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_Ks K hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi
  obtain ⟨i₀, hi₀⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun i => (Gj K i : Set (GQ l))) hcl (Set.disjoint_iff_inter_eq_empty.mpr hinter) hanti.directed_ge
  refine ⟨i₀, fun i hi σ hσ => ?_⟩
  by_contra hσU
  have hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l)) := ⟨hσU, hanti hi hσ⟩
  exact Set.disjoint_left.1 hi₀ hmem.1 hmem.2

theorem sum_mem_Kinf (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) {b : Om l} (hb : b ∈ L) :
    ∑ s ∈ S, s b ∈ Kinf K := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup := fun s hs =>
    (hrep (h * s) (mul_mem hh (hS s hs))).exists
  choose! φ hφS hφF using hex
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_nbij φ hφS ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ he
    have h₁ := hφF s₁ hs₁
    have h₂ := hφF s₂ hs₂
    rw [he] at h₁
    have hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup := by
      have := mul_mem (inv_mem h₁) h₂
      rwa [show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group] at this
    exact (hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro t ht
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
    refine ⟨s, Finset.mem_coe.2 hs, ?_⟩
    have hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup := by
      have := inv_mem hsm
      rwa [show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group] at this
    exact (hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩
  · intro s hs
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb
    have key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b) := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]
    rw [hfix] at key
    exact key.symm

theorem exists_finite_level (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by
  classical
  have hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x := by
    intro s hs t ht hst
    by_contra hne
    push Not at hne
    apply hst
    have hmem : s⁻¹ * t ∈ L.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hne
    exact (hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩
  choose! xf hxL hxne using hsep
  let T : Finset (Om l) := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2
  have hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l)) := by
    intro s hs t ht hst
    simp only [T, Finset.coe_image, Finset.coe_filter]
    exact ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩
  let L' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  have hL'L : L'.1 ≤ L := by
    show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx
    obtain ⟨p, ⟨hp, hpne⟩, rfl⟩ := hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hxL p.1 hp1 p.2 hp2 hpne
  have : FiniteDimensional ℚ_[l] L'.1 := L'.2
  let U : Set (GQ l) := ⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}
  have hUo : IsOpen U := isOpen_biUnion fun s _ =>
    (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)
  have hHU : (Hinf K : Set (GQ l)) ⊆ U := by
    intro σ hσ
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep σ hσ
    exact Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)
  obtain ⟨i₀, hi₀⟩ := exists_Gj_subset K hUo hHU
  refine ⟨L', hL'L, i₀, fun i hi h hh => ?_⟩
  obtain ⟨s, hs, hsm⟩ := Set.mem_iUnion₂.1 (hi₀ i hi hh)
  have hsG : s⁻¹ * h ∈ Gj K i := mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hsm, hsG⟩
  · rintro t ⟨ht, htm⟩
    by_contra hts
    have htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_left htm
    have hm : t⁻¹ * s ∈ L'.1.fixingSubgroup := by
      have := mul_mem htm' (inv_mem hsm)
      rwa [show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group] at this
    have hxT : xf t s ∈ L'.1 := IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)
    exact hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)

theorem trace_almost_onto_of_levels
    (hd : ∀ (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l),
      (∀ s ∈ S, s ∈ Gj K i) →
      (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) →
      ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖)
    (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, zero_mem _, by simp, by simp [ha0]⟩
  obtain ⟨L', hL'L, i₀, hi₀⟩ := exists_finite_level K L S hS hrep
  have hε : 0 < 1 - ‖a‖ := by linarith
  obtain ⟨i₁, hi₁⟩ := hd K L' (1 - ‖a‖) hε
  obtain ⟨b₀, hb₀, hb₀1, htr⟩ := hi₁ (max i₀ i₁) (le_max_right _ _) S
    (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))
  have hb₀L : b₀ ∈ L := (sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀
  have htK : ∑ s ∈ S, s b₀ ∈ Kinf K := sum_mem_Kinf K L S hS hrep hb₀L
  set t := ∑ s ∈ S, s b₀ with ht
  have hta : ‖a‖ ≤ ‖t‖ := by linarith
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hta
    exact ha0 (norm_le_zero_iff.1 hta)
  have hc : a / t ∈ Kinf K := div_mem ha htK
  refine ⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩
  · rw [norm_mul, norm_div]
    have h1 : ‖a‖ / ‖t‖ ≤ 1 := (div_le_one (norm_pos_iff.2 ht0)).2 hta
    calc ‖a‖ / ‖t‖ * ‖b₀‖ ≤ 1 * 1 := mul_le_mul h1 hb₀1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hfix : ∀ s ∈ S, s (a / t) = a / t := fun s hs =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc
    rw [Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum,
      ← ht, div_mul_cancel₀ a ht0]

end GlobalTheory.Cyc.AlmostTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
open GlobalTheory.NL

namespace GlobalTheory.NL.Twist

variable {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]

theorem conv_mem_of_forall (w : PowerSeries L) (g : ℤ → M) (S : Submodule L M) (j : ℤ)
    (h : ∀ i : ℕ, g (j - i) ∈ S) : conv w g j ∈ S := by
  unfold conv
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem)
    (fun i => S.smul_mem _ (h i))

theorem conv_eq_sum (w : PowerSeries L) (g : ℤ → M) (m : ℤ) (hg : ∀ j < m, g j = 0) (k : ℤ) :
    conv w g k = ∑ i ∈ Finset.range ((k - m).toNat + 1), PowerSeries.coeff i w • g (k - i) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  apply hi
  have : g (k - i) = 0 := hg _ (by omega)
  simp [this]

theorem tri (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hSub : Monotone Sub) (y : ℕ)
    (f : ℤ → M) (hf : ∃ m : ℤ, ∀ j < m, f j = 0) (hfS : ∀ j, f j ∈ Sub j) (k : ℤ)
    (hk : ∀ j < k, f j ∈ Sub (j - y)) :
    (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧
    (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧
    (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧
    conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  obtain ⟨m, hm⟩ := hf
  have hg : ∀ j < m, (fun m => u ^ m • f m) j = 0 := fun j hj => by simp [hm j hj]
  refine ⟨⟨m, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · refine (Submodule.mem_bot L).1 (conv_mem_of_forall w _ ⊥ j (fun i => ?_))
    rw [hm _ (by omega), smul_zero]
    exact Submodule.zero_mem _
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) ≤ j) (hfS _)))
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) - y ≤ j - y) (hk _ (by omega))))
  · rw [conv_eq_sum w _ m hg k, Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 w • (u ^ (k - ((0 : ℕ) : ℤ)) • f (k - ((0 : ℕ) : ℤ))) -
        (PowerSeries.constantCoeff w * u ^ k) • f k = 0 := by
      simp [mul_smul]
    rw [add_sub_assoc, h0, add_zero]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
    exact hSub (by omega : k - ((i + 1 : ℕ) : ℤ) - y ≤ k - y) (hk _ (by omega))

end GlobalTheory.NL.Twist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurentStatement
open GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent : ∀ {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M] (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M), Monotone Sub → ∀ (y : ℕ) (f : ℤ → M), (∃ m : ℤ, ∀ j < m, f j = 0) → (∀ j, f j ∈ Sub j) → ∀ k : ℤ, (∀ j < k, f j ∈ Sub (j - y)) → (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧ (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧ (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧ conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  first | exact @GlobalTheory.NL.Twist.tri | exact GlobalTheory.NL.Twist.tri | (intros; apply GlobalTheory.NL.Twist.tri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOne
universe u_1

namespace GlobalTheory.PowerEqOneClose

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans ih

theorem norm_geom_sum_sub_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ih (norm_pow_sub_one_le u hu n))

theorem eq_one_of_pow_eq_one {K : Type u_1} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = (1 : ℝ)) (u : K) (hu : u ^ m = (1 : K)) (h : ‖u - (1 : K)‖ < (1 : ℝ)) :
    u = (1 : K) := by
  have hu1 : ‖u‖ ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le norm_one.le)
  have hs := norm_geom_sum_sub_le u hu1 m
  have hg : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  rcases mul_eq_zero.mp hg with h0 | h0
  · rw [h0, zero_sub, norm_neg, hm] at hs
    exact absurd h (not_lt.mpr hs)
  · exact sub_eq_zero.mp h0

end GlobalTheory.PowerEqOneClose
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertFix

theorem eq_one_of_pow_eq_one {K : Type*} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = 1) (u : K) (hu : u ^ m = 1) (h1 : ‖u - 1‖ < 1) : u = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | (apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one ..)

theorem inertia_fix : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ σ : GQ l,
    (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → ∀ x : Om l, x ^ l ^ n = x → σ x = x := by
  intro l hl n hn σ hσ x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hlp : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.out.one_lt
  obtain ⟨m, hm⟩ : ∃ m, l ^ n = m + 1 := ⟨l ^ n - 1, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hxm : x ^ m = 1 := by
    rw [hm, pow_succ] at hx
    exact mul_right_cancel₀ hx0 (by rw [hx, one_mul])
  have hnx : ‖x‖ = 1 := by
    have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).1 this
  have hcop : l.Coprime m := by
    have h : (l ^ n).Coprime m := by rw [hm]; simp
    exact Nat.Coprime.of_dvd_left (dvd_pow_self l hn.ne') h
  have hmn : ‖(m : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 hcop
  have hu : σ x / x = 1 := by
    refine eq_one_of_pow_eq_one m hmn _ ?_ ?_
    · rw [div_pow, ← map_pow, hxm, map_one, div_one]
    · have e : σ x / x - 1 = (σ x - x) / x := by field_simp
      rw [e, norm_div, hnx, div_one]
      exact hσ x hnx.le
  exact (div_eq_one_iff_eq hx0).1 hu

end GlobalTheory.InertFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsForallEqPowOfPowEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues.FrobPow

open Polynomial

theorem eq_of_pow_eq_self_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k]
    (φ : O →+* k) (q : ℕ) (hq : (q : k) = 0) {y z : O} (hy : y ^ q = y) (hz : z ^ q = z)
    (h : φ y = φ z) : y = z := by
  have h1 := Commute.geom_sum₂_mul (Commute.all y z) q
  rw [hy, hz] at h1
  have h2 : ((∑ i ∈ Finset.range q, y ^ i * z ^ (q - 1 - i)) - 1) * (y - z) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have h4 := congrArg φ h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_pow, map_one, map_zero, h] at h4
    rw [geom_sum₂_self, hq, zero_mul, zero_sub, neg_eq_zero] at h4
    exact one_ne_zero h4
  · exact sub_eq_zero.1 h3

theorem exists_forall_eq_pow_of_pow_eq_self (l : ℕ) [Fact l.Prime] {O k : Type} [CommRing O]
    [IsDomain O] [Field k] [CharP k l] (φ : O →+* k) (τ : O →+* O)
    (hτ : ∀ x, φ x = 0 → φ (τ x) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, ∀ x : O, x ^ l ^ n = x → τ x = x ^ l ^ a := by
  classical
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let S : Set O := {x | x ^ l ^ n = x}
  have hmon : ∀ (A : Type) [CommRing A] [Nontrivial A], (X ^ l ^ n - X : A[X]).Monic := by
    intro A _ _
    apply Monic.sub_of_left (monic_X_pow _)
    rw [degree_X, degree_X_pow]
    exact_mod_cast hq
  have hS : S.Finite := by
    refine (X ^ l ^ n - X : O[X]).roots.toFinset.finite_toSet.subset fun x hx => ?_
    have hx' : x ^ l ^ n = x := hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots (hmon O).ne_zero]
    simp [hx']
  have hint : ∀ x ∈ S, IsIntegral ℤ x := by
    intro x hx
    have hx' : x ^ l ^ n = x := hx
    exact ⟨X ^ l ^ n - X, hmon ℤ, by simp [hx']⟩
  have hfin : Module.Finite ℤ (Algebra.adjoin ℤ S) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hS hint
  let ι : Algebra.adjoin ℤ S →+* O := (Algebra.adjoin ℤ S).val.toRingHom
  obtain ⟨a, ha⟩ := GlobalTheory.exists_forall_eq_pow_of_ker_le l (Algebra.adjoin ℤ S) k (φ.comp ι)
    (φ.comp (τ.comp ι)) (fun x hx => hτ _ hx)
  refine ⟨a, fun x hx => ?_⟩
  have h1 : φ (τ x) = φ x ^ l ^ a := ha ⟨x, Algebra.subset_adjoin hx⟩
  refine eq_of_pow_eq_self_of_map_eq φ (l ^ n) ?_ ?_ ?_ ?_
  · rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne']
  · rw [← map_pow, hx]
  · rw [← pow_mul, mul_comm, pow_mul, hx]
  · rw [h1, map_pow]

theorem exists_gal_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) (σ : GQ l) :
    ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a := by
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let v : Valuation (Om l) NNReal := (PadicAlgCl.valued l).v
  have hv : ∀ x : Om l, v (σ x) = v x := fun x =>
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  let O : ValuationSubring (Om l) := v.valuationSubring
  have hO : ∀ x : Om l, x ∈ O ↔ v x ≤ 1 := fun x => Iff.rfl
  have hm : ∀ x : O, IsLocalRing.residue O x = 0 ↔ v x < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff _ v
  have hch : CharP (IsLocalRing.ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl).2 ?_
    rw [← map_natCast (IsLocalRing.residue O), hm]
    have : v (l : Om l) = 1 / (l : NNReal) := PadicAlgCl.valuation_p l
    rw [SubringClass.coe_natCast, this, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  let τ : O →+* O := (σ : Om l →+* Om l).restrict O O (fun x hx => by
    rw [hO] at hx ⊢
    exact (hv x).trans_le hx)
  have hτ : ∀ x : O, ((τ x : O) : Om l) = σ x := fun x => rfl
  obtain ⟨a, ha⟩ := exists_forall_eq_pow_of_pow_eq_self l (IsLocalRing.residue O) τ
    (fun x hx => by rw [hm] at hx ⊢; rw [hτ, hv]; exact hx) n hn
  refine ⟨a, fun x hx => ?_⟩
  have hxO : x ∈ O := by
    rw [hO]
    by_contra h
    have h' : 1 < v x := not_le.1 h
    have h2 : v x ^ 1 < v x ^ l ^ n := pow_lt_pow_right₀ h' hq
    rw [← map_pow, ← map_pow, hx, pow_one] at h2
    exact lt_irrefl _ h2
  have h3 := ha ⟨x, hxO⟩ (Subtype.ext (by simpa using hx))
  have h4 := congrArg (fun y : O => (y : Om l)) h3
  simpa [hτ] using h4

end GlobalTheory.InertiaEigenvalues.FrobPow
end

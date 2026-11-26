module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QBinomialSumCardQuotientSubspaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem tensor_exists_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_eq_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add (f := _)] at h0 h1
  exact ⟨h0, h1⟩

theorem mem_ALint_of_supported_at_split : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L),
    Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 →
    ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) →
    Valued.v (s.proj (L := L) z) ≤ 1 →
    Valued.v (s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 →
    z ∈ ReciprocityTheory.Aut.ALint L := by
  intro L _ _ _ s e he hc z hz hp hq
  have hne : (e : L) ≠ IsCMField.complexConj L (e : L) := by
    intro h
    rw [← h, he] at hc
    exact lt_irrefl _ hc
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), (e : L)] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * ((e : L) - IsCMField.complexConj L (e : L)) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = (e : L) := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have hoff : ∀ w, w ≠ s.v → A w = 0 ∧ B w = 0 := by
    intro w hw
    have h := hz w hw
    rw [hAB] at h
    apply tensor_decomp_eq_zero b
    rw [hb0, hb1]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have h1 : s.proj (L := L) z = A s.v + s.i (e : L) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L (e : L)) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : Valued.v (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact hc), he]
  have hBv : Valued.v (B s.v) ≤ 1 := by
    have hm : (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) * B s.v =
        s.proj (L := L) z - s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    have hv := congrArg Valued.v hm
    rw [map_mul, hu, one_mul] at hv
    rw [hv]
    exact Valuation.map_sub_le _ hp hq
  have hAv : Valued.v (A s.v) ≤ 1 := by
    have hm : A s.v = s.proj (L := L) z - s.i (e : L) * B s.v := by rw [h1]; ring
    rw [hm]
    refine Valuation.map_sub_le _ hp ?_
    rw [map_mul, he, one_mul]
    exact hBv
  have hAi : ∀ w, A w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hAv
    · rw [(hoff w hw).1]; exact zero_mem _
  have hBi : ∀ w, B w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hBv
    · rw [(hoff w hw).2]; exact zero_mem _
  have hsplit : ((e : L) ⊗ₜ[maximalRealSubfield L] B : ReciprocityTheory.Aut.AL L) =
      ((e : L) ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) *
        ((1 : L) ⊗ₜ[maximalRealSubfield L] B) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hAB, hsplit]
  refine Subring.add_mem _ (Subring.subset_closure (Or.inr ⟨A, hAi, rfl⟩))
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨B, hBi, rfl⟩)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegralStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_adele_split_place_support_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L), Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 → ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) → Valued.v (s.proj (L := L) z) ≤ 1 → Valued.v (s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 → z ∈ ReciprocityTheory.Aut.ALint L := by
  first | exact @GlobalTheory.mem_ALint_of_supported_at_split | exact GlobalTheory.mem_ALint_of_supported_at_split | (intros; apply GlobalTheory.mem_ALint_of_supported_at_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
open NumberField IsDedekindDomain Neutral.HilbertClassField

namespace GlobalTheory

theorem inertiaEl_eq_one_or_liesAbove : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω),
    ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  intro E Ω _ _ _ _ _ A g hg
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let φ : 𝓞 E →+* A := RingHom.codRestrict ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)) A hint
  let I : Ideal (𝓞 E) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ I := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, Ideal.mem_comap]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hint x, h⟩
  by_cases hbot : I = ⊥
  · left
    have hE : ∀ y : E, algebraMap E Ω y ∈ A := by
      intro y
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbn : algebraMap E Ω (algebraMap (𝓞 E) E b) ∉ A.nonunits := by
        rw [show algebraMap (𝓞 E) E b = (b : E) from rfl, hI, hbot, Ideal.mem_bot]; exact hb0
      have hbinv : (algebraMap E Ω (algebraMap (𝓞 E) E b))⁻¹ ∈ A := by
        rw [ValuationSubring.mem_nonunits_iff_or] at hbn
        push_neg at hbn; exact hbn.2
      rw [map_div₀, div_eq_mul_inv]
      exact mul_mem (hint a) hbinv
    have hall : ∀ x : Ω, x ∈ A := by
      intro x
      have hx : IsIntegral E x := ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x).isIntegral
      obtain ⟨p, hpm, hp⟩ := hx
      let ψ : E →+* A := RingHom.codRestrict (algebraMap E Ω) A hE
      have hcomp : (algebraMap A Ω).comp ψ = algebraMap E Ω := by ext; rfl
      have h1 : IsIntegral A x := ⟨p.map ψ, hpm.map ψ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
      rw [← hy]; exact y.2
    ext x
    have h := hg.2 x (hall x)
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · simpa [sub_eq_zero] using h
    · exact absurd (hall _) h
  · right
    exact ⟨⟨I, Ideal.IsPrime.comap φ, hbot⟩, fun x => hI x⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlaceStatement
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaElement_eq_one_or_liesAbove_finitePlace : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  first | exact @GlobalTheory.inertiaEl_eq_one_or_liesAbove | exact GlobalTheory.inertiaEl_eq_one_or_liesAbove | (intros; apply GlobalTheory.inertiaEl_eq_one_or_liesAbove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionHeisenbergInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNilpotentOfTracePow
open Polynomial

namespace GlobalTheory.NilpotentOfTracePowers

theorem trace_mul_aeval {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) (p : K[X]) :
    LinearMap.trace K V (f * aeval f p) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, ← pow_succ', h (i + 1) (by omega), smul_zero]

theorem exists_pow_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ (m : ℕ) (g : K[X]), f ^ m = f ^ m * aeval f (X * g) := by
  have hp : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly hp 0
  set m := rootMultiplicity 0 f.charpoly
  have hc : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h0
  have h0 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
  have hpoly : (X : K[X]) ^ m = X ^ m * (X * (C (-(q.coeff 0)⁻¹) * q.divX))
      + C (q.coeff 0)⁻¹ * f.charpoly := by
    have h1 : X * q.divX + C (q.coeff 0) = q := X_mul_divX_add q
    have h2 : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X]) := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    rw [map_zero, sub_zero] at hq
    rw [map_neg]
    linear_combination (-C (q.coeff 0)⁻¹) * hq + (C (q.coeff 0)⁻¹ * X ^ m) * h1 - X ^ m * h2
  refine ⟨m, C (-(q.coeff 0)⁻¹) * q.divX, ?_⟩
  have := congrArg (aeval f) hpoly
  rw [map_add (f := _), map_mul (aeval f) _ f.charpoly, h0, mul_zero, add_zero, map_mul, map_pow,
    aeval_X] at this
  exact this

theorem isNilpotent_of_trace_pow {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  obtain ⟨m, g, hm⟩ := exists_pow_eq f
  have hiter : ∀ j : ℕ, f ^ m = f ^ m * aeval f ((X * g) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', map_mul, ← mul_assoc, ← hm, ← ih]
  set e : Module.End K V := aeval f ((X * g) ^ (m + 1)) with he
  have he1 : e = aeval f (X * g ^ (m + 1)) * f ^ m := by
    have : (X * g) ^ (m + 1) = (X * g ^ (m + 1)) * X ^ m := by ring
    rw [he, this, map_mul (aeval f) _ (X ^ m), map_pow, aeval_X]
  have hid : IsIdempotentElem e := by
    unfold IsIdempotentElem
    conv_lhs => enter [1]; rw [he1]
    rw [mul_assoc, ← hiter (m + 1), ← he1]
  have htr : LinearMap.trace K V e = 0 := by
    have : (X * g) ^ (m + 1) = X * (g ^ (m + 1) * X ^ m) := by ring
    rw [he, this, map_mul, aeval_X]
    exact trace_mul_aeval f h _
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    { map_mem := fun x => LinearMap.mem_range_self e x
      map_id := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun hid x }
  have hrk : Module.finrank K (LinearMap.range e) = 0 := by
    have := hproj.trace
    rw [htr] at this
    exact_mod_cast this.symm
  have he0 : e = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrk)
  exact ⟨m, by rw [hiter (m + 1), ← he, he0, mul_zero]⟩

end GlobalTheory.NilpotentOfTracePowers
end

namespace GlobalTheory.UnipNormalTrace

open Module

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem isNilpotent_of_trace_pow_eq_zero {K : Type} [Field K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  first
  | exact @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | (apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow ..)

end GlobalTheory.UnipNormalTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAlternatingCardElementarySublatticesAbove
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAlternatingCardElementarySublatticesAbove
open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem sum_alt_card_subElem_ge : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ)
    (L M : Lat O K r), 1 ≤ n → M ∈ subIdx n L →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) *
      (({M' | M' ∈ subElem k L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
  intro O K _ _ _ _ _ _ _ r n L M hn hM
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set A : Submodule O (Fin r → K) := M.1 ⊔ m • L.1 with hA
  have hML : M.1 ≤ L.1 := hM.1
  have hAL : A ≤ L.1 := sup_le hML Submodule.smul_le_right
  set P : Submodule O L.1 := A.comap L.1.subtype with hP
  have hPA : P.map L.1.subtype = A := by rw [Submodule.map_comap_subtype, inf_eq_right.2 hAL]
  have htor : Module.IsTorsionBySet O (L.1 ⧸ P) (m : Set O) := by
    intro x a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul a.2 y.2)
  letI : Module (IsLocalRing.ResidueField O) (L.1 ⧸ P) := htor.module
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (L.1 ⧸ P) := htor.isScalarTower
  have hq2 : 2 ≤ qRes O := two_le_qRes
  have hqn : 0 < qRes O ^ n := pow_pos (by omega) _
  have hcardV : Nat.card (L.1 ⧸ P) = A.toAddSubgroup.relIndex L.1.toAddSubgroup := rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup A.toAddSubgroup L.1.toAddSubgroup
    ((Submodule.toAddSubgroup_le _ _).2 le_sup_left) ((Submodule.toAddSubgroup_le _ _).2 hAL)
  have hdvd : Nat.card (L.1 ⧸ P) ∣ qRes O ^ n := ⟨M.1.toAddSubgroup.relIndex A.toAddSubgroup, by
    rw [hcardV, mul_comm, hmul, hM.2]⟩
  haveI : Finite (L.1 ⧸ P) := Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hdvd hqn).ne'
  haveI : FiniteDimensional (IsLocalRing.ResidueField O) (L.1 ⧸ P) := Module.Finite.of_finite
  set d := Module.finrank (IsLocalRing.ResidueField O) (L.1 ⧸ P) with hd
  have hcardq : Nat.card (L.1 ⧸ P) = qRes O ^ d :=
    Module.natCard_eq_pow_finrank (K := IsLocalRing.ResidueField O)
  have hdn : d ≤ n := (Nat.pow_dvd_pow_iff_le_right (by omega)).1 (hcardq ▸ hdvd)
  have hd1 : 1 ≤ d := by
    by_contra h0
    have h0' : d = 0 := by omega
    have h1 : A.toAddSubgroup.relIndex L.1.toAddSubgroup = 1 := by
      rw [← hcardV, hcardq, h0', pow_zero]
    have h2 : L.1 ≤ M.1 ⊔ m • L.1 := (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 h1)
    have h3 : L.1 ≤ M.1 := Submodule.le_of_le_smul_of_le_jacobson_bot L.2.fg
      (by rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) h2
    have h4 : M.1.toAddSubgroup.relIndex L.1.toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 h3)
    rw [hM.2] at h4
    have := Nat.one_lt_pow (by omega : n ≠ 0) (by omega : 1 < qRes O)
    omega

  set k := IsLocalRing.ResidueField O
  set V := L.1 ⧸ P
  have hdV : Module.finrank k V = d := rfl
  let Φ : Submodule k V → Submodule O (Fin r → K) := fun W =>
    ((W.restrictScalars O).comap P.mkQ).map L.1.subtype
  have hPC : ∀ W : Submodule k V, P ≤ (W.restrictScalars O).comap P.mkQ := fun W x hx => by
    rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hx]
    exact zero_mem _
  have hΦA : ∀ W, A ≤ Φ W := fun W => hPA ▸ Submodule.map_mono (hPC W)
  have hΦL : ∀ W, Φ W ≤ L.1 := fun W => Submodule.map_subtype_le _ _
  have hlat : ∀ W, (Φ W).IsFullLattice K := fun W => by
    haveI := (maxMul L).2
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg K
      (show (maxMul L).1 ≤ Φ W from le_trans le_sup_right (hΦA W)) (L.2.fg.of_le (hΦL W))
  let f : Submodule k V → Lat O K r := fun W => ⟨Φ W, hlat W⟩
  have hinj : Function.Injective f := by
    intro W W' h
    have h1 : Φ W = Φ W' := congrArg Subtype.val h
    have h2 := Submodule.map_injective_of_injective L.1.injective_subtype h1
    have h3 := Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective P) h2
    exact Submodule.restrictScalars_injective O k V h3
  have hidx : ∀ W : Submodule k V,
      (Φ W).toAddSubgroup.relIndex L.1.toAddSubgroup = qRes O ^ Module.finrank k (V ⧸ W) := by
    intro W
    change Nat.card (L.1 ⧸ (Φ W).comap L.1.subtype) = _
    rw [Submodule.comap_map_eq_of_injective L.1.injective_subtype,
      ← Nat.card_congr (Submodule.quotientQuotientEquivQuotient P _ (hPC W)).toEquiv,
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective P),
      Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv O W).toEquiv,
      Module.natCard_eq_pow_finrank (K := k)]
    rfl
  have hset : ∀ j, ({M' | M' ∈ subElem j L ∧ M.1 ≤ M'.1} : Set (Lat O K r)) =
      f '' {W | Module.finrank k (V ⧸ W) = j} := by
    intro j
    ext M'
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨⟨hle, hi⟩, hmL⟩, hMM⟩
      set C := M'.1.comap L.1.subtype
      have hPC' : P ≤ C := Submodule.comap_mono (sup_le hMM hmL)
      let Wk : Submodule k V :=
        { (C.map P.mkQ).toAddSubmonoid with
          smul_mem' := fun c x hx => by
            obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
            have e : (IsLocalRing.residue O a) • x = a • x := htor.mk_smul a x
            rw [e]
            exact (C.map P.mkQ).smul_mem a hx }
      have hWr : Wk.restrictScalars O = C.map P.mkQ := rfl
      have heq : Φ Wk = M'.1 := by
        change ((Wk.restrictScalars O).comap P.mkQ).map L.1.subtype = M'.1
        rw [hWr, Submodule.comap_map_mkQ, sup_eq_right.2 hPC', Submodule.map_comap_subtype,
          inf_eq_right.2 hle]
      refine ⟨Wk, ?_, Subtype.ext heq⟩
      have h := hidx Wk
      rw [heq, hi] at h
      exact (Nat.pow_right_injective hq2 h).symm
    · rintro ⟨W, hW, rfl⟩
      exact ⟨⟨⟨hΦL W, (hidx W).trans (by rw [hW])⟩, le_trans le_sup_right (hΦA W)⟩,
        le_trans le_sup_left (hΦA W)⟩
  have hcount : ∀ j, (({M' | M' ∈ subElem j L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) =
      (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) := by
    intro j
    rw [hset j, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
    rfl
  have hI := GlobalTheory.T.qBinomial_sum_card_quotient_subspaces k V 1
  rw [Finset.prod_eq_zero (Finset.mem_range.2 (by rw [hdV]; omega : 0 < Module.finrank k V)) (by simp)] at hI
  have hqk : (Nat.card k : ℂ) = (qRes O : ℂ) := rfl
  simp only [one_pow, mul_one, hqk, hdV] at hI
  have hzero : ∀ x ∈ Finset.range (n + 1), x ∉ Finset.range (d + 1) →
      (-1 : ℂ) ^ x * (qRes O : ℂ) ^ (x * (x - 1) / 2) *
        (({M' | M' ∈ subElem x L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
    intro x _ hx
    rw [Finset.mem_range] at hx
    haveI : IsEmpty {W : Submodule k V // Module.finrank k (V ⧸ W) = x} :=
      ⟨fun ⟨W, hW⟩ => by have := Submodule.finrank_quotient_le W; rw [hdV] at this; omega⟩
    rw [hcount, Nat.card_of_isEmpty]
    simp
  rw [← Finset.sum_subset (fun x hx => Finset.mem_range.2 (by have := Finset.mem_range.1 hx; omega)) hzero]
  simp only [hcount]
  exact hI

end GlobalTheory.LatHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAlternatingCardElementarySublatticesAboveStatement
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_alternating_card_elementarySublattices_above : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ) (L M : Lat O K r), 1 ≤ n → M ∈ subIdx n L → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * (({M' | M' ∈ subElem k L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
  first | exact @GlobalTheory.LatHecke.sum_alt_card_subElem_ge | exact GlobalTheory.LatHecke.sum_alt_card_subElem_ge | (intros; apply GlobalTheory.LatHecke.sum_alt_card_subElem_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentity
open GlobalTheory.LatHecke

namespace GlobalTheory.HeckeSeries

open Classical

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_subIdx_sub_iff {n k : ℕ} (hk : k ≤ n) {L M' M : Lat O K r}
    (hM' : M' ∈ subElem k L) :
    M ∈ subIdx (n - k) M' ↔ M ∈ subIdx n L ∧ M.1 ≤ M'.1 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := hM'
  have hq : 0 < qRes O := lt_of_lt_of_le two_pos two_le_qRes
  have hpow : qRes O ^ n = qRes O ^ (n - k) * qRes O ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  constructor
  · rintro ⟨h3, h4⟩
    refine ⟨⟨h3.trans h1, ?_⟩, h3⟩
    rw [← AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h3 h1, h4, h2, hpow]
  · rintro ⟨⟨-, h4⟩, h5⟩
    refine ⟨h5, ?_⟩
    have h := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h5 h1
    rw [h4, h2, hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq k) h

theorem heckeElem_heckeAll_eq {E : Type} [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E)
    {n k : ℕ} (hk : k ≤ n) (L : Lat O K r) :
    heckeElem k (heckeAll (n - k) φ) L = ∑ M ∈ (subIdx_finite n L).toFinset,
      ((((subElem_finite k L).toFinset.filter (fun M' => M.1 ≤ M'.1)).card : ℂ)) • φ M := by
  rw [heckeElem_eq_sum]
  have h : ∀ M' ∈ (subElem_finite k L).toFinset, heckeAll (n - k) φ M' =
      ∑ M ∈ (subIdx_finite n L).toFinset, if M.1 ≤ M'.1 then φ M else 0 := by
    intro M' hM'
    rw [heckeAll_eq_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext M
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact mem_subIdx_sub_iff hk ((Set.Finite.mem_toFinset _).1 hM')
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem heckeSeries_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r),
    1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) •
      heckeElem k (heckeAll (n - k) φ) L = 0 := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ n L hn
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [heckeElem_heckeAll_eq φ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) L])]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [← Finset.sum_smul]
  have hM' : M ∈ subIdx n L := (Set.Finite.mem_toFinset _).1 hM
  have h := GlobalTheory.T.sum_alternating_card_elementarySublattices_above O K r n L M hn hM'
  convert zero_smul ℂ (φ M) using 2
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext M'
  simp

end GlobalTheory.HeckeSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentityStatement
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_alternating_series_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r), 1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) • heckeElem k (heckeAll (n - k) φ) L = 0 := by
  first | exact @GlobalTheory.HeckeSeries.heckeSeries_identity | exact GlobalTheory.HeckeSeries.heckeSeries_identity | (intros; apply GlobalTheory.HeckeSeries.heckeSeries_identity <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)

theorem τ_self (y : N.X) : N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) := by
  have a := N.τ_add_left y (-y) y
  rw [add_neg_cancel, N.τ_zero_left, one_mul, N.c_neg] at a
  have b := N.ψ_add (-y) y
  rw [neg_add_cancel, N.ψ_zero] at b
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul (N.even y)
  apply Additive.ofMul.injective
  simp only [dbl, sq, ofMul_mul, ofMul_div, ofMul_one] at a' b' c' ⊢
  linear_combination (norm := abel) -a' + b' + c'

theorem s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have m := g.mult (n • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [succ_nsmul, cubN, Finset.prod_range_succ, one_mul, pow_succ, ← ih, mul_right_comm _ _ (g.s y), ← m,
      ← mul_assoc, mul_right_comm]

theorem ψ_nsmul (n : ℕ) (y : N.X) : N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) := by
  induction n with
  | zero => simp [mulq]
  | succ n ih =>
    have a := s_nsmul N (N.io y) n y
    rw [N.io_s, N.io_s, N.io_b, τ_self, N.τ_symm] at a
    rw [mulq] at ih
    rw [succ_nsmul, N.ψ_add, mulq, Finset.prod_range_succ, show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring,
      pow_succ, pow_add, pow_mul, ← ih]
    rw [mul_pow] at a
    have a' := congrArg Additive.ofMul a
    apply Additive.ofMul.injective
    generalize (N.ψ y ^ 2) ^ n = u at a' ⊢
    generalize dbl N.θ N.σ (N.c y) ^ n = v at a' ⊢
    simp only [ofMul_mul, ofMul_div] at a' ⊢
    linear_combination (norm := abel) a'

theorem main : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X),
    N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧
    ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧
      (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n :=
  fun _ _ N n y => ⟨τ_self N y, ψ_nsmul N n y, fun g => ⟨s_nsmul N g n y, g.pow_s n y⟩⟩

end GlobalTheory.PsiQuadratic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinearStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.degenerationData_psi_quadratic_generators_linear : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X), N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧ ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧ (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n := by
  first | exact @GlobalTheory.PsiQuadratic.main | exact GlobalTheory.PsiQuadratic.main | (intros; apply GlobalTheory.PsiQuadratic.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomAndIsAdicCompleteOfFiniteDvr
namespace GlobalTheory

open IsLocalRing in
private lemma exists_pow_maximalIdeal_eq_span {V V' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Algebra V V'] [IsLocalHom (algebraMap V V')] (hinj : Function.Injective (algebraMap V V'))
    {ϖ : V} (hϖ : Irreducible ϖ) :
    ∃ e : ℕ, 0 < e ∧ ∀ n, maximalIdeal V' ^ (e * n) = Ideal.span {algebraMap V V' ϖ ^ n} := by
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have h0 : algebraMap V V' ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V V')]
    exact fun h => hϖ.ne_zero (hinj h)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap V V' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  refine ⟨e, Nat.pos_of_ne_zero fun he => hnu ?_, fun n => ?_⟩
  · rw [hu, he, pow_zero, mul_one]; exact u.isUnit
  · rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      ← Units.val_pow_eq_pow_val, Ideal.span_singleton_mul_left_unit (u ^ n).isUnit]

open IsLocalRing in
private lemma mem_span_pow_iff_repr {V V' : Type} [CommRing V] [CommRing V'] [Algebra V V']
    {ι : Type} [Fintype ι] (b : Module.Basis ι V V') (ϖ : V) (j : ℕ) (x : V') :
    x ∈ Ideal.span {algebraMap V V' ϖ ^ j} ↔ ∀ i, b.repr x i ∈ Ideal.span {ϖ ^ j} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨b.repr y i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      smul_eq_mul, mul_comm]
  · intro h
    choose c hc using h
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, smul_smul, mul_comm (ϖ ^ j)]


open IsLocalRing in
theorem _root_.GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr :
    ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CommRing V'] [IsDomain V']
      [IsDiscreteValuationRing V'] [Algebra V V'], Module.Finite V V' →
      Function.Injective (algebraMap V V') →
      IsLocalHom (algebraMap V V') ∧ IsAdicComplete (IsLocalRing.maximalIdeal V') V' := by
  intro V V' _ _ _ _ _ _ _ _ hfin hinj
  have hloc : IsLocalHom (algebraMap V V') :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  refine ⟨hloc, ?_⟩
  haveI : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective V V').2 hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨e, he, hpow⟩ := exists_pow_maximalIdeal_eq_span hinj hϖ
  let b := Module.Free.chooseBasis V V'
  have hV : ∀ j, (maximalIdeal V ^ j • ⊤ : Submodule V V) = Ideal.span {ϖ ^ j} := by
    intro j
    rw [smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hV' : ∀ n, (maximalIdeal V' ^ n • ⊤ : Submodule V' V') = maximalIdeal V' ^ n := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
  haveI hH : IsHausdorff (maximalIdeal V') V' :=
    IsHausdorff.of_isLocalRing (maximalIdeal V') V' (IsLocalRing.maximalIdeal.isMaximal V').ne_top
  have hP : IsPrecomplete (maximalIdeal V') V' := by
    rw [isPrecomplete_iff]
    intro f hf
    have hcoord : ∀ i : Module.Free.ChooseBasisIndex V V', ∀ {m n : ℕ}, m ≤ n →
        b.repr (f (e * m)) i ≡ b.repr (f (e * n)) i
          [SMOD maximalIdeal V ^ m • (⊤ : Submodule V V)] := by
      intro i m n hmn
      have h := hf (Nat.mul_le_mul_left e hmn)
      rw [hV', SModEq.sub_mem, hpow, mem_span_pow_iff_repr b] at h
      rw [hV, SModEq.sub_mem, ← Finsupp.sub_apply, ← map_sub]
      exact h i
    choose L hL using fun i =>
      (isPrecomplete_iff.1 (inferInstance : IsPrecomplete (maximalIdeal V) V)) _ (hcoord i)
    refine ⟨b.equivFun.symm L, fun n => ?_⟩
    have h1 : f n ≡ f (e * n) [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] :=
      hf (Nat.le_mul_of_pos_left n he)
    have h2 : f (e * n) ≡ b.equivFun.symm L [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] := by
      rw [hV', SModEq.sub_mem]
      refine Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he) ?_
      rw [hpow, mem_span_pow_iff_repr b]
      intro i
      have hi := hL i n
      rw [hV, SModEq.sub_mem] at hi
      rw [map_sub, Finsupp.sub_apply, ← b.equivFun_apply (b.equivFun.symm L),
        LinearEquiv.apply_symm_apply]
      exact hi
    exact h1.trans h2
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvr
namespace GlobalTheory

namespace IntegralOverComplete

open IsLocalRing Polynomial

theorem isLocalHom_val {W R : Type} [CommRing W] [CommRing R] [Algebra W R]
    [Algebra.IsIntegral W R] (W' : Subalgebra W R) : IsLocalHom W'.val.toRingHom := by
  have : Algebra.IsIntegral W' R := Algebra.IsIntegral.tower_top W
  have : FaithfulSMul W' R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  exact inferInstanceAs (IsLocalHom (algebraMap W' R))

theorem exists_subalgebra (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra W R] [FaithfulSMul W R] [Algebra.IsIntegral W R]
    (s : Finset R) :
    ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ Module.Finite W W' ∧
      IsLocalHom W'.val.toRingHom := by
  classical
  let F := FractionRing R
  let j : R →ₐ[W] F := IsScalarTower.toAlgHom W R F
  have hj : Function.Injective j := IsFractionRing.injective R F
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq W R F]
    exact hj.comp (FaithfulSMul.algebraMap_injective W R))
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  have : Algebra.IsAlgebraic W F := Algebra.IsAlgebraic.trans W R F
  obtain ⟨V, hV, -, -, hfin, -, -, -, hs⟩ :=
    exists_complete_dvr_finite_subalgebra W F (s.image j)
  have hle : V ≤ j.range := fun x hx => by
    have h1 : IsIntegral W x :=
      (Algebra.IsIntegral.isIntegral (R := W) (⟨x, hx⟩ : V)).map V.val
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := R))
  let W' : Subalgebra W R := V.comap j
  have hmap : W'.map j = V := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx
      obtain ⟨y, rfl⟩ := hle hx
      exact ⟨y, hx, rfl⟩
  let e : V ≃ₐ[W] W' :=
    ((Subalgebra.equivMapOfInjective W' j hj).trans (Subalgebra.equivOfEq _ _ hmap)).symm
  have hd : IsDiscreteValuationRing W' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hf : Module.Finite W W' := Module.Finite.equiv e.toLinearEquiv
  refine ⟨W', hd, fun x hx => ?_,
    CompleteFiniteExtension.isAdicComplete_of_finite_local W W', hf, isLocalHom_val W'⟩
  exact hs _ (Finset.mem_image_of_mem j hx) ((Algebra.IsIntegral.isIntegral x).map j)

theorem henselian_of_union (W R : Type) [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (h : ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsLocalRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ IsLocalHom W'.val.toRingHom) :
    HenselianLocalRing R := by
  classical
  refine ⟨fun f hf a₀ h0 hu => ?_⟩
  obtain ⟨V, _, hs, hc, hl⟩ := h (insert a₀ f.coeffs ∪ {0})
  let i : V →+* R := V.val.toRingHom
  have hlift : f ∈ lifts i := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : f.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨f.coeff n, hs (by simp [coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  obtain ⟨b, rfl⟩ : ∃ b : V, i b = a₀ := ⟨⟨a₀, hs (by simp)⟩, rfl⟩
  subst hg
  rw [eval_map, eval₂_at_apply] at h0
  rw [derivative_map, eval_map, eval₂_at_apply] at hu
  have h0' : g.eval b ∈ maximalIdeal V := fun hu' => h0 (hu'.map i)
  have hu' : IsUnit (g.derivative.eval b) := IsLocalHom.map_nonunit _ hu
  obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian (I := maximalIdeal V) g hgm b h0' (hu'.map _)
  refine ⟨i a, ?_, ?_⟩
  · rw [IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact fun hh => hab (IsLocalHom.map_nonunit _ hh)

end IntegralOverComplete

theorem henselian_and_union_of_isIntegral_complete :
    ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) →
      Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧
      ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'),
        (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧
        Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by
  intro W R _ _ _ _ _ _ _ _ _ hinj hint
  have : FaithfulSMul W R := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine ⟨inferInstance, IntegralOverComplete.henselian_of_union W R fun s => ?_,
    IntegralOverComplete.exists_subalgebra W R⟩
  obtain ⟨V, hV, h1, h2, -, h3⟩ := IntegralOverComplete.exists_subalgebra W R s
  exact ⟨V, inferInstance, h1, h2, h3⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr : ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) → Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧ ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧ Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by
  first | exact @GlobalTheory.henselian_and_union_of_isIntegral_complete | exact GlobalTheory.henselian_and_union_of_isIntegral_complete | (intros; apply GlobalTheory.henselian_and_union_of_isIntegral_complete <;> assumption)
end
end

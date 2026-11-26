module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
private lemma natAbs_discr_pow_finrank_le_natAbs_discr (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    (discr K).natAbs ^ Module.finrank K L ≤ (discr L).natAbs := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) ?_
  rw [h]
  exact Dvd.intro_left _ rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    Real.log (Module.finrank ℚ K) ≤ Real.log (Module.finrank ℚ L) ∧
      Real.log |((NumberField.discr K : ℤ) : ℝ)| / Module.finrank ℚ K ≤
        Real.log |((NumberField.discr L : ℤ) : ℝ)| / Module.finrank ℚ L := by
  have hmul := Module.finrank_mul_finrank ℚ K L
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hm : 0 < Module.finrank K L := Module.finrank_pos
  have hnR : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast hn
  have hmR : (0 : ℝ) < Module.finrank K L := by exact_mod_cast hm
  have hNR : ((Module.finrank ℚ L : ℕ) : ℝ) = Module.finrank ℚ K * Module.finrank K L := by
    rw [← hmul]; push_cast; ring
  constructor
  · apply Real.log_le_log hnR
    rw [hNR]
    have : (1 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hm
    nlinarith
  · have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
      have := discr_ne_zero K
      positivity
    have hle : |((discr K : ℤ) : ℝ)| ^ Module.finrank K L ≤ |((discr L : ℤ) : ℝ)| := by
      have h := natAbs_discr_pow_finrank_le_natAbs_discr K L
      have h' : (((discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) ≤ ((discr L).natAbs : ℝ) := by
        exact_mod_cast h
      simpa [Nat.cast_natAbs, Int.cast_abs] using h'
    have hlog : (Module.finrank K L : ℝ) * Real.log |((discr K : ℤ) : ℝ)| ≤
        Real.log |((discr L : ℤ) : ℝ)| := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hK _) hle
    rw [hNR, div_le_div_iff₀ hnR (mul_pos hnR hmR)]
    nlinarith

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.sz_mono_and_of_le :
    (∀ (F : IntermediateField ℚ ℂ) (a b a' b' : ℝ), _root_.GlobalTheory.FieldSize.Sz F a b →
        a ≤ a' → b ≤ b' → _root_.GlobalTheory.FieldSize.Sz F a' b') ∧
      ∀ (F F' : IntermediateField ℚ ℂ) (a b : ℝ), F ≤ F' →
        _root_.GlobalTheory.FieldSize.Sz F' a b → _root_.GlobalTheory.FieldSize.Sz F a b := by
  constructor
  · rintro F a b a' b' ⟨hF, h1, h2⟩ ha hb
    exact ⟨hF, h1.trans ha, h2.trans hb⟩
  · rintro F F' a b hFF' ⟨hF', h1, h2⟩
    haveI : FiniteDimensional ℚ F' := hF'
    haveI hF : FiniteDimensional ℚ F :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hFF').toLinearMap
        (IntermediateField.inclusion hFF').injective
    haveI : NumberField F := ⟨⟩
    haveI : NumberField F' := ⟨⟩
    letI : Algebra F F' := (IntermediateField.inclusion hFF').toRingHom.toAlgebra
    obtain ⟨g1, g2⟩ := _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower F F'
    exact ⟨hF, g1.trans h1, g2.trans h2⟩

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateField
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateField
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DiffBaseChange

theorem sum_emb_mul_dual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ E) (σ τ : E →ₐ[ℚ] ℂ) [Decidable (σ = τ)] :
    ∑ i, σ (b i) * τ (b.traceDual i) = if σ = τ then 1 else 0 := by
  classical
  have hli := Fintype.linearIndependent_iff.1 (linearIndependent_algHom_toLinearMap ℚ E ℂ)
    (fun σ : E →ₐ[ℚ] ℂ => (∑ i, σ (b i) * τ (b.traceDual i)) - if σ = τ then 1 else 0) ?_ σ
  · convert sub_eq_zero.1 hli
  · ext x
    have h1 : τ x = ∑ i, (∑ σ : E →ₐ[ℚ] ℂ, σ (x * b i)) * τ (b.traceDual i) := by
      conv_lhs => rw [← b.traceDual.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, τ.commutes, b.traceDual_repr_apply, Algebra.traceForm_apply,
        ← trace_eq_sum_embeddings ℂ]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      smul_eq_mul, LinearMap.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1, sub_eq_zero]
    simp only [Finset.sum_mul, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eq_sum_trace_mul_dual {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra F L] (j : E →+* L) (u : L →+* ℂ)
    (hgen : ∀ ρ : L →+* ℂ, (∀ x : F, ρ (algebraMap F L x) = u (algebraMap F L x)) →
      (∀ x : E, ρ (j x) = u (j x)) → ρ = u)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (y : L) :
    y = ∑ i, algebraMap F L (Algebra.trace F L (y * j (b i))) * j (b.traceDual i) := by
  classical
  letI : Algebra L ℂ := u.toAlgebra
  letI : Algebra F ℂ := (u.comp (algebraMap F L)).toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply u.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have h1 : ∀ i, u (algebraMap F L (Algebra.trace F L (y * j (b i))) * j (b.traceDual i)) =
      ∑ ρ : L →ₐ[F] ℂ, ρ y * (ρ (j (b i)) * u (j (b.traceDual i))) := by
    intro i
    have := trace_eq_sum_embeddings (K := F) ℂ (x := y * j (b i))
    rw [map_mul]
    change algebraMap F ℂ _ * _ = _
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => by rw [map_mul, mul_assoc]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ ρ : L →ₐ[F] ℂ, ∑ i, ρ y * (ρ (j (b i)) * u (j (b.traceDual i))) =
      if ρ = IsScalarTower.toAlgHom F L ℂ then u y else 0 := by
    intro ρ
    rw [← Finset.mul_sum]
    have := sum_emb_mul_dual b ((ρ : L →+* ℂ).comp j).toRatAlgHom (u.comp j).toRatAlgHom
    simp only [RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.coe_coe] at this
    rw [this]
    by_cases h : ρ = IsScalarTower.toAlgHom F L ℂ
    · subst h
      rw [if_pos rfl, if_pos (by rfl), mul_one]
      rfl
    · rw [if_neg h, if_neg, mul_zero]
      intro h'
      apply h
      have := hgen (ρ : L →+* ℂ) (fun x => ρ.commutes x) (fun x => DFunLike.congr_fun h' x)
      ext x
      exact DFunLike.congr_fun this x
  simp [h2]

theorem map_different_le {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra F L] (j : E →+* L) (u : L →+* ℂ)
    (hgen : ∀ ρ : L →+* ℂ, (∀ x : F, ρ (algebraMap F L x) = u (algebraMap F L x)) →
      (∀ x : E, ρ (j x) = u (j x)) → ρ = u) :
    (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom j) ≤ differentIdeal (𝓞 F) (𝓞 L) := by
  classical
  rw [Ideal.map_le_iff_le_comap]
  intro δ hδ
  rw [Ideal.mem_comap]
  have h1 : algebraMap (𝓞 E) E δ ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ (𝓞 E), Submodule.mem_div_iff_forall_mul_mem] at h1
  have hb : ∀ i, (integralBasis E).traceDual i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    intro i
    rw [← Submodule.restrictScalars_mem ℤ, Submodule.traceDual_span_of_basis ℤ _ (integralBasis E)]
    · exact Submodule.subset_span ⟨i, rfl⟩
    · ext x
      rw [mem_span_integralBasis, Submodule.restrictScalars_mem, Submodule.mem_one]
      rfl
  suffices h : algebraMap (𝓞 L) L (RingOfIntegers.mapRingHom j δ) ∈
      IsLocalization.coeSubmodule L (differentIdeal (𝓞 F) (𝓞 L)) by
    obtain ⟨y, hy, hyx⟩ := (IsLocalization.mem_coeSubmodule _ _).1 h
    obtain rfl := IsFractionRing.injective (𝓞 L) L hyx
    exact hy
  rw [coeSubmodule_differentIdeal (𝓞 F) F (𝓞 L), Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [eq_sum_trace_mul_dual (F := F) j u hgen (integralBasis E) y, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (h1 _ (hb i))
  obtain ⟨t, ht⟩ := Submodule.mem_traceDual.1 hy (j (integralBasis E i))
    (Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom j (RingOfIntegers.basis E i), by
      rw [integralBasis_apply]; rfl⟩)
  rw [Algebra.traceForm_apply] at ht
  refine Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 L) t * RingOfIntegers.mapRingHom j c, ?_⟩
  have e1 : ∀ z : 𝓞 E, algebraMap (𝓞 L) L (RingOfIntegers.mapRingHom j z) = j (algebraMap (𝓞 E) E z) := fun _ => rfl
  rw [map_mul, e1, e1, hc, map_mul, ← ht, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  ring

theorem map_different_le_sup (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')] :
    letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    (differentIdeal ℤ (𝓞 F')).map
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤
      differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  refine map_different_le (F := F) _ (F ⊔ F').val.toRingHom fun ρ h1 h2 => ?_
  ext ⟨x, hx⟩
  change ρ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h1 ⟨x, hx⟩
    · exact h2 ⟨x, hx⟩
  | algebraMap q => exact h1 (algebraMap ℚ F q)
  | add x y hx hy ihx ihy => exact (map_add ρ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [ihx, ihy])
  | inv x hx ih => exact (map_inv₀ ρ ⟨x, hx⟩).trans (by rw [ih])
  | mul x y hx hy ihx ihy => exact (map_mul ρ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [ihx, ihy])

end GlobalTheory.DiffBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateFieldStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_different_le_different_sup_intermediateField : ∀ (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')], letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra; (differentIdeal ℤ (𝓞 F')).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤ differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  first | exact @GlobalTheory.DiffBaseChange.map_different_le_sup | exact GlobalTheory.DiffBaseChange.map_different_le_sup | (intros; apply GlobalTheory.DiffBaseChange.map_different_le_sup <;> assumption)
end
end

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

namespace GlobalTheory.FieldSize

theorem natAbs_discr_le_of_map_different_le (F F' L : Type) [Field F] [Field F'] [Field L]
    [NumberField F] [NumberField F'] [NumberField L] [Algebra F L] [Algebra F' L]
    (h : (differentIdeal ℤ (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) ≤ differentIdeal (𝓞 F) (𝓞 L)) :
    (discr L).natAbs ≤ (discr F').natAbs ^ Module.finrank F' L * (discr F).natAbs ^ Module.finrank F L := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)]
  refine Nat.mul_le_mul_right _ ?_
  have h1 := Ideal.absNorm_dvd_absNorm_of_le h
  rw [Ideal.absNorm_algebraMap (𝓞 F') (𝓞 L), absNorm_differentIdeal F' (𝓞 F')] at h1
  have h2 : Module.finrank (𝓞 F') (𝓞 L) = Module.finrank F' L :=
    (IsFractionRing.finrank_eq (𝓞 F') F' (𝓞 L) L).symm
  rw [h2] at h1
  exact Nat.le_of_dvd (pow_pos (Int.natAbs_pos.2 (discr_ne_zero F')) _) h1

theorem log_discr_div_le (F F' L : Type) [Field F] [Field F'] [Field L]
    [NumberField F] [NumberField F'] [NumberField L] [Algebra F L] [Algebra F' L]
    (h : (differentIdeal ℤ (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) ≤ differentIdeal (𝓞 F) (𝓞 L)) :
    Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤
      Real.log |((discr F : ℤ) : ℝ)| / Module.finrank ℚ F + Real.log |((discr F' : ℤ) : ℝ)| / Module.finrank ℚ F' := by
  have h1 := natAbs_discr_le_of_map_different_le F F' L h
  have h2 : |((discr L : ℤ) : ℝ)| ≤ |((discr F' : ℤ) : ℝ)| ^ Module.finrank F' L * |((discr F : ℤ) : ℝ)| ^ Module.finrank F L := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    simpa [Nat.cast_natAbs] using this
  have p : ∀ (K : Type) [Field K] [NumberField K], (0 : ℝ) < |((discr K : ℤ) : ℝ)| := fun K _ _ =>
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have h3 := Real.log_le_log (p L) h2
  rw [Real.log_mul (pow_pos (p F') _).ne' (pow_pos (p F) _).ne', Real.log_pow, Real.log_pow] at h3
  have e1 : (Module.finrank ℚ L : ℝ) = Module.finrank ℚ F * Module.finrank F L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F L).symm
  have e2 : (Module.finrank ℚ L : ℝ) = Module.finrank ℚ F' * Module.finrank F' L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F' L).symm
  have q : ∀ (K : Type) [Field K] [NumberField K], (0 : ℝ) < Module.finrank ℚ K := fun K _ _ => by
    exact_mod_cast Module.finrank_pos
  have qL := q L
  have qF := q F
  have qF' := q F'
  rw [div_le_iff₀ qL, add_mul]
  have a1 : Real.log |((discr F : ℤ) : ℝ)| / Module.finrank ℚ F * Module.finrank ℚ L =
      Module.finrank F L * Real.log |((discr F : ℤ) : ℝ)| := by
    rw [e1]; field_simp
  have a2 : Real.log |((discr F' : ℤ) : ℝ)| / Module.finrank ℚ F' * Module.finrank ℚ L =
      Module.finrank F' L * Real.log |((discr F' : ℤ) : ℝ)| := by
    rw [e2]; field_simp
  rw [a1, a2]; linarith

theorem sz_sup : ∀ (F F' : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → Sz F' a' b' → Sz (F ⊔ F') (a + a') (b + b') := by
  rintro F F' a b a' b' ⟨i1, ha, hb⟩ ⟨i2, ha', hb'⟩
  haveI i3 : FiniteDimensional ℚ ↥(F ⊔ F') := IntermediateField.finiteDimensional_sup F F'
  letI : NumberField F := NumberField.mk
  letI : NumberField F' := NumberField.mk
  letI : NumberField ↥(F ⊔ F') := NumberField.mk
  refine ⟨i3, ?_, ?_⟩
  · have h1 : (Module.finrank ℚ ↥(F ⊔ F') : ℝ) ≤ Module.finrank ℚ F * Module.finrank ℚ F' := by
      exact_mod_cast IntermediateField.finrank_sup_le F F'
    have q : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], (0 : ℝ) < Module.finrank ℚ K := fun K _ => by
      exact_mod_cast Module.finrank_pos
    have h2 := Real.log_le_log (q _) h1
    rw [Real.log_mul (q F).ne' (q F').ne'] at h2
    linarith
  · letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    letI : Algebra F' ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    have h := log_discr_div_le F F' ↥(F ⊔ F') (GlobalTheory.T.map_different_le_different_sup_intermediateField F F')
    exact h.trans (add_le_add hb hb')

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
set_option autoImplicit false

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem sz_adjoin_rootOfUnity :
    ∀ n : ℕ, 0 < n → Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set F := ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ with hF
  haveI hc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [hF, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hn).tower_top (A := ℚ)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hfd : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {n} ℚ F
  refine ⟨hfd, ?_⟩
  letI : NumberField F := NumberField.mk
  have hrk : Module.finrank ℚ F = Nat.totient n :=
    IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hn)
  have ht : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have htR : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast ht
  have hd : (NumberField.discr F).natAbs ≤ n ^ Nat.totient n := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr n F]
    exact Nat.div_le_self _ _
  refine ⟨?_, ?_⟩
  · rw [hrk]
    exact Real.log_le_log htR (by exact_mod_cast Nat.totient_le n)
  · rw [hrk, div_le_iff₀ htR, mul_comm, ← Real.log_pow]
    have h0 : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
    refine Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hd

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixes
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixes
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N]

theorem mem_of_smul_eq (H : Subgroup (N ≃ₐ[K] N)) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ H) (P : Ideal (𝓞 N)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal]
    (τ : N ≃ₐ[K] N) (hτ : τ • P = P) : τ ∈ H := by
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 N ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (N ≃ₐ[K] N) P
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := hPo.over.symm
  set q := Ideal.absNorm 𝔭.asIdeal with hq
  have hq' : q = Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ q := fun x => by
    have := hσ x
    rw [hu, ← hq'] at this
    rw [← map_pow, Ideal.Quotient.eq]
    exact this
  have hσH : σ ∈ H := h σ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow]; exact hσ' x⟩
  have hpow : ∀ (i : ℕ) (x : 𝓞 N), Ideal.Quotient.mk P ((σ ^ i) • x) = Ideal.Quotient.mk P x ^ (q ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro x; rw [pow_succ', mul_smul, hσ', ih, ← pow_mul, pow_succ]
  letI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 N ⧸ P) := Ideal.Quotient.field _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p⟩
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (𝓞 K ⧸ 𝔭.asIdeal) p (𝓞 N ⧸ P)
    (Ideal.Quotient.stabilizerHom P 𝔭.asIdeal (N ≃ₐ[K] N) ⟨τ, hτ⟩)
  have hτ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (τ • x) = Ideal.Quotient.mk P x ^ (q ^ i) := fun x => by
    rw [hq', ← hi, Ideal.Quotient.stabilizerHom_apply]
    rfl
  have h1 : σ * τ * (σ ^ i)⁻¹ ∈ H := h _ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow, mul_smul, mul_smul, hσ', hτ', ← hpow, smul_inv_smul]⟩
  have h2 := H.mul_mem (H.mul_mem (H.inv_mem hσH) h1) (H.pow_mem hσH i)
  simpa [mul_assoc] using h2

theorem ncard_primes_eq_finrank_of_frob_fix (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M := by
  have := 𝔭.isPrime
  have hH : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ M.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 (h σ hσ)
  obtain ⟨P, hP, hPo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 N)))
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, f σ = f τ ↔ σ⁻¹ * τ ∈ M.fixingSubgroup := by
    intro σ τ
    constructor
    · intro e
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 M) (𝓞 N) (N ≃ₐ[M] N)
        (σ⁻¹ • P) (τ⁻¹ • P) e
      have hg' : τ⁻¹ • P = (g.restrictScalars K) • (σ⁻¹ • P) := by
        rw [hg]; rfl
      have hgH : g.restrictScalars K ∈ M.fixingSubgroup :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
      have h1 := mem_of_smul_eq M.fixingSubgroup 𝔭 hH (σ⁻¹ • P) (σ⁻¹ * τ * g.restrictScalars K) (by
        rw [mul_smul, ← hg', mul_smul, smul_inv_smul])
      exact (M.fixingSubgroup.mul_mem_cancel_right hgH).1 h1
    · intro e
      have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
      ext x
      simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
      have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
        apply RingOfIntegers.ext
        exact e' _ (x : M).2
      rw [mul_smul, inv_smul_eq_iff] at this
      rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq,
    ← Nat.card_congr (Setoid.quotientKerEquivRange f)]
  have : Setoid.ker f = QuotientGroup.leftRel M.fixingSubgroup := by
    ext σ τ
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply, hker]
  rw [this]
  rfl

end GlobalTheory.SplitCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixesStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) → {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M := by
  first | exact @GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | exact GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | (intros; apply GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix <;> assumption)
end
end

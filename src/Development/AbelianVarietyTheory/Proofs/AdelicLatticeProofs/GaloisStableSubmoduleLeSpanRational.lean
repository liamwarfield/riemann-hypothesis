module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.GaloisDescent

private theorem exists_rational_support_subset_of_galois_stable {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hw0 hcard
  have hrepr0 : b.repr w ≠ 0 := fun h => hw0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k₀, hk₀⟩ := Finsupp.support_nonempty_iff.mpr hrepr0
  have hk₀' : b.repr w k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀

  have hvW : (b.repr w k₀)⁻¹ • w ∈ W := W.smul_mem _ hw
  have hvk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w) k = (b.repr w k₀)⁻¹ * b.repr w k := by
    intro k; simp
  have hv1 : b.repr ((b.repr w k₀)⁻¹ • w) k₀ = 1 := by
    rw [hvk, inv_mul_cancel₀ hk₀']
  by_cases hfix : ∀ σ : ℂ ≃+* ℂ, ∀ k,
      σ (b.repr ((b.repr w k₀)⁻¹ • w) k) = b.repr ((b.repr w k₀)⁻¹ • w) k
  ·
    refine ⟨_, hvW, ?_, fun k => GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed _ (fun σ => hfix σ k), ?_⟩
    · intro h0
      rw [h0, map_zero, Finsupp.zero_apply] at hv1
      exact zero_ne_one hv1
    · intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [hvk] at hk
      exact right_ne_zero_of_mul hk
  ·
    push Not at hfix
    obtain ⟨σ, k₁, hk₁⟩ := hfix
    obtain ⟨v', hv'W, hv'⟩ := hW σ _ hvW
    have hdW : (b.repr w k₀)⁻¹ • w - v' ∈ W := W.sub_mem hvW hv'W
    have hdk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w - v') k =
        b.repr ((b.repr w k₀)⁻¹ • w) k - σ (b.repr ((b.repr w k₀)⁻¹ • w) k) := by
      intro k; rw [map_sub, Finsupp.sub_apply, hv']
    have hd0 : (b.repr w k₀)⁻¹ • w - v' ≠ 0 := by
      intro h
      have := hdk k₁
      rw [h, map_zero, Finsupp.zero_apply] at this
      exact hk₁ (sub_eq_zero.mp this.symm).symm
    have hsub : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support ⊆ (b.repr w).support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      intro hwk
      apply hk
      rw [hdk, hvk, hwk]
      simp
    have hk₀d : k₀ ∉ (b.repr ((b.repr w k₀)⁻¹ • w - v')).support := by
      rw [Finsupp.mem_support_iff, not_not, hdk, hv1, map_one, sub_self]
    have hlt : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k₀, hk₀, hk₀d⟩)
    obtain ⟨u, huW, hu0, hurat, husub⟩ := ih _ hlt _ hdW hd0 rfl
    exact ⟨u, huW, hu0, hurat, husub.trans hsub⟩

theorem exists_rational_support_subset {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) (n : ℕ) :
    ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support :=
  fun w hw hw0 hcard => exists_rational_support_subset_of_galois_stable b W hW n w hw hw0 hcard

private theorem mem_span_rational_of_galois_stable_of_support_card {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, (b.repr w).support.card = n →
      w ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hcard
  by_cases hw0 : w = 0
  · rw [hw0]; exact Submodule.zero_mem _
  obtain ⟨u, huW, hu0, hurat, husub⟩ :=
    exists_rational_support_subset b W hW n w hw hw0 hcard
  have hru : b.repr u ≠ 0 := fun h => hu0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hru
  have huk : b.repr u k ≠ 0 := Finsupp.mem_support_iff.mp hk

  have hdk : ∀ j, b.repr (w - (b.repr w k / b.repr u k) • u) j =
      b.repr w j - (b.repr w k / b.repr u k) * b.repr u j := by
    intro j; simp
  have hsub : (b.repr (w - (b.repr w k / b.repr u k) • u)).support ⊆ (b.repr w).support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    intro hwj
    apply hj
    have huj : b.repr u j = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (husub (Finsupp.mem_support_iff.mpr h)) hwj
    rw [hdk, hwj, huj]
    simp
  have hkout : k ∉ (b.repr (w - (b.repr w k / b.repr u k) • u)).support := by
    rw [Finsupp.mem_support_iff, not_not, hdk, div_mul_cancel₀ _ huk, sub_self]
  have hlt : (b.repr (w - (b.repr w k / b.repr u k) • u)).support.card < n := by
    rw [← hcard]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, husub hk, hkout⟩)
  have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ huW)) rfl
  have h2 : u ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} :=
    Submodule.subset_span ⟨huW, hurat⟩
  have h3 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w k / b.repr u k) h2)
  rwa [sub_add_cancel] at h3

theorem le_span_rational :
    ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro V κ _ _ b W hW w hw
  exact mem_span_rational_of_galois_stable_of_support_card b W hW _ w hw rfl

end GlobalTheory.ClassFin.GaloisDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisStable_submodule_le_span_rational : ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  first | exact @GlobalTheory.ClassFin.GaloisDescent.le_span_rational | exact GlobalTheory.ClassFin.GaloisDescent.le_span_rational | (intros; apply GlobalTheory.ClassFin.GaloisDescent.le_span_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem IsKum.minpoly_eq {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) : minpoly F θ = X ^ p - C δ := by
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime h.prime h.nonpow
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C δ h.prime.ne_zero)).symm
  simp [h.pow]

theorem IsKum.pow_apply {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (k : ℕ) :
    (σ ^ k) θ = algebraMap F E (ζ ^ k) * θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, h.conj, pow_succ', map_mul]
    ring

theorem kummer_galois : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ IsGalois F E ∧ orderOf σ = p ∧ (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) ∧ Nonempty (E ≃ₐ[F] AdjoinRoot (X ^ p - C δ : F[X])) ∧ ∀ (L : Type) [Field L] [Algebra F L] (r : L), r ^ p = algebraMap F L δ → ∃ ψ : E →ₐ[F] L, ψ θ = r := by
  intro p F E _ _ _ _ ζ δ θ σ h
  have hp := h.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero p := ⟨hp0⟩
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime hp h.nonpow
  have hζ : (primitiveRoots p F).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr h.root⟩
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hθ0 : θ ≠ 0 := by
    intro h0
    have h1 := h.pow
    rw [h0, zero_pow hp0, eq_comm, map_eq_zero] at h1
    exact h.nonpow 0 (by rw [zero_pow hp0, h1])
  have hsplit : IsSplittingField F E (X ^ p - C δ) := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot (h.root.map_of_injective hinj) h.pow
    · rw [eq_top_iff, ← h.gen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos δ)]
      simp [h.pow]
  have hfin : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ p - C δ)
  have hrank : Module.finrank F E = p :=
    finrank_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hgal : IsGalois F E := isGalois_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hext : ∀ τ₁ τ₂ : E ≃ₐ[F] E, τ₁ θ = τ₂ θ → τ₁ = τ₂ := by
    intro τ₁ τ₂ hτ
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top h.gen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hτ
  have hσp : σ ^ p = 1 :=
    hext _ _ (by rw [h.pow_apply, h.root.pow_eq_one, map_one, one_mul, AlgEquiv.one_apply])
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hc := h.conj
    rw [h1, AlgEquiv.one_apply] at hc
    have hz : algebraMap F E ζ = 1 := mul_right_cancel₀ hθ0 (by rw [← hc, one_mul])
    exact h.root.ne_one hp.one_lt (hinj (by rw [hz, map_one]))
  have hord : orderOf σ = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime hσp hσ1
  have hall : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ := by
    intro τ
    have hτp : (τ θ) ^ p = algebraMap F E δ := by rw [← map_pow, h.pow, AlgEquiv.commutes]
    have hq : (τ θ / θ) ^ p = 1 := by
      rw [div_pow, hτp, ← h.pow, div_self (pow_ne_zero _ hθ0)]
    obtain ⟨i, -, hi⟩ := (h.root.map_of_injective hinj).eq_pow_of_pow_eq_one hq
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨i, hext _ _ ?_⟩
    rw [zpow_natCast, h.pow_apply, map_pow, hi, div_mul_cancel₀ _ hθ0]
  let e : AdjoinRoot (X ^ p - C δ : F[X]) ≃ₐ[F] E := adjoinRootXPowSubCEquiv hζ hirr h.pow
  refine ⟨hfin, hrank, hgal, hord, hall, ⟨e.symm⟩, ?_⟩
  intro L _ _ r hr
  refine ⟨(AdjoinRoot.liftAlgHom (X ^ p - C δ) (Algebra.ofId F L) r (by simp [hr])).comp
    e.symm.toAlgHom, ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e, adjoinRootXPowSubCEquiv_symm_eq_root,
    AdjoinRoot.liftAlgHom_root]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormCoeffMinpolyLeOneOfNormLeOne
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_coeff_minpoly_le_one_of_norm_le_one (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (h : ‖Algebra.norm K x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ ≤ 1 := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖(minpoly K x).coeff 0‖ ≤ 1 := by
    rw [Algebra.norm_eq_norm_adjoin K x, ← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
      IntermediateField.minpoly_gen, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Module.finrank_pos).ne').1 h
  have h1 : spectralNorm K L x ≤ 1 := by
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x]
    exact Real.rpow_le_one (norm_nonneg _) h0 (by positivity)
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h1
  exact h1 n

theorem isIntegral_iff_valued_norm_le_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] [Algebra (v.adicCompletionIntegers F) L]
    [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L] (x : L) :
    IsIntegral (v.adicCompletionIntegers F) x ↔
      Valued.v (Algebra.norm (v.adicCompletion F) x) ≤ 1 := by
  constructor
  · intro h
    have h1 : IsIntegral (v.adicCompletionIntegers F) (Algebra.norm (v.adicCompletion F) x) :=
      Algebra.isIntegral_norm (v.adicCompletion F) h
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := v.adicCompletion F)).1 h1
    rw [← hy]
    exact y.2
  · intro h
    letI : NontriviallyNormedField (v.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰
    haveI : IsUltrametricDist (v.adicCompletion F) :=
      inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
        (Valued.toNormedField (v.adicCompletion F) ℤᵐ⁰).toDist)
    have hc : ∀ n, Valued.v ((minpoly (v.adicCompletion F) x).coeff n) ≤ 1 := fun n =>
      Valued.toNormedField.norm_le_one_iff.1
        (norm_coeff_minpoly_le_one_of_norm_le_one (v.adicCompletion F) L x
          (Valued.toNormedField.norm_le_one_iff.2 h) n)
    have hx : IsIntegral (v.adicCompletion F) x := Algebra.IsIntegral.isIntegral x
    have hl : minpoly (v.adicCompletion F) x ∈
        Polynomial.lifts (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (v.adicCompletion F), hq,
      minpoly.aeval]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteSpanAlgebraMapOfFreeFinite
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
    · simpa using J.mul_mem_right _ hr
    · simpa using J.add_mem hy hz
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_free_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (h : IsAdicComplete I R) :
    IsAdicComplete I M := by
  classical
  let b := Module.Free.chooseBasis R M
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    refine forall_congr' fun i => ?_
    rw [SModEq.sub_mem]
    simp
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have := h.toIsHausdorff.haus (b.repr x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
    simpa using this
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => h.toIsPrecomplete.prec (f := fun n => b.repr (f n) i)
        fun {m n} hmn => (key m _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have : b.repr (b.equivFun.symm L) i = L i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem isAdicComplete_span_algebraMap_of_free_finite :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
      (t : R), IsAdicComplete (Ideal.span {t}) R →
        IsAdicComplete (Ideal.span {algebraMap R O t}) O := by
  intro R O _ _ _ _ _ t h
  have h1 : IsAdicComplete (Ideal.span {t}) O := isAdicComplete_of_free_finite _ h
  have h2 : Ideal.span {algebraMap R O t} = (Ideal.span {t}).map (algebraMap R O) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h2]
  exact (IsAdicComplete.map_algebraMap_iff _ O).2 h1

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedOfUnit
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem IsQuad.exists_base_value {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (w : Valuation E ℤᵐ⁰) (h2 : w 2 = 1)
    (hδ : w (algebraMap F E δ) = 1) (x : E) : ∃ u : F, w x = w (algebraMap F E u) := by
  obtain ⟨a, b, hx⟩ := h.span x
  have hθ : w θ = 1 := by
    rw [← h.sq, map_pow] at hδ
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 hδ
  set y : E := algebraMap F E a - algebraMap F E b * θ with hy
  have ha : w (x + y) = w (algebraMap F E a) := by
    have : x + y = 2 * algebraMap F E a := by rw [hx, hy]; ring
    rw [this, map_mul, h2, one_mul]
  have hb : w (x - y) = w (algebraMap F E b) := by
    have : x - y = 2 * algebraMap F E b * θ := by rw [hx, hy]; ring
    rw [this, map_mul, map_mul, h2, hθ, one_mul, mul_one]
  have hn : x * y = algebraMap F E (a ^ 2 - δ * b ^ 2) := by
    rw [hx, hy, map_sub, map_mul, map_pow, map_pow, ← h.sq]; ring
  rcases lt_trichotomy (w x) (w y) with hlt | heq | hgt
  · have h1 : w y = w (algebraMap F E a) := by rw [← ha, w.map_add_eq_of_lt_right hlt]
    have hy0 : w y ≠ 0 := (lt_of_le_of_lt zero_le hlt).ne'
    refine ⟨(a ^ 2 - δ * b ^ 2) / a, ?_⟩
    rw [map_div₀, map_div₀, ← hn, ← h1, map_mul, mul_div_assoc, div_self hy0, mul_one]
  · have h1 : w (algebraMap F E a) ≤ w x := by
      rw [← ha]; exact (w.map_add x y).trans (max_le le_rfl heq.ge)
    have h3 : w (algebraMap F E b) ≤ w x := by
      rw [← hb]; exact (w.map_sub x y).trans (max_le le_rfl heq.ge)
    have h4 : w x ≤ max (w (algebraMap F E a)) (w (algebraMap F E b)) := by
      have := w.map_add (algebraMap F E a) (algebraMap F E b * θ)
      rwa [← hx, map_mul, hθ, mul_one] at this
    rcases le_max_iff.1 h4 with h5 | h5
    · exact ⟨a, le_antisymm h5 h1⟩
    · exact ⟨b, le_antisymm h5 h3⟩
  · exact ⟨a, by rw [← ha, w.map_add_eq_of_lt_left hgt]⟩

theorem valuation_unramified_of_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F 2 = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  intro F E _ _ _ _ _ δ θ σ hq w h2 hδ
  obtain ⟨e, he, hw⟩ := (places_over F E).2.2 w
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h2' : w.valuation E 2 = 1 := by
    have := hw 2
    rwa [map_ofNat, h2, one_pow] at this
  obtain ⟨u, hu⟩ := hq.exists_base_value (w.valuation E) h2' (by rw [hw, hδ, one_pow]) π
  rw [hπ, hw] at hu
  have hu0 : (w.under (𝓞 F)).valuation F u ≠ 0 := by
    intro h0
    rw [h0, zero_pow he.ne'] at hu
    exact WithZero.exp_ne_zero hu
  rw [← WithZero.exp_log hu0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hu
  have h1 : (e : ℤ) ∣ 1 := ⟨-WithZero.log ((w.under (𝓞 F)).valuation F u), by linear_combination -hu⟩
  have h3 : e = 1 := by
    have : e ∣ 1 := by exact_mod_cast h1
    exact Nat.dvd_one.1 this
  intro x
  rw [hw, h3, pow_one]

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_map_of_basis {F L A B ι : Type} [CommRing F] [CommRing L] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra L B] [Fintype ι] [DecidableEq ι] (φ : F →+* L) (ψ : A →+* B)
    (hψ : ∀ c, ψ (algebraMap F A c) = algebraMap L B (φ c))
    (b : Module.Basis ι F A) (b' : Module.Basis ι L B) (hb : ∀ i, ψ (b i) = b' i) (y : A) :
    Algebra.norm L (ψ y) = φ (Algebra.norm F y) := by
  have hr : ∀ (x : A) (i : ι), b'.repr (ψ x) i = φ (b.repr x i) := by
    intro x i
    have h1 : ψ x = ∑ j, φ (b.repr x j) • b' j := by
      conv_lhs => rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hψ, hb]
    rw [h1, b'.repr_sum_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem exists_basis_pow_root {L : Type} [Field L] {p : ℕ} (hp : 0 < p) (a : L) :
    ∃ b : Module.Basis (Fin p) L (AdjoinRoot (X ^ p - C a : L[X])),
      ∀ i, b i = AdjoinRoot.root (X ^ p - C a : L[X]) ^ (i : ℕ) := by
  have hne : (X ^ p - C a : L[X]) ≠ 0 := X_pow_sub_C_ne_zero hp a
  have hd : (AdjoinRoot.powerBasis hne).dim = p := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]
  refine ⟨(AdjoinRoot.powerBasis hne).basis.reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
  simp

theorem powSub_le_kNorm_and_kNorm_map : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  intro p hp
  constructor
  · intro F L _ _ φ δ x hx
    obtain ⟨r, hr⟩ := (mem_powSub p φ x).1 hx
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    obtain ⟨b, -⟩ := exists_basis_pow_root hp (φ δ)
    refine (mem_kNorm p φ δ x).2
      ⟨Units.map (algebraMap L (AdjoinRoot (X ^ p - C (φ δ) : L[X]))).toMonoidHom
        (Units.mk0 r hr0), ?_⟩
    change Algebra.norm L (algebraMap L _ r) = _
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, hr]
  · intro F L _ _ φ δ x hx
    obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ x).1 hx
    obtain ⟨b, hb⟩ := exists_basis_pow_root hp (RingHom.id F δ)
    obtain ⟨b', hb'⟩ := exists_basis_pow_root hp (φ δ)
    have hdv : (X ^ p - C (φ δ) : L[X]) ∣ (X ^ p - C (RingHom.id F δ) : F[X]).map φ := by
      simp
    let ψ := AdjoinRoot.map φ _ _ hdv
    refine (mem_kNorm p φ δ x).2 ⟨Units.map ψ.toMonoidHom y, ?_⟩
    change Algebra.norm L (ψ y) = _
    rw [norm_map_of_basis φ ψ (fun c => by simp [ψ]) b b'
      (fun i => by simp [hb, hb', ψ]) y, hy]
    rfl

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  first | exact @GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map | exact GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map | (intros; apply GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMul
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pTor_eq_card_inf_ker (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p U = Nat.card (U ⊓ (powMonoidHom p : G →* G).ker : Subgroup G) := by
  unfold pTor
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply])

theorem pIdx_pTor_ker_range :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  intro p A A' _ _ g hIK hTK hIR hTR
  have hcomm : (powMonoidHom p : A' →* A').comp g = g.comp (powMonoidHom p : A →* A) := by
    ext a; simp [map_pow]
  have hRp : pows p g.range = (powMonoidHom p : A →* A).range.map g := by
    simp only [pows, MonoidHom.range_eq_map, Subgroup.map_map, hcomm]
  have hKpow : g.ker.map (powMonoidHom p : A →* A) ≤ g.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact g.ker.pow_mem hk p

  have eA : pIdx p (⊤ : Subgroup A) =
      (powMonoidHom p : A →* A).range.relIndex g.ker * pIdx p g.range := by
    have h1 : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.index := by
      rw [pIdx, Subgroup.relIndex_top_right, pows, ← MonoidHom.range_eq_map]
    rw [h1, ← Subgroup.relIndex_mul_index
      (le_sup_left : (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).range ⊔ g.ker),
      Subgroup.relIndex_sup_left, ← Subgroup.comap_map_eq, Subgroup.index_comap, pIdx, hRp]

  have eK : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex
      ((powMonoidHom p : A →* A).range ⊓ g.ker) * (powMonoidHom p : A →* A).range.relIndex g.ker := by
    have h0 : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex g.ker := rfl
    rw [h0, ← Subgroup.relIndex_mul_relIndex _ ((powMonoidHom p : A →* A).range ⊓ g.ker) _
      (le_inf (Subgroup.map_le_range _ _) hKpow) inf_le_right, Subgroup.inf_relIndex_right]

  have hB : g.ker.comap (powMonoidHom p : A →* A) = (powMonoidHom p : A' →* A').ker.comap g := by
    ext a; simp [MonoidHom.mem_ker, map_pow]
  have hKB : g.ker ≤ g.ker.comap (powMonoidHom p : A →* A) := fun x hx => g.ker.pow_mem hx p
  have hQB : (powMonoidHom p : A →* A).ker ≤ g.ker.comap (powMonoidHom p : A →* A) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp [Subgroup.mem_comap, hx]

  have eR : pTor p g.range = g.ker.relIndex (powMonoidHom p : A →* A).ker *
      (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
    have h1 : pTor p g.range = g.ker.relIndex (g.ker.comap (powMonoidHom p : A →* A)) := by
      rw [pTor_eq_card_inf_ker, Subgroup.relIndex_ker, hB, Subgroup.map_comap_eq]
    have h2 : (g.ker ⊔ (powMonoidHom p : A →* A).ker).relIndex
        (g.ker.comap (powMonoidHom p : A →* A)) =
        (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
      rw [← Subgroup.comap_map_eq, Subgroup.relIndex_comap, Subgroup.map_comap_eq]
    rw [h1, ← Subgroup.relIndex_mul_relIndex g.ker (g.ker ⊔ (powMonoidHom p : A →* A).ker) _
      le_sup_left (sup_le hKB hQB), h2,
      Subgroup.relIndex_sup_left]

  have eT : pTor p (⊤ : Subgroup A) = pTor p g.ker * g.ker.relIndex (powMonoidHom p : A →* A).ker := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (g.ker ⊓ (powMonoidHom p : A →* A).ker)
      (powMonoidHom p : A →* A).ker bot_le inf_le_right
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] at h
    rw [pTor_eq_card_inf_ker, pTor_eq_card_inf_ker, top_inf_eq, ← h]
  rw [eK] at hIK ⊢
  rw [eR] at hTR ⊢
  rw [eA, eT]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul hIK) hIR, mul_ne_zero hTK (left_ne_zero_of_mul hTR), ?_⟩
  ring

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMulStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powIndex_torsion_ker_range_mul : ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  first | exact @GlobalTheory.CNorm.pIdx_pTor_ker_range | exact GlobalTheory.CNorm.pIdx_pTor_ker_range | (intros; apply GlobalTheory.CNorm.pIdx_pTor_ker_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugates
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugates
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem _root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates (F E K : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E) :
    algebraMap K (K ⊗[F] E) (Algebra.norm K y) =
      ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  classical
  set G := E ≃ₐ[F] E
  have hcard : Fintype.card G = Module.finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank F E, Nat.card_eq_fintype_card]
  let b : Module.Basis G F E := (Module.finBasis F E).reindex (Fintype.equivFinOfCardEq hcard).symm
  let b' : Module.Basis G K (K ⊗[F] E) := Algebra.TensorProduct.basis K b
  set A := Algebra.leftMulMatrix b' y with hA
  let P : Matrix G G E := fun g j => g (b j)
  have hP : P.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
    have hj : ∀ j, ∑ g, v g * g (b j) = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct, P] using congrFun hv j
    have hx : ∀ x : E, ∑ g, v g * g x = 0 := fun x => by
      calc ∑ g, v g * g x = ∑ g, v g * g (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr x j • ∑ g, v g * g (b j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, Algebra.smul_def, map_mul, AlgEquiv.commutes, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => by rw [AlgEquiv.commutes]; ring
        _ = 0 := by simp [hj]
    have hli := (linearIndependent_monoidHom E E).comp
      (fun g : G => (g : E ≃* E).toMonoidHom) (fun g₁ g₂ h => by
        ext x; exact DFunLike.congr_fun h x)
    have := Fintype.linearIndependent_iff.mp hli v (by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply]
      exact hx x)
    exact hv0 (funext this)
  let P' : Matrix G G (K ⊗[F] E) := P.map Algebra.TensorProduct.includeRight
  have key : Matrix.diagonal
      (fun g : G => Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y) * P'
      = P' * A.map (algebraMap K (K ⊗[F] E)) := by
    ext g j
    have h1 : y * b' j = ∑ i, A i j • b' i := by
      simpa [A, Algebra.leftMulMatrix_eq_repr_mul] using (b'.sum_repr (y * b' j)).symm
    have h2 := congrArg (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, b', Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.smul_def,
      AlgHom.commutes] at h2
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    change _ * (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b j)) =
      ∑ i, (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b i)) * algebraMap K (K ⊗[F] E) (A i j)
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdet := congrArg Matrix.det key
  have hAdet : (A.map (algebraMap K (K ⊗[F] E))).det = algebraMap K (K ⊗[F] E) A.det :=
    (RingHom.map_det _ _).symm
  have hPdet : P'.det = Algebra.TensorProduct.includeRight P.det :=
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hAdet, hA,
    ← Algebra.norm_eq_matrix_det] at hdet
  have hu : IsUnit P'.det := by
    rw [hPdet]; exact (isUnit_iff_ne_zero.mpr hP).map _
  exact (hu.mul_left_cancel (by rw [mul_comm]; exact hdet)).symm

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugatesStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates : ∀ (F E K : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), algebraMap K (K ⊗[F] E) (Algebra.norm K y) = ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  first | exact @GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | exact GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | (intros; apply GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tensor_repr_map {ι : Type} (b : Module.Basis ι F E) {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis K' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) i =
      φ ((Algebra.TensorProduct.basis K b).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]

theorem tensor_norm_map [FiniteDimensional F E] {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) :
    Algebra.norm K' (Algebra.TensorProduct.map φ (AlgHom.id F E) y) = φ (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K' b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b)]
  rw [show (φ : K → K') = φ.toRingHom from rfl, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply]
  have h1 : (1 : K') ⊗ₜ[F] b j = Algebra.TensorProduct.map φ (AlgHom.id F E) ((1 : K) ⊗ₜ[F] b j) := by
    simp
  rw [h1, ← map_mul, tensor_repr_map b φ]
  rfl

theorem tensor_norm_one_tmul [FiniteDimensional F E] (K : Type) [CommRing K] [Algebra F K] (e : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.norm F e) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b), Algebra.norm_eq_matrix_det b,
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end

theorem tnorm_baseChange : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  intro F E _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rintro K K' _ _ _ _ φ x ⟨y, hy⟩
    refine ⟨Algebra.TensorProduct.map φ (AlgHom.id F E) y, ?_⟩
    rw [tensor_norm_map φ y, hy, AlgHom.commutes]
  · intro K _ _ e
    exact ⟨(1 : K) ⊗ₜ[F] e, tensor_norm_one_tmul K e⟩
  · rintro K _ _ x y hy0 ⟨a, ha⟩ ⟨c, hc⟩
    have hyK : algebraMap F K y ≠ 0 := (_root_.map_ne_zero _).mpr hy0
    have hu : IsUnit (Algebra.lmul K (K ⊗[F] E) c) := by
      rw [LinearMap.isUnit_iff_isUnit_det, ← Algebra.norm_apply, hc]
      exact hyK.isUnit
    obtain ⟨d, hd⟩ := ((Module.End.isUnit_iff _).mp hu).2 1
    have hd' : c * d = 1 := hd
    have hn : Algebra.norm K c * Algebra.norm K d = 1 := by
      rw [← map_mul, hd', map_one]
    refine ⟨a * d, ?_⟩
    rw [map_mul, ha, map_mul]
    rw [hc] at hn
    calc algebraMap F K x * algebraMap F K y * Algebra.norm K d
        = algebraMap F K x * (algebraMap F K y * Algebra.norm K d) := by ring
      _ = algebraMap F K x := by rw [hn, mul_one]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangePropertiesStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormFromBaseChange_base_change_properties : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  first | exact @GlobalTheory.CNorm.tnorm_baseChange | exact GlobalTheory.CNorm.tnorm_baseChange | (intros; apply GlobalTheory.CNorm.tnorm_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorPowerSumRightActionNormAndContinuity
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ActNorm

private lemma tpow_apply_eq_prod {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ)
    (a b : Fin n → ι) : _root_.GlobalTheory.ClassFin.tpow n y a b = ∏ k, y (a k) (b k) := by
  simp [_root_.GlobalTheory.ClassFin.tpow]

private lemma tpow_conjTranspose {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) :
    (_root_.GlobalTheory.ClassFin.tpow n y)ᴴ = _root_.GlobalTheory.ClassFin.tpow n yᴴ := by
  ext a b
  simp [tpow_apply_eq_prod, conjTranspose_apply, star_prod]

private lemma nsq_eq_sum_sum_norm_sq_components {ι : Type} [Fintype ι] {m : ℕ} (d : Fin m → ℕ)
    (x : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) :
    _root_.GlobalTheory.ClassFin.nsq x = ∑ i, ∑ a : Fin (d i) → ι, ‖x ⟨i, a⟩‖ ^ 2 := by
  unfold _root_.GlobalTheory.ClassFin.nsq _root_.GlobalTheory.ClassFin.TIdx at *
  exact Fintype.sum_sigma _

private lemma act_apply_eq_vecMul_tpow {ι : Type} [Fintype ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ) (i : Fin m)
    (a : Fin (d i) → ι) :
    _root_.GlobalTheory.ClassFin.act d v y ⟨i, a⟩ =
      ((fun b => v ⟨i, b⟩) ᵥ* _root_.GlobalTheory.ClassFin.tpow (d i) y) a := rfl

private lemma sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] (w : κ → ℂ)
    (M : Matrix κ κ ℂ) (hM : M * Mᴴ = 1) : ∑ c, ‖(w ᵥ* M) c‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key : ∀ x : κ → ℂ, ((∑ c, ‖x c‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    intro x
    push_cast
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key, key, star_vecMul, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_one]

private lemma sum_norm_sq_vecMul_le_card_sq_mul_bound_sq {κ : Type} [Fintype κ] (w : κ → ℂ) (M : Matrix κ κ ℂ)
    (K : ℝ) (hK : ∀ a c, ‖M a c‖ ≤ K) :
    ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) ^ 2 * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
  have hc : ∀ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
    intro c
    have h1 : ‖(w ᵥ* M) c‖ ≤ ∑ a, ‖w a‖ * K := by
      simp only [vecMul, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hK a c) (norm_nonneg _)
    calc ‖(w ᵥ* M) c‖ ^ 2 ≤ (∑ a, ‖w a‖ * K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = K ^ 2 * (∑ a, ‖w a‖) ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ K ^ 2 * ((Fintype.card κ : ℝ) * ∑ a, ‖w a‖ ^ 2) := by
          gcongr
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖w a‖)
      _ = _ := by ring
  calc ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ ∑ _c : κ, (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => hc c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private lemma norm_tpow_apply_le_pow_of_forall_norm_le {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) (B : ℝ)
    (hy : ∀ i j, ‖y i j‖ ≤ B) (a b : Fin n → ι) : ‖_root_.GlobalTheory.ClassFin.tpow n y a b‖ ≤ B ^ n := by
  rw [tpow_apply_eq_prod, norm_prod]
  calc ∏ k, ‖y (a k) (b k)‖ ≤ ∏ _k : Fin n, B :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hy _ _
    _ = B ^ n := by simp

theorem _root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ), (∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ), U * Uᴴ = 1 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v U) = _root_.GlobalTheory.ClassFin.nsq v) ∧ (∀ C : ℝ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ), (∀ i j, ‖y i j‖ ≤ C) → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v y) ≤ C' * _root_.GlobalTheory.ClassFin.nsq v) ∧ ∀ v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ, Continuous (_root_.GlobalTheory.ClassFin.act d v) := by
  intro ι _ _ m d
  refine ⟨fun v U hU => ?_, fun C => ?_, fun v => ?_⟩
  · have hK : ∀ n, _root_.GlobalTheory.ClassFin.tpow n U * (_root_.GlobalTheory.ClassFin.tpow n U)ᴴ = 1 := by
      intro n
      have h := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).1 n
      rw [tpow_conjTranspose, ← h.2.1, hU, h.1]
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    exact sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one _ _ (hK _)
  · set B := max C 0
    refine ⟨∑ i, (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2,
      Finset.sum_nonneg fun _ _ => by positivity, fun v y hy => ?_⟩
    have hyB : ∀ i j, ‖y i j‖ ≤ B := fun i j => (hy i j).trans (le_max_left _ _)
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    refine (sum_norm_sq_vecMul_le_card_sq_mul_bound_sq _ _ _ (norm_tpow_apply_le_pow_of_forall_norm_le _ y B hyB)).trans ?_
    gcongr
    exact Finset.single_le_sum
      (f := fun i => (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  · unfold _root_.GlobalTheory.ClassFin.act
    simp only [vecMul, dotProduct, tpow_apply_eq_prod]
    fun_prop

end GlobalTheory.ClassFin.ActNorm
end

module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsDiscreteValuationRingLocalizationOfIsDedekindD
namespace GlobalTheory

open IsDiscreteValuationRing IsLocalRing Module TensorProduct

namespace NormVal

section Det

variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

lemma length_quot_span_singleton (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a := Ring.ord_eq_addVal a

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

lemma addVal_det_of_injective (f : M →ₗ[R] M) (hf : Function.Injective f) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by
  classical
  let N := LinearMap.range f
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype.comp (e' : M →ₗ[R] N)
  have hfe : f = N.subtype.comp (e : M →ₗ[R] N) := by ext x; rfl
  have hass : Associated (LinearMap.det f) (LinearMap.det g) := by
    rw [hfe]; exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, g (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : N) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hg : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  rw [(addVal_eq_iff_associated _ _).2 hass, ← LinearMap.det_toMatrix b', hg, Matrix.det_diagonal,
    addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => (length_quot_span_singleton _).symm

lemma length_quot_range_of_not_injective (f : M →ₗ[R] M) (hf : ¬ Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [f.quotKerEquivRange.finrank_eq] at h1
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have h3 : 0 < Module.finrank R (LinearMap.ker f) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
    exact hf
  have h4 : 0 < Module.finrank R (M ⧸ LinearMap.range f) := by omega
  obtain ⟨v, hv⟩ : ∃ v : M ⧸ LinearMap.range f, ∀ a : R, a • v = 0 → a = 0 := by
    by_contra hcon
    push Not at hcon
    have : Module.finrank R (M ⧸ LinearMap.range f) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro v
      obtain ⟨a, ha, ha0⟩ := hcon v
      exact ⟨a, ha0, ha⟩
    omega
  have hinj : Function.Injective (LinearMap.toSpanSingleton R _ v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hv a ha
  have h5 := Module.length_le_of_injective _ hinj
  have h6 : Module.length R R = ⊤ := by
    rw [← Ring.ord_zero, Ring.ord_eq_addVal, addVal_zero]
  rwa [h6, top_le_iff] at h5

lemma addVal_det (f : M →ₗ[R] M) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by
  by_cases hf : Function.Injective f
  · exact addVal_det_of_injective f hf
  · rw [length_quot_range_of_not_injective f hf, addVal_eq_top_iff,
      LinearMap.det_eq_zero_iff_ker_ne_bot, Ne, LinearMap.ker_eq_bot]
    exact hf

end Det

section Semilocal

variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]

lemma liesOver_maximalIdeal (n : Ideal S) [n.IsMaximal] : n.LiesOver (maximalIdeal R) :=
  ⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap R S) (algebraMap_isIntegral_iff.mpr inferInstance) n)).symm⟩

lemma length_quot_maximal (n : Ideal S) [n.IsMaximal] :
    Module.length R (S ⧸ n) = n.inertiaDeg R := by
  have := liesOver_maximalIdeal R n
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) n]
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n) := Module.Finite.of_restrictScalars_finite R _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective


lemma length_localization_quot_maximal (m n : MaximalSpectrum S) [Decidable (n = m)]
    (B : Type*) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B n.asIdeal] :
    Module.length B (B ⧸ m.asIdeal.map (algebraMap S B)) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h
    have := IsLocalization.AtPrime.isLocalRing B n.asIdeal
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal n.asIdeal B, Module.length_eq_one_iff,
      isSimpleModule_iff_isCoatom]
    exact Ideal.isMaximal_def.1 inferInstance
  · rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
    have : ¬ m.asIdeal ≤ n.asIdeal := fun hle =>
      h (MaximalSpectrum.ext (m.isMaximal.eq_of_le n.isMaximal.ne_top hle).symm)
    obtain ⟨y, hy, hyn⟩ := Set.not_subset.1 this
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hy)
      (IsLocalization.map_units _ (⟨y, hyn⟩ : n.asIdeal.primeCompl))

variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

lemma length_eq_sum_tensor {X : Type*} [AddCommGroup X] [Module S X] (hX : IsFiniteLength S X) :
    ∀ [Module R X] [IsScalarTower R S X], Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (A n ⊗[S] X) * n.asIdeal.inertiaDeg R := by
  classical
  induction hX with
  | of_subsingleton => intro _ _; simp
  | @of_simple_quotient X _ _ N hs _ ih =>
    intro _ _
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    let f : N →ₗ[S] X := N.subtype
    let g : X →ₗ[S] S ⧸ m := e.toLinearMap.comp N.mkQ
    have hf : Function.Injective f := N.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp N.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by simp [f, g])
    rw [length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg, ih,
      length_quot_maximal]
    have key : ∀ n : MaximalSpectrum S,
        Module.length (A n) (A n ⊗[S] X) =
        Module.length (A n) (A n ⊗[S] N) + if n = ⟨m, hm⟩ then 1 else 0 := by
      intro n
      have : Module.Flat S (A n) := IsLocalization.flat (A n) n.asIdeal.primeCompl
      rw [length_eq_add_of_exact (AlgebraTensorModule.lTensor (A n) (A n) f)
        (AlgebraTensorModule.lTensor (A n) (A n) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (A n) hg) (Module.Flat.lTensor_exact (A n) hfg),
        ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A n) m).toLinearEquiv.length_eq,
        ← length_localization_quot_maximal ⟨m, hm⟩ n (A n)]
    simp_rw [key, add_mul, Finset.sum_add_distrib]
    simp

lemma length_quot_eq_sum (I : Ideal S) (hI : Module.length R (S ⧸ I) ≠ ⊤) :
    Module.length R (S ⧸ I) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ I.map (algebraMap S (A n))) * n.asIdeal.inertiaDeg R := by
  have h : IsFiniteLength S (S ⧸ I) := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hI
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hI.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [length_eq_sum_tensor R A h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A n) I).toLinearEquiv.length_eq]

end Semilocal

end NormVal

open NormVal

variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

theorem addVal_norm_eq_length (x : S) :
    addVal R (Algebra.norm R x) = Module.length R (S ⧸ Ideal.span {x}) := by
  rw [Algebra.norm_apply, addVal_det]
  have h : LinearMap.range (Algebra.lmul R S x) = (Ideal.span {x}).restrictScalars R := by
    ext y
    simp [Ideal.mem_span_singleton', mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ h).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {x})).length_eq]

theorem addVal_norm_ne_top_iff (x : S) :
    addVal R (Algebra.norm R x) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by
  rw [Ne, addVal_eq_top_iff, Algebra.norm_apply, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot', mem_nonZeroDivisors_iff_left]
  simp

theorem length_quot_span_ne_top_iff (x : S) :
    Module.length R (S ⧸ Ideal.span {x}) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by
  rw [← addVal_norm_eq_length, addVal_norm_ne_top_iff]

section Local

variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

theorem addVal_norm_eq_sum_length {x : S} (hx : x ∈ nonZeroDivisors S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ Ideal.span {algebraMap S (A n) x}) * n.asIdeal.inertiaDeg R := by
  rw [addVal_norm_eq_length, length_quot_eq_sum R A _ ((length_quot_span_ne_top_iff R x).2 hx)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Ideal.map_span, Set.image_singleton]

variable [∀ n, IsDomain (A n)] [∀ n, IsDiscreteValuationRing (A n)]

theorem addVal_norm_eq_sum (x : S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      addVal (A n) (algebraMap S (A n) x) * n.asIdeal.inertiaDeg R := by
  by_cases hx : x ∈ nonZeroDivisors S
  · rw [addVal_norm_eq_sum_length R A hx]
    exact Finset.sum_congr rfl fun n _ => by rw [length_quot_span_singleton]
  · have h1 : addVal R (Algebra.norm R x) = ⊤ := by
      rwa [← addVal_norm_ne_top_iff R, not_not] at hx
    rw [mem_nonZeroDivisors_iff_left] at hx
    push Not at hx
    obtain ⟨y, hxy, hy⟩ := hx
    have hne : LinearMap.ker (LinearMap.toSpanSingleton S S y) ≠ ⊤ := by
      intro h
      have : (1 : S) ∈ LinearMap.ker (LinearMap.toSpanSingleton S S y) := h ▸ Submodule.mem_top
      exact hy (by simpa using this)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let n : MaximalSpectrum S := ⟨m, hm⟩
    have hy' : algebraMap S (A n) y ≠ 0 := by
      intro h
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.asIdeal.primeCompl (A n) y).1 h
      exact s.2 (hle (by simpa using hs))
    have hx' : algebraMap S (A n) x = 0 := by
      have := congrArg (algebraMap S (A n)) hxy
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hy'
    rw [h1, eq_comm, ENat.sum_eq_top]
    refine ⟨n, Finset.mem_univ _, ?_⟩
    rw [hx', addVal_zero, ENat.top_mul]
    exact_mod_cast (Ideal.inertiaDeg_pos n.asIdeal R).ne'


include R in
theorem addVal_localization_ne_top {x : S} (hx : x ∈ nonZeroDivisors S) (n : MaximalSpectrum S) :
    addVal (A n) (algebraMap S (A n) x) ≠ ⊤ := by
  rw [Ne, addVal_eq_top_iff]
  intro h
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.asIdeal.primeCompl (A n) x).1 h
  have : (s : S) = 0 := (mem_nonZeroDivisors_iff_left.mp hx) s (by simpa [mul_comm] using hs)
  exact s.2 (this ▸ n.asIdeal.zero_mem)

variable [∀ n, Algebra R (A n)] [∀ n, IsScalarTower R S (A n)]
  [∀ n, IsLocalHom (algebraMap R (A n))]

end Local


include R in
theorem isDiscreteValuationRing_localization_of_isDedekindDomain [IsDedekindDomain S]
    (n : MaximalSpectrum S) : IsDiscreteValuationRing (Localization.AtPrime n.asIdeal) := by
  have := NormVal.liesOver_maximalIdeal R n.asIdeal
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) n.asIdeal) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OrdFracEqValuationInvOfIsLocalization
open Module IsDiscreteValuationRing IsDedekindDomain TensorProduct Pointwise

universe u v

namespace GlobalTheory

namespace ExtField

section Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type*} [Field L] [Algebra A L] [IsFractionRing A L]
  [Algebra R A] [IsLocalHom (algebraMap R A)] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R A L]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain A] [IsDiscreteValuationRing A]
  [IsFractionRing A L] [IsLocalHom (algebraMap R A)] in
variable (R K L) in
include K L in
theorem faithfulSMul_of_tower : FaithfulSMul R A := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  rw [IsScalarTower.algebraMap_eq R A L] at h
  exact Function.Injective.of_comp h

end Local

section Kernel

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {V : Type*} [AddCommGroup V] [Module K V]
  {ι : Type*}

theorem ker_liftBaseChange_eq_of_finrank_le [Fintype ι] [DecidableEq ι] (c : V →ₗ[K] (ι → L))
    {W₀ : Submodule K V} (hW : W₀ ≤ LinearMap.ker c) [FiniteDimensional K (V ⧸ W₀)]
    (hr : finrank K (V ⧸ W₀) ≤ Fintype.card ι) {θ : ι → V}
    (hdet : (Matrix.of fun i j => c (θ j) i).det ≠ 0) :
    LinearMap.ker (c.liftBaseChange L) = W₀.baseChange L := by
  let g : L ⊗[K] (V ⧸ W₀) →ₗ[L] (ι → L) := (W₀.liftQ c hW).liftBaseChange L
  have hg : c.liftBaseChange L = g ∘ₗ W₀.mkQ.baseChange L := by
    ext v i
    simp [g]
  have hs : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)) y
    refine ⟨∑ j, a j ⊗ₜ Submodule.Quotient.mk (θ j), ?_⟩
    funext i
    simp [g, Matrix.mulVec, dotProduct, mul_comm]
  have hi : LinearMap.ker g = ⊥ := by
    have h₁ := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_baseChange,
      Module.finrank_fintype_fun_eq_card] at h₁
    rw [← Submodule.finrank_eq_zero]
    omega
  rw [hg, LinearMap.ker_comp, hi, Submodule.comap_bot, ker_baseChange_mkQ]

end Kernel

section Scale

variable {R K V ι : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

end Scale

section Free

variable (R S : Type*) [CommRing R] [Nontrivial R] [AddCommGroup S] [Module R S]
  [Module.Free R S] [Module.Finite R S] (Q : Type*) [AddCommGroup Q] [Module R Q]

end Free

section Valuation

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra S A]
  [IsLocalization.AtPrime A P.asIdeal] [Algebra A L] [IsScalarTower S A L] [IsFractionRing A L]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
private theorem valuation_algebraMap_le_one (a : A) : P.valuation L (algebraMap A L a) ≤ 1 := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj P.asIdeal.primeCompl a
  have h₁ := congrArg (fun y => P.valuation L (algebraMap A L y)) h
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr s.2, mul_one] at h₁
  rw [h₁]
  exact P.valuation_le_one r

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
private theorem valuation_algebraMap_unit (u : Aˣ) : P.valuation L (algebraMap A L u) = 1 := by
  refine eq_one_of_one_le_mul_left (valuation_algebraMap_le_one (L := L) P A (u : A))
    (valuation_algebraMap_le_one (L := L) P A (u⁻¹ : Aˣ)) ?_
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]

omit [IsFractionRing A L] in
private theorem valuation_algebraMap_irreducible {ϖ : A} (hϖ : Irreducible ϖ) :
    P.valuation L (algebraMap A L ϖ) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer' L
  have hπ' : P.valuation L (algebraMap A L (algebraMap S A π)) = WithZero.exp (-1) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact hπ
  have h₀ : algebraMap S A π ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible h₀ hϖ
  rw [hu, map_mul, map_mul, valuation_algebraMap_unit, one_mul, map_pow, map_pow] at hπ'
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← WithZero.exp_zero, WithZero.exp_inj] at hπ'
    omega
  have h₁ : P.valuation L (algebraMap A L ϖ) ≠ 0 := by
    intro h
    rw [h, zero_pow hk] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  rw [← WithZero.exp_log h₁, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hπ'
  rw [← WithZero.exp_log h₁, WithZero.exp_inj]
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hπ' with h | h
  · exact h.2
  · omega

theorem ordFrac_eq_valuation_inv_of_isLocalization (x : L) :
    Ring.ordFrac A x = (P.valuation L x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible hϖ hx
  rw [Units.smul_def, Algebra.smul_def, ordFrac_unit_mul_zpow hϖ, map_mul, map_zpow₀,
    valuation_algebraMap_unit, valuation_algebraMap_irreducible P A hϖ, one_mul,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg]
  simp

theorem log_ordFrac_eq_neg_log_valuation (x : L) :
    WithZero.log (Ring.ordFrac A x) = -WithZero.log (P.valuation L x) := by
  rw [ordFrac_eq_valuation_inv_of_isLocalization P A, WithZero.log_inv]

end Valuation

section Semilocal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]

omit [Module.Finite R S] in
variable {S} in
private theorem exists_algebra_localization (P : HeightOneSpectrum S) :
    ∃ _ : Algebra (Localization.AtPrime P.asIdeal) L,
      IsScalarTower S (Localization.AtPrime P.asIdeal) L ∧
      IsScalarTower R (Localization.AtPrime P.asIdeal) L ∧
      IsFractionRing (Localization.AtPrime P.asIdeal) L := by
  have hu : ∀ y : P.asIdeal.primeCompl, IsUnit (algebraMap S L y) := fun y =>
    IsLocalization.map_units L ⟨y.1, P.asIdeal.primeCompl_le_nonZeroDivisors y.2⟩
  letI : Algebra (Localization.AtPrime P.asIdeal) L := (IsLocalization.lift hu).toAlgebra
  have h₁ : IsScalarTower S (Localization.AtPrime P.asIdeal) L :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hu).symm
  refine ⟨inferInstance, h₁, IsScalarTower.of_algebraMap_eq fun r => ?_,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl _ L⟩
  rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime P.asIdeal),
    ← IsScalarTower.algebraMap_apply S, ← IsScalarTower.algebraMap_apply]

variable {S} in
private theorem dvr_localization (P : HeightOneSpectrum S) :
    IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S P.ne_bot _


include R K L in
theorem not_isField_of_finite : ¬ IsField S := by
  have := faithfulSMul_of_tower R K S L
  rw [← Algebra.IsIntegral.isField_iff_isField (FaithfulSMul.algebraMap_injective R S)]
  exact not_isField R


include R in
theorem finite_heightOneSpectrum : Finite (HeightOneSpectrum S) := by
  have := finite_maximalSpectrum_of_finite R S
  exact Finite.of_injective (fun P : HeightOneSpectrum S => (⟨P.asIdeal, P.isMaximal⟩ :
    MaximalSpectrum S)) fun P Q h => HeightOneSpectrum.ext (congrArg MaximalSpectrum.asIdeal h)


include R S in
theorem finrank_field_pos : 0 < finrank K L := by
  have := faithfulSMul_of_tower R K S L
  rw [IsFractionRing.finrank_eq R K S L]
  exact Module.finrank_pos

variable [Fintype (HeightOneSpectrum S)]

private theorem log_ordFrac_norm_algebraMap {x : S} (hx : x ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm K (algebraMap S L x))) =
      ∑ P : HeightOneSpectrum S,
        (P.asIdeal.inertiaDeg R : ℤ) * -WithZero.log (P.valuation L (algebraMap S L x)) := by
  have := faithfulSMul_of_tower R K S L
  let e := HeightOneSpectrum.equivMaximalSpectrum (not_isField_of_finite R K S L)
  letI : Fintype (MaximalSpectrum S) := Fintype.ofEquiv _ e
  have := isDiscreteValuationRing_localization_of_isDedekindDomain R (S := S)
  have h := addVal_norm_eq_sum R (fun n : MaximalSpectrum S => Localization.AtPrime n.asIdeal) x
  rw [← e.sum_comp] at h
  have key : ∀ P : HeightOneSpectrum S, ∃ m : ℕ,
      addVal (Localization.AtPrime (e P).asIdeal) (algebraMap S _ x) = m ∧
        -WithZero.log (P.valuation L (algebraMap S L x)) = m := by
    intro P
    obtain ⟨_, _, _, _⟩ := exists_algebra_localization R L P
    have := dvr_localization P
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (addVal_localization_ne_top R
      (fun n : MaximalSpectrum S => Localization.AtPrime n.asIdeal)
      (mem_nonZeroDivisors_of_ne_zero hx) (e P))
    refine ⟨m, hm.symm, ?_⟩
    have hm₁ : addVal (Localization.AtPrime P.asIdeal) (algebraMap S _ x) = m := hm.symm
    rw [← log_ordFrac_eq_neg_log_valuation P (Localization.AtPrime P.asIdeal),
      IsScalarTower.algebraMap_apply S (Localization.AtPrime P.asIdeal) L,
      ordFrac_algebraMap_eq_exp hm₁, WithZero.log_exp]
  choose m hm hm' using key
  simp only [hm] at h
  norm_cast at h
  rw [Algebra.norm_localization R (nonZeroDivisors R), ordFrac_algebraMap_eq_exp h,
    WithZero.log_exp]
  push_cast
  exact Finset.sum_congr rfl fun P _ => by rw [hm', mul_comm]; rfl


variable {L} in
theorem log_ordFrac_norm_eq_sum {x : L} (hx : x ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm K x)) =
      ∑ P : HeightOneSpectrum S,
        (P.asIdeal.inertiaDeg R : ℤ) * -WithZero.log (P.valuation L x) := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (finrank_field_pos R K S L)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hb₀ : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha₀ : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb₁ : algebraMap S L b ≠ 0 := by simpa using hb₀
  have ha₁ : algebraMap S L a ≠ 0 := by simpa using ha₀
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_mul, map_inv₀,
    WithZero.log_mul (by simpa using ha₀) (by simpa using hb₀), WithZero.log_inv,
    log_ordFrac_norm_algebraMap R K S L ha₀, log_ordFrac_norm_algebraMap R K S L hb₀,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [map_mul, map_inv₀, WithZero.log_mul (by simpa using ha₀) (by simpa using hb₀),
    WithZero.log_inv]
  ring

variable {R K S L}
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [FloorRing F]

end Semilocal

end ExtField

end GlobalTheory
end

open NumberField IsDedekindDomain IsLocalRing IsDiscreteValuationRing

namespace GlobalTheory

namespace OrderNorm

theorem length_quot_ringEquiv {T U : Type*} [CommRing T] [CommRing U] (e : T ≃+* U) (x : T) :
    Module.length T (T ⧸ Ideal.span {x}) = Module.length U (U ⧸ Ideal.span {e x}) := by
  let _ : Algebra T U := e.toRingHom.toAlgebra
  let f : T ≃ₐ[T] U := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  have hI : Ideal.span {e x} = (Ideal.span {x}).map (f : T →+* U) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [(Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f hI).toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective e.surjective

end OrderNorm

end GlobalTheory

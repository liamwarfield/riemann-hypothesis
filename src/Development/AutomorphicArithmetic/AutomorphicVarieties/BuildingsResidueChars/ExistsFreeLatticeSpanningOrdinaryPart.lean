module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOrdInt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigUnitInt
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite
    {O K : Type*} [CommRing O] [Field K] [Algebra O K] {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Finite O M] (T : Module.End O M) (μ : K) (y : K ⊗[O] M) (hy : y ≠ 0)
    (h : T.baseChange K y = μ • y) : IsIntegral O μ := by
  obtain ⟨p, hp, hT⟩ := LinearMap.exists_monic_and_aeval_eq_zero O T
  have key : ∀ q : Polynomial O,
      (Polynomial.aeval T q).baseChange K y = (Polynomial.aeval μ q) • y := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.smul_apply,
        Module.End.one_apply, algebraMap_smul]
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, hp, hq, add_smul]
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval T), map_mul (Polynomial.aeval μ),
        Polynomial.aeval_X, Polynomial.aeval_X, LinearMap.baseChange_mul, Module.End.mul_apply,
        h, map_smul, ih, smul_smul, mul_comm]
  have h0 := key p
  rw [hT, LinearMap.baseChange_zero, LinearMap.zero_apply] at h0
  have h1 : Polynomial.aeval μ p = 0 := (smul_eq_zero.mp h0.symm).resolve_right hy
  exact ⟨p, hp, by rwa [Polynomial.aeval_def] at h1⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (U V e : Module.End O M), V * U * e = e → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → e.baseChange K y = y → U.baseChange K y = μ • y → μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ M _ _ _ U V e hVU μ y hy he hU
  have h1 : μ • V.baseChange K y = y := by
    have h := congrArg (fun f : Module.End O M => f.baseChange K y) hVU
    simp only [LinearMap.baseChange_mul, Module.End.mul_apply] at h
    rwa [he, hU, map_smul] at h
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h1
    exact hy h1.symm
  have h2 : V.baseChange K y = μ⁻¹ • y := by
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
  exact ⟨hμ, UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite U μ y hy hU,
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite V μ⁻¹ y hy h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigNilInt
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (T : Module.End O M), LinearMap.range T ≤ IsLocalRing.maximalIdeal O • ⊤ → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → T.baseChange K y = μ • y → μ ≠ 0 → ¬ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ _ M _ _ _ T hT μ y hy hμy hμ hint
  obtain ⟨p, hmon, -, hcoef, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := T) (I := IsLocalRing.maximalIdeal O) (hI := hT)
  have hK : Polynomial.aeval (T.baseChange K) p = 0 := by
    have e : T.baseChange K = Module.End.baseChangeHom O K M T := rfl
    rw [e, Polynomial.aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvector (T.baseChange K) μ y :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμy, hy⟩
  have hq : Polynomial.aeval μ p = 0 := by
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O K)) hev
    rw [Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hK,
      LinearMap.zero_apply] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hy
  set n := p.natDegree with hn
  set ν := μ⁻¹ with hνdef
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have key : (1 : K) + ∑ i ∈ Finset.range n, algebraMap O K (p.coeff i) * ν ^ (n - i) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hq
    have h2 : ν ^ n * (∑ i ∈ Finset.range n, p.coeff i • μ ^ i + μ ^ n) = 0 := by
      rw [hq, mul_zero]
    rw [mul_add, Finset.mul_sum, ← mul_pow, hνμ, one_pow, add_comm] at h2
    rw [← h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hp' : ν ^ n = ν ^ (n - i) * ν ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
    have e : ν ^ i * μ ^ i = 1 := by rw [← mul_pow, hνμ, one_pow]
    rw [Algebra.smul_def, hp']
    calc algebraMap O K (p.coeff i) * ν ^ (n - i)
        = algebraMap O K (p.coeff i) * ν ^ (n - i) * (ν ^ i * μ ^ i) := by rw [e, mul_one]
      _ = ν ^ (n - i) * ν ^ i * (algebraMap O K (p.coeff i) * μ ^ i) := by ring
  let C := integralClosure O K
  let ν' : C := ⟨ν, hint⟩
  have hs : (1 : C) + ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) = 0 := by
    apply Subtype.ext
    simpa [C, ν'] using key
  have hmem : ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) ∈
      (IsLocalRing.maximalIdeal O).map (algebraMap O C) := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have hin : i < n := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hcoef i)
  have htop : (IsLocalRing.maximalIdeal O).map (algebraMap O C) = ⊤ := by
    rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_left hs]
    exact (Ideal.neg_mem_iff _).mpr hmem
  have hker : RingHom.ker (algebraMap O C) ≤ IsLocalRing.maximalIdeal O :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hint' : (algebraMap O C).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    ((Ideal.map_eq_top_iff_of_ker_le _ hker hint').mp htop)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigSum
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.exists_eigenvector_fixed_idempotent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U f : Module.End K V) (hc : Commute U f) (μ : K) :
    ∀ (k : ℕ) (y : V), y ≠ 0 → f y = y → ((U - μ • (1 : Module.End K V)) ^ k) y = 0 →
      ∃ z : V, z ≠ 0 ∧ f z = z ∧ U z = μ • z := by
  intro k
  induction k with
  | zero =>
    intro y hy _ h
    rw [pow_zero, Module.End.one_apply] at h
    exact absurd h hy
  | succ k ih =>
    intro y hy hfy hk
    by_cases hw : (U - μ • (1 : Module.End K V)) y = 0
    · refine ⟨y, hy, hfy, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hw
      exact hw
    · apply ih _ hw
      · have hc' : Commute (U - μ • (1 : Module.End K V)) f :=
          hc.sub_left (Commute.smul_left (Commute.one_left f) μ)
        have := LinearMap.congr_fun hc'.eq y
        rw [Module.End.mul_apply, Module.End.mul_apply, hfy] at this
        exact this.symm
      · rw [← Module.End.mul_apply, ← pow_succ]
        exact hk

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idempotent_kills_generalized_eigenspace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U f : Module.End K V) (hf : IsIdempotentElem f) (hc : Commute U f) (μ : K)
    (h : ∀ z : V, z ≠ 0 → f z = z → U z = μ • z → False) (y : V)
    (hy : y ∈ U.maxGenEigenspace μ) : f y = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U μ y).mp hy
  have hc' : Commute ((U - μ • (1 : Module.End K V)) ^ k) f :=
    (hc.sub_left (Commute.smul_left (Commute.one_left f) μ)).pow_left k
  obtain ⟨z, hz, hfz, hUz⟩ := exists_eigenvector_fixed_idempotent U f hc μ k (f y) hne
    (by rw [← Module.End.mul_apply, hf.eq])
    (by rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply, hk, map_zero])
  exact h z hz hfz hUz

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum :
    ∀ {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (U e : Module.End K V) (S : Set K), IsIdempotentElem e → Commute U e → (∀ μ y, y ≠ 0 → e y = y → U y = μ • y → μ ∈ S) → (∀ μ y, y ≠ 0 → e y = 0 → U y = μ • y → μ ∉ S) → LinearMap.range e = ⨆ μ ∈ S, U.maxGenEigenspace μ := by
  intro K V _ _ _ _ _ U e S he hc h1 h2
  have hE : ∀ μ, Submodule.map e (U.maxGenEigenspace μ) ≤ U.maxGenEigenspace μ := by
    intro μ
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U μ y).mp hy
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨k, ?_⟩
    have hc' : Commute ((U - μ • (1 : Module.End K V)) ^ k) e :=
      (hc.sub_left (Commute.smul_left (Commute.one_left e) μ)).pow_left k
    rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply, hk, map_zero]
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← Module.End.iSup_maxGenEigenspace_eq_top U, Submodule.map_iSup]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ S
    · exact (hE μ).trans (le_iSup₂_of_le μ hμ le_rfl)
    · rintro _ ⟨y, hy, rfl⟩
      have h0 : e y = 0 :=
        idempotent_kills_generalized_eigenspace U e he hc μ (fun z hz hez hUz => hμ (h1 μ z hz hez hUz)) y hy
      rw [h0]
      exact Submodule.zero_mem _
  · refine iSup₂_le fun μ hμ => ?_
    intro y hy
    have hf : IsIdempotentElem (1 - e) := he.one_sub
    have hc1 : Commute U (1 - e) := (Commute.one_right U).sub_right hc
    have h0 := idempotent_kills_generalized_eigenspace U (1 - e) hf hc1 μ
      (fun z hz hez hUz => h2 μ z hz
        (by rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_self] at hez; exact hez) hUz hμ) y hy
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
    exact ⟨y, h0.symm⟩
end

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}
    {U e : Module.End R M} (h : IsOrdProj I U e) : ∃ V : Module.End R M, V * U * e = e := by
  have hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e := fun x hx => h.bij.mapsTo hx
  have hb : Function.Bijective (U.restrict hm) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hxy⟩ := h.bij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective _ hb
  let V : Module.End R M := (LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict
  have hc : ∀ x, U (e x) = e (U x) := fun x => LinearMap.congr_fun h.comm.eq x
  have hV : ∀ z, e z = z → V (U z) = z := by
    intro z hz
    have : e.rangeRestrict (U z) = E ⟨z, z, hz⟩ := Subtype.ext (by
      show e (U z) = U z
      rw [← hc, hz])
    simp only [V, LinearMap.comp_apply, this]
    simp
  refine ⟨V, LinearMap.ext fun x => ?_⟩
  exact hV (e x) (LinearMap.congr_fun h.idem.eq x)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] [IsAlgClosed K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] {U e : Module.End O M}, IsOrdProj (IsLocalRing.maximalIdeal O) U e → LinearMap.range (e.baseChange K) = ⨆ μ ∈ {μ : K | μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹}, Module.End.maxGenEigenspace (U.baseChange K) μ := by
  intro O K _ _ _ _ _ M _ _ _ U e h
  refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum (U.baseChange K) (e.baseChange K) _ ?_ ?_ ?_ ?_
  · show _ * _ = _
    rw [← LinearMap.baseChange_mul, h.idem.eq]
  · show _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.comm.eq]
  · intro μ y hy he hU
    obtain ⟨V, hV⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv h
    exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt U V e hV μ y hy he hU
  · rintro μ y hy he hU ⟨h0, -, hi⟩
    obtain ⟨n, hn⟩ := h.nil 1
    have hp : ∀ k : ℕ, (U ^ k).baseChange K y = μ ^ k • y := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, LinearMap.baseChange_one, one_smul, Module.End.one_apply]
      | succ k ih =>
        rw [pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hU, map_smul, ih, smul_smul,
          pow_succ']
    refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt (U ^ n * (1 - e)) ?_ (μ ^ n) y hy ?_ (pow_ne_zero n h0) ?_
    · rintro _ ⟨x, rfl⟩
      have := hn x
      rw [pow_one] at this
      exact this
    · rw [LinearMap.baseChange_mul, Module.End.mul_apply, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply, he, sub_zero, Module.End.one_apply, hp]
    · rw [← inv_pow]
      exact hi.pow n
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmLocal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmFin
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CompleteFin
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [Module.Finite R M], IsAdicComplete I M := by
  intro R _ M _ _ _ I _ _
  have hH : IsHausdorff I M := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
  have hP : IsPrecomplete I M := by
    rw [← AdicCompletion.of_surjective_iff]
    have hR : Function.Surjective (AdicCompletion.of I R) := AdicCompletion.of_surjective_iff.mpr inferInstance
    intro x
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a m =>
      obtain ⟨r, rfl⟩ := hR a
      refine ⟨r • m, ?_⟩
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
      ext n
      rw [AdicCompletion.val_smul_apply]
      simp
      try rfl
    | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, by rw [map_add (f := _), map_add (f := _), hu, hv]⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem isMax_of_le {R : Type*} [CommRing R] (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (P : Ideal R) [hP : P.IsPrime] (h : I ≤ P) : P.IsMaximal := by
  have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (K := P.map (Ideal.Quotient.mk I))
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.2 h] at h3

private theorem art_pow {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] (k : ℕ) : IsArtinianRing (R ⧸ I ^ k) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h0 : I ^ k ≤ p.comap (Ideal.Quotient.mk (I ^ k)) := by
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h1 : (p.comap (Ideal.Quotient.mk (I ^ k))).IsMaximal :=
    isMax_of_le I _ (Ideal.IsPrime.le_of_pow_le h0)
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I ^ k)) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (I ^ k))
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.tateH1FinitenessAtPlacesOver :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [IsArtinianRing (R ⧸ I)] [Module.Finite R M], OrdAdm (M := M) I := by
  intro R _ M _ _ _ I _ _ _
  refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin I, fun k => ?_⟩
  haveI := art_pow I k
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Finite (R ⧸ I ^ k) (M ⧸ (I ^ k • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact isArtinian_of_surjective_algebraMap (R := R ⧸ I ^ k) Ideal.Quotient.mk_surjective
end

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M], OrdAdm (M := M) (IsLocalRing.maximalIdeal R) ∧ (Finite (IsLocalRing.ResidueField R) → ∀ k : ℕ, Finite (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M))) := by
  intro R _ M _ _ _ _ _ _
  haveI : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  have hOrd : OrdAdm (M := M) (IsLocalRing.maximalIdeal R) := by
    refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin (IsLocalRing.maximalIdeal R), fun k => ?_⟩
    have hMax {I : Ideal R} [IsArtinianRing (R ⧸ I)] (P : Ideal R) [P.IsPrime]
        (h : I ≤ P) : P.IsMaximal := by
      have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
      have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (K := P.map (Ideal.Quotient.mk I))
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 h] at h3
    have hArtPow (k : ℕ) : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
      rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
      intro p hp
      have h0 : IsLocalRing.maximalIdeal R ^ k ≤ p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k)) := by
        intro x hx
        simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      have h1 : (p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))).IsMaximal :=
        hMax _ (Ideal.IsPrime.le_of_pow_le h0)
      have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
        Ideal.Quotient.mk_surjective p
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
          Ideal.Quotient.mk_surjective h1 with h | h
      · exact absurd (h2 ▸ h) hp.ne_top
      · exact h2 ▸ h
    haveI := hArtPow k
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    refine ⟨inferInstance, ?_⟩
    haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k)
        (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact isArtinian_of_surjective_algebraMap (R := R ⧸ IsLocalRing.maximalIdeal R ^ k)
      Ideal.Quotient.mk_surjective
  refine ⟨hOrd, fun hfin k => ?_⟩
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := hfin
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    infer_instance
  | succ n ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.finite_quotient_smul _ (IsNoetherian.noetherian _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpanOrdinaryPartEqSupUnitGeneralizedEigenspaces
open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

open TensorProduct in
private theorem UpperTheory.pi_scalar_right_tmul {O Ω ι : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    [Fintype ι] [DecidableEq ι] (a : Ω) (v : ι → O) :
    TensorProduct.piScalarRight O Ω Ω ι (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := by
  ext i
  simp [Algebra.smul_def, mul_comm]

private theorem UpperTheory.map_max_gen_eigenspace_of_intertwine {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (E : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ x, g (E x) = E (f x)) (μ : K) :
    (f.maxGenEigenspace μ).map E.toLinearMap = g.maxGenEigenspace μ := by
  have hp : ∀ (k : ℕ) x, ((g - μ • 1) ^ k) (E x) = E (((f - μ • 1) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      simp [h]
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Module.End.mem_maxGenEigenspace,
    Module.End.mem_maxGenEigenspace]
  simp only [hp, EmbeddingLike.map_eq_zero_iff]

theorem UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces :
    ∀ (O Ω ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [Fintype ι] (T₀ : Module.End O (ι → O)) (T : Module.End Ω (ι → Ω)), (∀ v, T (fun i => algebraMap O Ω (v i)) = fun i => algebraMap O Ω (T₀ v i)) → ⨆ μ : {μ : Ω // IsIntUnit O μ}, T.maxGenEigenspace μ.1 = Submodule.span Ω ((fun (v : ι → O) i => algebraMap O Ω (v i)) '' (ordPart T₀ : Set (ι → O))) := by
  intro O Ω ι _ hO _ _ _ _ T₀ T hT
  classical
  haveI : IsAdicComplete (maximalIdeal O) O := hO.complete
  have hadm := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)).1
  have hex := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hadm T₀
  have key := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt (K := Ω) hex.1
  set E := TensorProduct.piScalarRight O Ω Ω ι with hE
  have hEt : ∀ (a : Ω) (v : ι → O),
      E (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := UpperTheory.pi_scalar_right_tmul
  have hc : ∀ x, T (E x) = E (T₀.baseChange Ω x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [LinearMap.baseChange_tmul, hEt, hEt, map_smul, hT]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 := congrArg (Submodule.map E.toLinearMap) key
  simp only [Submodule.map_iSup, UpperTheory.map_max_gen_eigenspace_of_intertwine E _ T hc] at h1
  rw [iSup_subtype]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [← hex.2.1]
      exact ⟨v, rfl⟩
    | add x y hx hy => simp only [map_add] at ⊢; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [← hex.2.1] at hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨_, ⟨(1 : Ω) ⊗ₜ w, rfl⟩, ?_⟩
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt, one_smul]
end

open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

theorem UpperTheory.exists_free_lattice_spanning_ordinary_part :
    ∀ (O Ω V ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] [Fintype ι] (C : Submodule Ω V) (T : Module.End Ω V) (ev : V →ₗ[Ω] (ι → Ω)), Function.Injective (algebraMap O Ω) → Set.BijOn ev C Set.univ → (∀ F ∈ C, T F ∈ C) → (∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∀ i, ev (T F) i ∈ mIm O Ω 0) → ∃ S : Submodule O V, Module.Free O S ∧ (⨆ μ : {μ : Ω // IsIntUnit O μ}, C ⊓ T.maxGenEigenspace μ.1) = Submodule.span Ω (S : Set V) ∧ (∀ F ∈ S, F ∈ C ∧ (∀ i, ev F i ∈ mIm O Ω 0) ∧ ∀ k : ℕ, ∃ n : ℕ, ∀ i, ev ((T ^ (n + 1)) F - F) i ∈ mIm O Ω k) ∧ ∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∃ F' ∈ S, ∀ k : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ i, ev ((T ^ j.factorial) F - F') i ∈ mIm O Ω k := by
  intro O Ω V ι _ _ _ _ _ _ _ _ _ _ C T ev hinj hbij hTC hint
  haveI : IsAdicComplete (maximalIdeal O) O := IsCNL.complete
  haveI : Finite (ResidueField O) := IsCNL.finite
  obtain ⟨hadm, hfin⟩ := ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)
  have hfin' := hfin ‹_›
  set A := algebraMap O Ω with hA
  let evC : C →ₗ[Ω] (ι → Ω) := ev ∘ₗ C.subtype
  have hevC : Function.Bijective evC := by
    refine ⟨fun x y hxy => Subtype.ext (hbij.injOn x.2 y.2 hxy), fun w => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn (Set.mem_univ w)
    exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective evC hevC
  let g : (ι → Ω) →ₗ[Ω] V := C.subtype ∘ₗ e.symm.toLinearMap
  have hgC : ∀ w, g w ∈ C := fun w => (e.symm w).2
  have hevg : ∀ w, ev (g w) = w := fun w => e.apply_symm_apply w
  have hgev : ∀ F ∈ C, g (ev F) = F := fun F hF => by
    have : e ⟨F, hF⟩ = ev F := rfl
    show ((e.symm (ev F) : C) : V) = F
    rw [← this, e.symm_apply_apply]
  have hginj : Function.Injective g := fun a b h => by rw [← hevg a, ← hevg b, h]
  let T' : Module.End Ω (ι → Ω) := ev ∘ₗ T ∘ₗ g
  have hgT : ∀ w, g (T' w) = T (g w) := fun w => hgev _ (hTC _ (hgC w))
  let jL : (ι → O) →ₗ[O] (ι → Ω) := LinearMap.pi (fun i => (Algebra.linearMap O Ω) ∘ₗ LinearMap.proj i)
  have hjL : ∀ v i, jL v i = A (v i) := fun v i => rfl
  have hjinj : Function.Injective jL := fun v w h => funext fun i => hinj (by rw [← hjL, ← hjL, h])
  have hmem0 : ∀ x : O, A x ∈ mIm O Ω 0 := fun x => mem_mIm.2 ⟨x, by simp, rfl⟩
  have hint' : ∀ v : ι → O, ∀ i, ∃ x : O, A x = T' (jL v) i := by
    intro v i
    have h1 : ∀ i, ev (g (jL v)) i ∈ mIm O Ω 0 := fun i => by rw [hevg]; exact hmem0 _
    obtain ⟨x, -, hx⟩ := mem_mIm.1 (hint _ (hgC _) h1 i)
    exact ⟨x, hx⟩
  choose f0 hf0 using hint'
  let T₀ : Module.End O (ι → O) :=
    { toFun := f0
      map_add' := fun v w => funext fun i => hinj (by
        simp only [Pi.add_apply, map_add (f := _), hf0])
      map_smul' := fun c v => funext fun i => hinj (by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, hf0, RingHom.id_apply]
        rw [map_smul, ← algebraMap_smul Ω c (jL v), map_smul, Pi.smul_apply, smul_eq_mul]) }
  have hT₀ : ∀ v, T' (jL v) = jL (T₀ v) := fun v => funext fun i => (hf0 v i).symm
  have key := UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces O Ω ι T₀ T' (fun v => hT₀ v)
  let L : (ι → O) →ₗ[O] V := (g.restrictScalars O) ∘ₗ jL
  have hLinj : Function.Injective L := hginj.comp hjinj
  have hpow : ∀ m w, g ((T' ^ m) w) = (T ^ m) (g w) := pow_intertwine (U := T') (U' := T) (f := g) hgT
  have hpow0 : ∀ m u, jL ((T₀ ^ m) u) = (T' ^ m) (jL u) :=
    pow_intertwine (U := T₀) (U' := T') (f := jL) (fun u => (hT₀ u).symm)
  have hcoord : ∀ k (x : ι → O), x ∈ maximalIdeal O ^ k • (⊤ : Submodule O (ι → O)) → ∀ i, x i ∈ maximalIdeal O ^ k := by
    intro k x hx i
    have := map_mem_smul_top (LinearMap.proj (R := O) (φ := fun _ : ι => O) i) _ hx
    simpa using this
  refine ⟨(ordPart T₀).map L, ?_, ?_, ?_, ?_⟩
  · haveI := (ordProjective hadm T₀).1 inferInstance
    haveI := (ordProjective hadm T₀).2 inferInstance
    haveI : Module.Free O (ordPart T₀) := Module.free_of_flat_of_isLocalRing
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective L hLinj _)
  · have key' : (⨆ μ : {μ : Ω // IsIntUnit O μ}, T'.maxGenEigenspace μ.1) =
        Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O))) := key
    have hspan : Submodule.span Ω (((ordPart T₀).map L : Submodule O V) : Set V) =
        (Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O)))).map g := by
      rw [← Submodule.span_image, Submodule.map_coe, Set.image_image]
      rfl
    have heig : ∀ μ : Ω, C ⊓ T.maxGenEigenspace μ = (T'.maxGenEigenspace μ).map g := by
      intro μ
      have hpowμ : ∀ (k : ℕ) (w : ι → Ω), g (((T' - μ • (1 : Module.End Ω (ι → Ω))) ^ k) w) =
          ((T - μ • (1 : Module.End Ω V)) ^ k) (g w) :=
        pow_intertwine (U := T' - μ • 1) (U' := T - μ • 1) (f := g) (fun w => by simp [hgT])
      ext x
      constructor
      · rintro ⟨hxC, hx⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
        refine ⟨ev x, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, hginj ?_⟩, hgev x hxC⟩
        rw [hpowμ, hgev x hxC, hk, map_zero]
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
        exact ⟨hgC w, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [← hpowμ, hk, map_zero]⟩⟩
    rw [hspan, ← key', Submodule.map_iSup]
    exact iSup_congr fun μ => heig μ.1
  · rintro F ⟨v, hv, rfl⟩
    refine ⟨hgC _, fun i => ?_, fun k => ?_⟩
    · show ev (g (jL v)) i ∈ _
      rw [hevg]
      exact hmem0 _
    · obtain ⟨n, hn⟩ := (ordPer hadm hfin' T₀ v).1 hv k
      refine ⟨n, fun i => ?_⟩
      show ev ((T ^ (n + 1)) (g (jL v)) - g (jL v)) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ hn i, rfl⟩
  · intro F hF hFi
    choose v _ hv using fun i => mem_mIm.1 (hFi i)
    have hFv : F = g (jL v) := by
      rw [← hgev F hF]
      congr 1
      funext i
      exact (hv i).symm
    refine ⟨L (ordProj (maximalIdeal O) T₀ v), ⟨_, ?_, rfl⟩, fun k => ?_⟩
    · rw [← (ordExists hadm T₀).2.1]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨N, hN⟩ := (ordFactLim hadm hfin' T₀ _).2 rfl k
      refine ⟨N, fun j hj i => ?_⟩
      rw [hFv]
      show ev ((T ^ j.factorial) (g (jL v)) - g (jL (ordProj _ T₀ v))) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ (hN j hj v) i, rfl⟩

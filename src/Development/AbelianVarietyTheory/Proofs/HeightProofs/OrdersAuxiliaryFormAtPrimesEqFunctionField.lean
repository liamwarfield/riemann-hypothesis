module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealisationValuesEqValuedPointOrders
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEquivCoverPointsPlacesBaseChange
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.ExistsMulEqMapOfIsAlgebraic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletion
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open ReciprocityTheory.ChartRestriction.G

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance gaussCompletionOpIsLocalRing : IsLocalRing (Op X la N) :=
  IsLocalization.AtPrime.isLocalRing (Op X la N) (gI X la N)

local instance gaussCompletionOpIsDomain : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance gaussCompletionKpField : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance gaussCompletionKpAlgebra : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la)
    (g := (algebraMap (Op X la N) (FractionRing (Op X la N))).comp
      (algebraMap (X.Ol la) (Op X la N)))
    ((IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp
      (Op.algebraMap_injective X la N))).toAlgebra

theorem exists_gaussRing_map :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ)
      (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ)
      (σ : T0.TVar D' N' ≃ Idx D j N),
      ∃ (f : T0.Op D' N' la →+* Op X la N) (φ : T0.KTf B.KO D' N' →+* Kp X la N),
        f.Flat ∧ IsLocalHom f ∧
        Ideal.map f (IsLocalRing.maximalIdeal (T0.Op D' N' la)) =
          IsLocalRing.maximalIdeal (Op X la N) ∧
        (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧
        (∀ o, φ (T0.OpToKT D' N' la o) = algebraMap (Op X la N) (FractionRing (Op X la N)) (f o)) ∧
        (∀ a : B.KO, φ (algebraMap B.KO (T0.KTf B.KO D' N') a) =
          algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧
        ∀ q, φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N') (MvPolynomial.X q)) =
          algebraMap (Op X la N) (FractionRing (Op X la N)) (Tv X la N (σ q)) := by
  intro D B P j X la N D' N' σ
  let : Algebra (MvPolynomial (T0.TVar D' N') (X.Ol la)) (Op X la N) :=
    ((algebraMap (Pol X la N) (Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) σ).toRingEquiv.toRingHom).toAlgebra
  have halg (p : MvPolynomial (T0.TVar D' N') (X.Ol la)) :
      algebraMap (MvPolynomial (T0.TVar D' N') (X.Ol la)) (Op X la N) p =
        algebraMap (Pol X la N) (Op X la N) (MvPolynomial.rename σ p) := rfl
  let Q := Formalism.DV.gaussIdeal (T0.TVar D' N') (X.Ol la)
  have : Q.IsPrime :=
    Formalism.DV.GaussP.gaussIdeal_isPrime (T0.TVar D' N') (X.Ol la)
  have : IsLocalization.AtPrime (Op X la N) Q :=
    isLocalization_rename (IsLocalRing.maximalIdeal (X.Ol la)) σ (gI X la N) rfl Q rfl
  obtain ⟨-, f, hf, hflat, hlocal, hmax, hres⟩ :=
    GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
      (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la) Q rfl (Op X la N)
  have hinj : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (T0.laT D' N' la).primeCompl x
    have hzero := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at hzero
    have hp : p = 0 := by
      have hrename := hinj (hzero.symm.trans (map_zero _).symm)
      have hmap := MvPolynomial.rename_injective σ σ.injective (hrename.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (hmap.trans (map_zero _).symm)
    simp only [hp, map_zero] at h
    exact (IsLocalization.map_units (T0.Op D' N' la) s).mul_left_eq_zero.mp h
  let := T0.algOpKT (K := B.KO) D' N' la
  have := T0.isFractionRing_Op (K := B.KO) D' N' la
  let ι : Op X la N →+* Kp X la N := algebraMap (Op X la N) (FractionRing (Op X la N))
  have hg : Function.Injective (ι.comp f) :=
    (IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp hfinj
  let φ : T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := T0.Op D' N' la) hg
  have hφ (o : T0.Op D' N' la) : φ (T0.OpToKT D' N' la o) = ι (f o) :=
    IsFractionRing.lift_algebraMap (A := T0.Op D' N' la) hg o
  have hφp (p : T0.OT B.KO D' N') :
      φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      ι (algebraMap (Pol X la N) (Op X la N)
        (MvPolynomial.rename σ (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    rw [← halg, ← hf, ← hφ, T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hlocal, hmax, hres, hφ, ?_, ?_⟩
  · have hconst : φ.comp (algebraMap B.KO (T0.KTf B.KO D' N')) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply B.KO (T0.KTp B.KO D' N') (T0.KTf B.KO D' N'),
        MvPolynomial.algebraMap_eq, h, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change ι (algebraMap (Pol X la N) (Op X la N)
          (MvPolynomial.C (algebraMap (𝓞 B.KO) (X.Ol la) a))) =
        (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la) _
          (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a)) : FractionRing (Op X la N))
      rw [IsFractionRing.lift_algebraMap]
      change ι (algebraMap (Pol X la N) (Op X la N)
          (MvPolynomial.C (algebraMap (𝓞 B.KO) (X.Ol la) a))) =
        ι (algebraMap (X.Ol la) (Op X la N) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun hconst a
  · intro q
    have h := hφp (MvPolynomial.X q)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h
    exact h

end

end GlobalTheory.GaussCompletion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletionStatement
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G
open scoped TensorProduct

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance gaussStatementOpIsLocalRing : IsLocalRing (Op X la N) :=
  IsLocalization.AtPrime.isLocalRing (Op X la N) (gI X la N)

local instance gaussStatementOpIsDomain : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance gaussStatementKpField : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance gaussStatementKpAlgebra : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la)
    (g := (algebraMap (Op X la N) (FractionRing (Op X la N))).comp
      (algebraMap (X.Ol la) (Op X la N)))
    ((IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp
      (Op.algebraMap_injective X la N))).toAlgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussRing_map_to_completion :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ)
      (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ)
      (σ : T0.TVar D' N' ≃ Idx D j N),
      ∃ (f : T0.Op D' N' la →+* Op X la N) (φ : T0.KTf B.KO D' N' →+* Kp X la N),
        f.Flat ∧ IsLocalHom f ∧
        Ideal.map f (IsLocalRing.maximalIdeal (T0.Op D' N' la)) =
          IsLocalRing.maximalIdeal (Op X la N) ∧
        (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧
        (∀ o, φ (T0.OpToKT D' N' la o) = algebraMap (Op X la N) (FractionRing (Op X la N)) (f o)) ∧
        (∀ a : B.KO, φ (algebraMap B.KO (T0.KTf B.KO D' N') a) =
          algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧
        ∀ q, φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N') (MvPolynomial.X q)) =
          algebraMap (Op X la N) (FractionRing (Op X la N)) (Tv X la N (σ q)) :=
  GlobalTheory.GaussCompletion.exists_gaussRing_map

end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComponentRingAwayGenericSectionQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComponentRingAwayGenericSectionQuotient
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem exists_away_algHom_ker {K R Q : Type*} [CommRing K] [CommRing R] [CommRing Q] [Algebra K R] [Algebra K Q]
    {n : ℕ} (Ψ : R →ₐ[K] Q) (a : Fin (n + 1) → R) (hs : Function.Surjective Ψ)
    (hk : RingHom.ker Ψ = Ideal.span (Set.range fun i : Fin n => a i.succ)) (hu : IsUnit (Ψ (a 0))) :
    ∃ χ : Localization.Away (a 0) →ₐ[K] Q, Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin n =>
        algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := by
  have hunit : ∀ y : Submonoid.powers (a 0), IsUnit (Ψ y) := by
    rintro ⟨_, m, rfl⟩
    simpa using hu.pow m
  let χ : Localization.Away (a 0) →ₐ[K] Q := IsLocalization.liftAlgHom (M := Submonoid.powers (a 0)) hunit
  have hχ : ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := fun r => by
    simp [χ]
  refine ⟨χ, fun q => ?_, le_antisymm ?_ ?_, hχ⟩
  · obtain ⟨r, rfl⟩ := hs q
    exact ⟨_, hχ r⟩
  · intro z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers (a 0)) z
    have hr : r ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker] at hz ⊢
      have := congrArg χ hrs
      rw [map_mul, hz, zero_mul, hχ] at this
      exact this.symm
    rw [hk] at hr
    have hle : Ideal.span (Set.range fun i : Fin n => a i.succ) ≤
        (Ideal.span (Set.range fun i : Fin n =>
          algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))).comap
          (algebraMap R (Localization.Away (a 0))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have e : algebraMap R (Localization.Away (a 0)) (a i.succ) =
          algebraMap R (Localization.Away (a 0)) (a 0) *
            (algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) := by
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
      show algebraMap R (Localization.Away (a 0)) (a i.succ) ∈ Ideal.span _
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have h2 := hle hr
    rw [Ideal.mem_comap] at h2
    simp only at hrs
    rw [← hrs] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ s)).1 h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : Ψ (a i.succ) = 0 := by
      rw [← RingHom.mem_ker, hk]
      exact Ideal.subset_span ⟨i, rfl⟩
    show χ _ = 0
    rw [map_mul, hχ, this, zero_mul]


open ReciprocityTheory.ChartRestriction.G.T0 in
theorem genericSection_away_quotient {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K']
    [Algebra K Kl] [Algebra Kl K'] {Dd m D' N' : ℕ} (hD : D' + 1 = Dd + 1) (eN : Fin (N' + 1) ≃ Fin m)
    (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (KTf K D' N') (OmS Ω D' N')]
    [FiniteDimensional (KTf K D' N') (OmS Ω D' N')] [Algebra (KTf K D' N') K']
    (t : Fin (Dd + 1) × Fin m → K') (v : Fin m → Ω)
    (hs : ∀ p : KTp K D' N', algebraMap (KTf K D' N') (OmS Ω D' N') (algebraMap (KTp K D' N') (KTf K D' N') p) =
      sHom j₀ x p)
    (hK : ∀ a : K, algebraMap (KTf K D' N') K' (algebraMap K (KTf K D' N') a) = algebraMap Kl K' (algebraMap K Kl a))
    (ht : ∀ q : TVar D' N', algebraMap (KTf K D' N') K' (algebraMap (KTp K D' N') (KTf K D' N') (MvPolynomial.X q)) =
      t (Fin.cast hD q.1, eN q.2))
    (hv : v (eN j₀) ≠ 0) (hx : ∀ k, x k * v (eN j₀) = v (eN (j₀.succAbove k)))
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    ∃ χ : Localization.Away (a 0) →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N', Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ ω : Ω, χ (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω)) (Localization.Away (a 0)) ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω))) =
        (1 : K') ⊗ₜ[KTf K D' N'] algebraMap Ω (OmS Ω D' N') ω := by
  obtain rfl : D' = Dd := by omega
  letI : Algebra K K' := ((algebraMap Kl K').comp (algebraMap K Kl)).toAlgebra
  haveI : IsScalarTower K Kl K' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (KTf K D' N') K' := IsScalarTower.of_algebraMap_eq fun c => (hK c).symm
  obtain ⟨Φ, hΦ, hsurj, hker, hunit⟩ := genericSection_quotient K Ω K' D' N' j₀ x
    (fun q => t (q.1, eN q.2)) (fun k => v (eN k) / v (eN j₀)) hs (fun q => (ht q).symm) (div_self hv)
    (fun k => by rw [div_eq_iff hv, hx])
  let Φ' : K' ⊗[K] Ω →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N' :=
    { Φ with
      commutes' := fun c => by
        show Φ (c ⊗ₜ[K] 1) = c ⊗ₜ 1
        rw [hΦ, map_one] }
  let e : K' ⊗[Kl] (Kl ⊗[K] Ω) ≃ₐ[K'] K' ⊗[K] Ω := Algebra.TensorProduct.cancelBaseChange K Kl K' K' Ω
  have he : ∀ (c : K') (ω : Ω), e (c ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω)) = c ⊗ₜ[K] ω := fun c ω => by
    simp [e]
  let u : K' ⊗[K] Ω := (1 : K') ⊗ₜ[K] v (eN j₀)
  have hu : IsUnit u :=
    (IsUnit.mk0 _ hv).map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Ω))
  have hea : ∀ i, e (a i) = u * ∑ k, t (i, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_sum, Finset.mul_sum, ← Equiv.sum_comp eN]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_div_cancel₀ _ hv]
  have hΨ : ∀ r, (Φ'.comp e.toAlgHom) r = Φ (e r) := fun _ => rfl
  obtain ⟨χ, h1, h2, h3⟩ := exists_away_algHom_ker (Φ'.comp e.toAlgHom) a (hsurj.comp e.surjective)
    (by
      apply le_antisymm
      · intro r hr
        have hr' : e r ∈ RingHom.ker Φ := hr
        rw [hker] at hr'
        have hle : Ideal.span (Set.range fun i : Fin D' =>
            (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) : K' ⊗[K] Ω)) ≤
            (Ideal.span (Set.range fun i : Fin D' => a i.succ)).comap e.symm := by
          rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          have h0 : a i.succ ∈ Ideal.span (Set.range fun i : Fin D' => a i.succ) := Ideal.subset_span ⟨i, rfl⟩
          rw [← e.symm_apply_apply (a i.succ), hea, map_mul,
            Ideal.unit_mul_mem_iff_mem _ (hu.map e.symm)] at h0
          exact h0
        have := hle hr'
        rwa [Ideal.mem_comap, AlgEquiv.symm_apply_apply] at this
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        show Φ (e (a i.succ)) = 0
        have : Φ (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀))) = 0 := by
          rw [← RingHom.mem_ker, hker]
          exact Ideal.subset_span ⟨i, rfl⟩
        rw [hea, map_mul, this, mul_zero])
    (by rw [hΨ, hea, map_mul]; exact (hu.map Φ).mul hunit)
  exact ⟨χ, h1, h2, fun ω => by rw [h3, hΨ, he, hΦ]⟩

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem componentRing_sec_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem componentRing_map_sectionIdeal : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

end Rec

theorem componentRing_away_quotient :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  intro D B P j X la N wL w Ω _ _ gF D' N' hD eN j₀ x _ _ _ hs hK ht hv hx
  rw [componentRing_map_sectionIdeal]
  exact genericSection_away_quotient (Kl := X.Kl la) hD eN j₀ x
    (fun p => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) (fun k => gF (X.inc wL (w k))) hs hK ht hv hx
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i))
    (fun i => componentRing_sec_eq_sum X la N Ω gF w i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComponentRingAwayGenericSectionQuotientStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentRing_away_genericSection_quotient : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  first | exact @GlobalTheory.componentRing_away_quotient | exact GlobalTheory.componentRing_away_quotient | (intros; apply GlobalTheory.componentRing_away_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrdersAuxiliaryFormAtPrimesEqFunctionField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.NetOrders

theorem exists_quot_maps {K' Fr : Type} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
    {ι : Type} [Fintype ι] {R : ι → Type} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
    (φ : ∀ c, Fr →ₐ[K'] R c) (hinj : ∀ f : Fr, (∀ c, φ c f = 0) → f = 0)
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q →
      RingHom.ker (φ c') ≤ Q → c = c')
    (hloc : ∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra K' (S c)] (χ : ∀ c, R c →ₐ[K'] S c)
    (hs : ∀ c, Function.Surjective (χ c)) (hk : ∀ c, RingHom.ker (χ c) = Ideal.map (φ c) J) :
    ∃ Ψ : ∀ c, (Fr ⧸ J) →ₐ[K'] S c, (∀ c x, Ψ c (Ideal.Quotient.mk J x) = χ c (φ c x)) ∧
      (∀ c, Function.Surjective (Ψ c)) ∧ (∀ a, (∀ c, Ψ c a = 0) → a = 0) ∧
      ∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1 := by
  have hJ : ∀ c, ∀ x ∈ J, χ c (φ c x) = 0 := fun c x hx => by
    rw [← RingHom.mem_ker, hk]; exact Ideal.mem_map_of_mem _ hx
  have hJK : ∀ c, ∀ x ∈ J ⊔ RingHom.ker (φ c), χ c (φ c x) = 0 := fun c x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), hJ c a ha, (RingHom.mem_ker).1 hb, map_zero, add_zero]
  refine ⟨fun c => Ideal.Quotient.liftₐ J ((χ c).comp (φ c)) (hJ c), fun c x => rfl, fun c s => ?_,
    fun a ha => ?_, fun c c' hne => ?_⟩
  · obtain ⟨r, rfl⟩ := hs c s
    obtain ⟨a, p, hp, e⟩ := hloc c r
    have hu := LocalUnitReduction.isUnit_mk_of_forall_prime (I := J ⊔ RingHom.ker (φ c)) (p := p)
      fun Q hQ hle => hp Q hQ (le_sup_left.trans hle) (le_sup_right.trans hle)
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : p * q - 1 ∈ J ⊔ RingHom.ker (φ c) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hq, map_one, sub_self]
    have h2 := hJK c _ h1
    refine ⟨Ideal.Quotient.mk J (q * a), ?_⟩
    show χ c (φ c (q * a)) = _
    simp only [map_sub, map_mul, map_one] at h2 ⊢
    rw [← e, map_mul]
    linear_combination (χ c r) * h2
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine LocalUnitReduction.mem_of_forall_sup_ker J φ hinj hone fun c => LocalUnitReduction.mem_sup_ker J φ (hloc c) ?_
    rw [← hk]; exact ha c
  · have htop : (J ⊔ RingHom.ker (φ c')) ⊔ RingHom.ker (φ c) = ⊤ := by
      by_contra hne'
      obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne'
      exact hne (hone Q hQ.isPrime (le_sup_left.trans (le_sup_left.trans hle)) c c' (le_sup_right.trans hle)
        (le_sup_right.trans (le_sup_left.trans hle)))
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 htop)
    refine ⟨Ideal.Quotient.mk J b, ?_, ?_⟩
    · show χ c (φ c b) = 0
      rw [(RingHom.mem_ker).1 hb, map_zero]
    · show χ c' (φ c' b) = 1
      have := congrArg (fun z => χ c' (φ c' z)) e
      simpa only [map_add (f := _), hJK c' a ha, zero_add, map_one] using this

theorem addVal_mul_pow {S : Type} [CommRing S] (u : AddValuation S (WithTop ℤ)) (a b : S) (m : ℕ) :
    u (a * b ^ m) = u a + m • u b := by
  rw [u.map_mul, u.map_pow]


open ReciprocityTheory.ChartRestriction.G.T0 (Data KTf KTp OmS TVar algOpKT) in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_equiv_places {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, X.Forms →ₐ[B.KO] Ω c)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ c, gF c (X.inc u F) = 0) → F = 0)
    (hsplit : ∀ (c : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF c (X.inc wL g) = gF c (X.inc wL (w k)) ∧
      ∀ c', c' ≠ c → gF c' (X.inc wL g) = 0)
    (hB : ∀ c, CurveLoc.BirAt X N w (gF c)) (hC : ∀ c, CurveLoc.CountQAt X la N w (gF c))
    [FiniteDimensional (Kp X la N) (OsK X la w)] [IsReduced (OsK X la w)]
    {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)]
    [∀ c, Algebra B.KO (A c)] [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
    (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin N)
    (hD : d.D = WeightFamilies.dimY D j) (h0 : ∀ c, gF c (X.inc wL (w (eN (d.jc c)))) ≠ 0)
    (hx : ∀ c k, d.x c k * gF c (X.inc wL (w (eN (d.jc c)))) = gF c (X.inc wL (w (eN ((d.jc c).succAbove k))))) :
    ∃ e : Pts (Op X la N) (OsK X la w) ≃ Σ c, {v // v ∈ d.PlOver la c}, ∀ ζ,
      fdeg ζ = d.fze hs (e ζ).1 (e ζ).2.1 ∧ ∃ κ : WithTop ℤ, κ ≠ ⊤ ∧ ∀ (m : ℕ) (F : X.Forms)
        (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F ∈ Vw X la N (addL (wt0 D j) wL m)),
        ord (unifO X la N) ζ (toOsK X la w (CurveLoc.fr0 X la N w m F hF)) =
          d.Wres (e ζ).1 (e ζ).2.1 (gF (e ζ).1 F) + m • κ := by
  have hD' : d.D + 1 = WeightFamilies.dimY D j + 1 := by rw [hD]
  obtain ⟨f, φ, hflat, hloc, hmax, hres, hφ, hφK, hφT⟩ :=
    GlobalTheory.T.exists_gaussRing_map_to_completion D B P j X la N d.D d.N (Equiv.prodCongr (finCongr hD') eN)
  letI : ∀ c, Algebra (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS hs c).toAlgebra
  letI : ∀ c, Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp hs la c
  letI := algOpKT (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR (K := B.KO) d.D d.N la
  haveI := fun c => (d.comp_facts hd hs la c).2.1
  haveI := fun c => (d.comp_facts hd hs la c).2.2.1
  haveI := fun c => (d.comp_facts hd hs la c).2.2.2.1
  letI : Algebra (KTf B.KO d.D d.N) (Kp X la N) := φ.toAlgebra
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) := f.toAlgebra
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Kp X la N) :=
    ((@algebraMap (Op X la N) (Kp X la N) _ _ _).comp f).toAlgebra
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) (Kp X la N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (Kp X la N) :=
    IsScalarTower.of_algebraMap_eq fun o => (hφ o).symm
  haveI : Module.Flat (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) := hflat
  haveI : IsLocalHom (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N)) := hloc
  have hres' : Function.Surjective (IsLocalRing.ResidueField.map
      (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N))) := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, ha⟩ := hres x
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact ha
  let hχ := fun c => GlobalTheory.T.componentRing_away_genericSection_quotient D B P j X la N wL w (Ω c) (gF c) d.D d.N hD' eN (d.jc c) (d.x c)
    (fun p => IsFractionRing.lift_algebraMap (g := (d.sH c).toRingHom) (hs c) p) hφK hφT (h0 c) (hx c)
  let χ := fun c => Classical.choose (hχ c)
  have hχs := fun c => (Classical.choose_spec (hχ c)).1
  have hχk := fun c => (Classical.choose_spec (hχ c)).2.1
  have hχψ := fun c => (Classical.choose_spec (hχ c)).2.2
  obtain ⟨Ψ, hΨ, hΨs, hΨi, hΨsep⟩ := exists_quot_maps (Jid X la w) (fun c => phiZ X la N (Ω c) (gF c) w)
    (CurveInj.fraction_zero_injective X la N Ω gF w hinj)
    (fun Q hQ _ c c' => CurveLoc.one_of_split X la N w Ω gF hsplit Q hQ c c')
    (fun c => CurveLoc.loc_of_bir X la N w (gF c) (hB c) (hC c)) χ hχs hχk
  haveI : CharZero (Kp X la N) := by
    haveI : CharZero (X.Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective
    exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective
  haveI := (integralClosure_dvr' (Op X la N) (Kp X la N) (OsK X la w)).2
  have hU : IsUnif (OsK X la w) (unifO X la N) :=
    isUnif_of_field (Kp X la N) (Op.irreducible_map X la N
      (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))))
  let Ψ' : ∀ c, OsK X la w →ₐ[Kp X la N] Kp X la N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N := Ψ
  have key : ∀ c (m : ℕ) (F : X.Forms)
      (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F ∈ Vw X la N (addL (wt0 D j) wL m)),
      Ψ' c (toOsK X la w (CurveLoc.fr0 X la N w m F hF)) =
        ((1 : Kp X la N) ⊗ₜ[KTf B.KO d.D d.N] algebraMap (Ω c) (OmS (Ω c) d.D d.N) (gF c F)) *
          χ c (CurveLoc.invS X la N w (gF c)) ^ m := fun c m F hF => by
    refine (hΨ c _).trans ?_
    rw [CurveLoc.phiZ_fraction_base, map_mul, map_pow, hχψ c]
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_coverPoints_places_baseChange (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) (KTf B.KO d.D d.N) (Kp X la N)
    hmax hres' ι (fun c => OmS (Ω c) d.D d.N) (OsK X la w) (unifO X la N) hU
    (fun c => (Ψ' c).restrictScalars (Op X la N)) hΨs hΨi hΨsep
  refine ⟨e.trans (Equiv.sigmaCongrRight fun c => Equiv.subtypeEquivRight fun v => by
    rw [d.plOver_eq hs la c]), fun ζ => ?_⟩
  obtain ⟨h1, u, hu, hord⟩ := he ζ
  refine ⟨h1, u (χ _ (CurveLoc.invS X la N w (gF (e ζ).1))), ?_, fun m F hF => ?_⟩
  · intro ht
    have := congrArg (fun z => u (χ _ z)) (CurveLoc.weight_zero_section_mul_inv X la N w (gF (e ζ).1))
    simp only [map_mul, map_one, AddValuation.map_mul, ht, add_top, AddValuation.map_one] at this
    exact WithTop.top_ne_zero this
  · exact (hord _).trans ((congrArg u (key (e ζ).1 m F hF)).trans ((addVal_mul_pow u _ _ m).trans
      (congrArg (· + _) (hu _))))

theorem toE_eq_nval {T : CDVR} {a : WithTop ℤ} {x : T.Fr} (h : toE a = nval T.V 1 x) :
    (x = 0 → a = ⊤) ∧ (x ≠ 0 → a = (vV T.V x : ℤ)) := by
  constructor
  · rintro rfl
    rw [nval_zero] at h
    cases a with
    | top => rfl
    | coe n => exact absurd h (EReal.coe_ne_top _)
  · intro hx
    rw [nval_of_ne hx] at h
    cases a with
    | top => exact absurd h.symm (EReal.coe_ne_top _)
    | coe n =>
      have h' : ((n : ℝ) : EReal) = _ := h
      rw [EReal.coe_eq_coe_iff, Nat.cast_one, div_one] at h'
      exact_mod_cast h'


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem comp_val_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
    {la : HeightOneSpectrum (𝓞 B.KO)} {ζ : PtsG G la} {y : E.Pt' la} (h : SecPt ζ y)
    {ι : Type} (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, (xplus X E hM).Forms →ₐ[B.KO] Ω c)
    (hsplit : ∀ (c : ι) (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ g : B.Cusp j u,
      gF c ((xplus X E hM).inc u g) = gF c ((xplus X E hM).inc u F) ∧
      ∀ c', c' ≠ c → gF c' ((xplus X E hM).inc u g) = 0)
    (c : ι) (hB : CurveLoc.BirAt (xplus X E hM) G.N G.w (gF c)) (k0 : Fin G.N)
    (hk0 : gF c ((xplus X E hM).inc wL (G.w k0)) ≠ 0)
    (W : AddValuation (Ω c) (WithTop ℤ)) (κ : WithTop ℤ) (hκ : κ ≠ ⊤)
    (hW : ∀ (m : ℕ) (F : (xplus X E hM).Forms)
      (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL m)),
      ord (unifO (xplus X E hM) la G.N) ζ
        (toOsK (xplus X E hM) la G.w (CurveLoc.fr0 (xplus X E hM) la G.N G.w m F hF)) = W (gF c F) + m • κ)
    (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)) (s : WeightFamilies.Wt D j → ℤ)
    (hv : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u),
      (gF Z ((xplus X E hM).inc u F) = 0 → h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (gF Z ((xplus X E hM).inc u F) ≠ 0 → h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) ≠ 0 ∧
        vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F))) =
          WithTop.untopD 0 (v (gF Z ((xplus X E hM).inc u F))) + s u)) :
    (⟨Z, v⟩ : Σ c, AddValuation (Ω c) (WithTop ℤ)) = ⟨c, W⟩ := by
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have key : ∀ (m : ℕ) (F : B.Cusp j (addL (wt0 D j) wL m)),
      toE (W (gF c ((xplus X E hM).inc _ F)) + m • κ) =
        nval h.T.V 1 (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc _ F)) *
          (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ m) := by
    intro m F
    rw [← hW m _ (emb_mem_Vw (xplus X E hM) la G.N _ F), h.ord]
    congr 1
    exact h.lift_frac m _
  have hWt : ∀ a : Ω c, a ≠ 0 → W a ≠ ⊤ := fun a ha ht => ha ((AddValuation.top_iff W).1 ht)
  obtain ⟨κ, rfl⟩ := WithTop.ne_top_iff_exists.1 hκ
  obtain rfl : Z = c := by
    by_contra hne
    obtain ⟨k, hk⟩ := GlobalTheory.ConstRatio.ratio_large (xplus X E hM) G.w (gF c) hB k0 hk0 1
    obtain ⟨-, d, hd, -⟩ := hk (k + 1) (Nat.lt_succ_self k)
    obtain ⟨g, hg1, hg2⟩ := hsplit c _ d
    have h1 := (toE_eq_nval (key _ g)).1 (by rw [(hv _ g).1 (hg2 Z hne), zero_mul])
    rw [← WithTop.coe_nsmul, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · exact hWt _ (hg1 ▸ hd) h1
    · exact WithTop.coe_ne_top h1
  congr 1
  apply AddValuation.ext
  intro a
  by_cases ha : a = 0
  · rw [ha, v.map_zero, W.map_zero]
  have hvt : ∀ a : Ω Z, a ≠ 0 → v a ≠ ⊤ := fun a ha ht => ha ((AddValuation.top_iff v).1 ht)
  obtain ⟨k, hk⟩ := GlobalTheory.ConstRatio.ratio_large (xplus X E hM) G.w (gF Z) hB k0 hk0 a
  obtain ⟨n, d, hd, hn⟩ := hk (k + 1) (Nat.lt_succ_self k)
  have hn0 : gF Z ((xplus X E hM).inc _ n) ≠ 0 := hn ▸ mul_ne_zero ha hd
  have hp := pow_ne_zero (k + 1) (inv_ne_zero hb)
  obtain ⟨n1, n2⟩ := (hv _ n).2 hn0
  obtain ⟨d1, d2⟩ := (hv _ d).2 hd
  have n3 := (toE_eq_nval (key _ n)).2 (mul_ne_zero n1 hp)
  have d3 := (toE_eq_nval (key _ d)).2 (mul_ne_zero d1 hp)
  rw [vV_mul n1 hp, n2, hn, W.map_mul, v.map_mul] at n3
  rw [vV_mul d1 hp, d2] at d3
  obtain ⟨va, hva⟩ := WithTop.ne_top_iff_exists.1 (hvt a ha)
  obtain ⟨Wa, hWa⟩ := WithTop.ne_top_iff_exists.1 (hWt a ha)
  obtain ⟨vd, hvd⟩ := WithTop.ne_top_iff_exists.1 (hvt _ hd)
  obtain ⟨Wd, hWd⟩ := WithTop.ne_top_iff_exists.1 (hWt _ hd)
  rw [← hva, ← hWa, ← hvd, ← hWd] at n3
  rw [← hvd, ← hWd] at d3
  rw [← hva, ← hWa]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.untopD_coe, WithTop.coe_inj] at n3 d3 ⊢
  omega


open ReciprocityTheory.ChartRestriction.G.T0 (Data) in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem net_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (xplus X E hM) ka wL wF)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, (xplus X E hM).Forms →ₐ[B.KO] Ω c) (val : ∀ c (u : WeightFamilies.Wt D j), B.Cusp j u → Ω c)
    (hval : ∀ c u F, gF c ((xplus X E hM).inc u F) = val c u F)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ c, val c u F = 0) → F = 0)
    (hsplit : ∀ (c : ι) (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ g : B.Cusp j u,
      val c u g = val c u F ∧ ∀ c', c' ≠ c → val c' u g = 0)
    (hB : ∀ c, CurveLoc.BirAt (xplus X E hM) G.N G.w (gF c))
    (hC : ∀ la c, CurveLoc.CountQAt (xplus X E hM) la G.N G.w (gF c))
    (y : ∀ la, PtsG G la → E.Pt' la) (hw : ∀ la ζ, SecPt ζ (y la ζ)) (g0 : B.Cusp j wF)
    (hcur : ∀ la, (secQ (y la) (hw la) g0).InCurve)
    {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)]
    [∀ c, Algebra B.KO (A c)] [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
    (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N)
    (hD : d.D = WeightFamilies.dimY D j) (h0 : ∀ c, val c wL (G.w (eN (d.jc c))) ≠ 0)
    (hx : ∀ c k, d.x c k * val c wL (G.w (eN (d.jc c))) = val c wL (G.w (eN ((d.jc c).succAbove k))))
    (het : ∀ c, val c _ G.et ≠ 0)
    (s : ∀ c, AddValuation (Ω c) (WithTop ℤ) → WeightFamilies.Wt D j → ℤ)
    (hord : ∀ c v, d.ord c v (d.n1 • d.wde) (d.et c) = WithTop.untopD 0 (v (val c _ G.et)) + s c v (etWt D j G.iet))
    (hpt : ∀ la (ζ : PtsG G la), ∃ (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)),
      ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u),
      (val Z u F = 0 → (hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (val Z u F ≠ 0 → (hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) ≠ 0 ∧
        vV (hw la ζ).T.V ((hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F))) =
          WithTop.untopD 0 (v (val Z u F)) + s Z v u)) (Gc PH Prw Pet : ℝ) :
    NetTie d hd hs G (fun la => secQ (y la) (hw la) g0) Gc PH Prw Pet := by
  intro la
  haveI := (hcur la).1
  haveI := (hcur la).2.1
  simp only [← hval] at hinj hsplit h0 hx het hord hpt
  obtain ⟨e, he⟩ := exists_equiv_places (xplus X E hM) la G.N G.w Ω gF hinj (fun c k => hsplit c wL (G.w k)) hB
    (hC la) d hd hs eN hD h0 hx
  refine finsum_eq_of_bijective e e.bijective fun ζ => ?_
  obtain ⟨h1, κ, hκ, hW⟩ := he ζ
  obtain ⟨Z, v, hv⟩ := hpt la ζ
  have hZ := comp_val_eq (hw la ζ) Ω gF hsplit (e ζ).1 (hB _) _ (h0 _) _ κ hκ hW Z v (s Z v) hv
  obtain ⟨e1, e2⟩ := (hv _ G.et).2 (het Z)
  rw [← hord] at e2
  have e3 : d.ord Z v (d.n1 • d.wde) (d.et Z) =
      d.ord (e ζ).1 (d.Wres (e ζ).1 (e ζ).2.1) (d.n1 • d.wde) (d.et (e ζ).1) :=
    congrArg (fun p : Σ c, AddValuation (Ω c) (WithTop ℤ) => d.ord p.1 p.2 (d.n1 • d.wde) (d.et p.1)) hZ
  have e4 := normalized_valuation_mul (hw la ζ).ep_pos _ e1
  rw [← (hw la ζ).hv, e2, e3] at e4
  show (ep (unifO (xplus X E hM) la G.N) ζ : ℝ) * (fdeg ζ : ℝ) * (E.vAt' la (y la ζ) (X.inc _ G.et)).toReal =
    ((1 : ℕ) : ℝ) * (d.fze hs (e ζ).1 (e ζ).2.1 : ℝ) *
      (d.ord (e ζ).1 (d.Wres (e ζ).1 (e ζ).2.1) (d.n1 • d.wde) (d.et (e ζ).1) : ℝ)
  rw [← e4, ← h1]
  push_cast
  ring

theorem ratio_single_mul {Ω M : Type} [Field Ω] (m : M) (a b : Ω) (hb : b ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Ω) (AddMonoidAlgebra.single m a : AddMonoidAlgebra Ω M)
      (AddMonoidAlgebra.single m b) * b = a := by
  have hex : ∃ r : Ω, (AddMonoidAlgebra.single m a : AddMonoidAlgebra Ω M) = r • AddMonoidAlgebra.single m b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ hb]⟩
  unfold ReciprocityTheory.ChartRestriction.G.T0.ratio
  rw [dite_eq_left hex]
  have := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at this
  exact (AddMonoidAlgebra.single_right_injective this).symm


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem netTie_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (hd : d.AxH (fun Z => AG Z)) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N), d.D = WeightFamilies.dimY D j → (∀ Z v, d.ord Z v = ordC (δ Z v) v) → d.wL = wtZ (wtA wL) wL.n → d.wF = wtZ (wtA wF) wF.n → (∀ k, d.w k = valC hG (wtA wL) wL.n (G.w (eN k)).1) → d.et = valC hG (wtA (wEt D j G.iet)) (wEt D j G.iet).n G.et.1 → d.n1 • d.wde = wtZ (wtA (wEt D j G.iet)) (wEt D j G.iet).n → ∀ (Gc PH Prw Pet : ℝ), NetTie (B := (recB h.toLawsCore)) d hd hs G (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie _ δ hδ d hd hs eN hD hord _ _ hdw hdet hwt
    Gc PH Prw Pet
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hpt := GlobalTheory.T.realisation_values_eq_valuedPoint_orders D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hδ
  have hQ : CountQAtSt h j hj hG hT := GlobalTheory.SecCount.countQAtSt D T h j hj hG hT
  have hordC : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (v : AddValuation (Om Z) (WithTop ℤ)) a n f,
      ordC (δ Z v) v (wtZ a n) (valC hG a n f Z) =
        WithTop.untopD 0 (v (evC hG Z f)) + frW (δ Z v) (wtZ a n) := fun Z v a n f => by
    simp only [ordC, valC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have h0 : ∀ Z, evC hG Z (G.w (eN (d.jc Z))).1 ≠ 0 := fun Z h0 => hd.w_base Z (by
    rw [hdw]; simp only [valC, h0, AddMonoidAlgebra.single_zero])
  refine net_eq (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G (fun Z => Om Z)
    (fun Z => formsEvR j hG hT Z) (fun Z u F => evC hG Z F.1) (fun Z u F => formsEvR_inc h j hj hG hT Z u F) hV hC
    (fun Z => birAt_of h j hj hG hT G hB Z) (fun la Z => hQ ka wL wF G S g0 la hH Z) y
    (fun la ζ => (hw la ζ).toSecPt) g0 hcur d hd hs eN hD h0 (fun Z k => ?_) (fun Z h0 => hd.et_ne Z ?_)
    (fun Z v u => frW (δ Z v) (wtZ (wtA u) u.n)) (fun Z v => ?_) (fun la ζ => ?_) Gc PH Prw Pet
  · unfold ReciprocityTheory.ChartRestriction.G.T0.Data.x
    rw [hdw, hdw]
    exact ratio_single_mul _ _ _ (h0 Z)
  · rw [hdet]
    have h0' : evC hG Z G.et.1 = 0 := h0
    simp only [valC, h0', AddMonoidAlgebra.single_zero]
  · rw [hord, hwt, hdet]
    exact hordC Z v _ _ _
  · obtain ⟨Z, v, -, -, hv⟩ := hpt la ζ
    exact ⟨Z, v, fun u F => ⟨(hv u F).1, fun hne => ⟨((hv u F).2 hne).1,
      ((hv u F).2 hne).2.trans (hordC Z v _ _ _)⟩⟩⟩

end GlobalTheory.NetOrders
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrdersAuxiliaryFormAtPrimesEqFunctionFieldStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orders_auxiliary_form_at_primes_eq_functionField : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (hd : d.AxH (fun Z => AG Z)) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N), d.D = WeightFamilies.dimY D j → (∀ Z v, d.ord Z v = ordC (δ Z v) v) → d.wL = wtZ (wtA wL) wL.n → d.wF = wtZ (wtA wF) wF.n → (∀ k, d.w k = valC hG (wtA wL) wL.n (G.w (eN k)).1) → d.et = valC hG (wtA (wEt D j G.iet)) (wEt D j G.iet).n G.et.1 → d.n1 • d.wde = wtZ (wtA (wEt D j G.iet)) (wEt D j G.iet).n → ∀ (Gc PH Prw Pet : ℝ), NetTie (B := (recB h.toLawsCore)) d hd hs G (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  first | exact @GlobalTheory.NetOrders.netTie_record | exact GlobalTheory.NetOrders.netTie_record | (intros; apply GlobalTheory.NetOrders.netTie_record <;> assumption)
end

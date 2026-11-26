module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCompDim
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecAlgField

theorem genPar_algebraicIndependent (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

end SecAlgField

theorem SecAlgField.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement) :
    SecAlgField.Statement := by
  intro k _ n e Q g hQ hg
  show IsField (GenSec k e Q)
  have : Module.Finite (GenParField k e n) (GenSec k e Q) :=
    h₁ k (GenParField k e n) n e Q g (genPar k e n)
      (SecAlgField.genPar_algebraicIndependent k e n) hQ hg
  have : IsDomain (GenSec k e Q) := h₂ k n e Q g hQ hg
  exact isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PResidueAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem ResidueAlgIndep.proof : ResidueAlgIndep.Statement := by
  intro K _ _ e n v
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal) p

  have hext : (eval₂Hom ((algebraMap k E).comp (algebraMap (𝓞 K) k)) (parYκ e n v)) =
      (algebraMap R E).comp (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
      rw [← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) R]
      exact Ideal.ResidueField.map_algebraMap _ _ _ _ a
    · simp [parYκ, parY, R, E]
  have key : aeval (parYκ e n v) (MvPolynomial.map (algebraMap (𝓞 K) k) q) =
      algebraMap R E (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R q) := by
    rw [aeval_def, eval₂_map]
    exact congrArg (fun φ => φ q) hext
  rw [key, Ideal.algebraMap_residueField_eq_zero] at hp
  have hq : q ∈ parPrime e n v := by
    have h2 : (IsLocalRing.maximalIdeal R).comap (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) =
        parPrime e n v :=
      Localization.AtPrime.under_maximalIdeal
    rw [← h2]
    exact hp
  rw [parPrime, MvPolynomial.mem_map_C_iff] at hq
  ext m
  simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
    Ideal.algebraMap_residueField_eq_zero.mpr (hq m)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace ChartDomain

variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

abbrev Base : Type := Localization.Away (Ideal.Quotient.mk Q (X j))

def cx (e : ℕ) (l : Fin n) : MvPolynomial (Par e n) (Base Q j) :=
  C (algebraMap _ _ (Ideal.Quotient.mk Q (X l)))

def cinv (e : ℕ) : MvPolynomial (Par e n) (Base Q j) :=
  C (IsLocalization.Away.invSelf (Ideal.Quotient.mk Q (X j)))

theorem cx_mul_cinv : cx Q j e j * cinv Q j e = 1 := by
  rw [cx, cinv, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

def parVal : Par e n → MvPolynomial (Par e n) (Base Q j)
  | .inl (i, l) => X (.inl (i, l)) -
      if l = j then cinv Q j e * ∑ m, X (.inl (i, m)) * cx Q j e m else 0
  | .inr l => X (.inr l) -
      if l = j then cinv Q j e * (∑ m, X (.inr m) * cx Q j e m - 1) else 0

def κ (e : ℕ) : D →+* MvPolynomial (Par e n) (Base Q j) :=
  (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp ((Ideal.Quotient.mk Q).comp C))

def evalF (e : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* MvPolynomial (Par e n) (Base Q j) :=
  eval₂Hom (eval₂Hom (κ Q j e) (parVal Q j)) (cx Q j e)

theorem evalF_comp_map :
    (evalF Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)) =
      (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp (Ideal.Quotient.mk Q)) := by
  apply MvPolynomial.ringHom_ext
  · intro d; simp [evalF, κ]
  · intro l; simp [evalF, cx]

theorem secIdeal_le_ker :
    secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X ≤ RingHom.ker (evalF Q j e) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, evalF_comp_map]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inl (i, m)) * cx Q j e m)) * cx_mul_cinv Q j (e := e)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_one, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inr m) * cx Q j e m - 1)) * cx_mul_cinv Q j (e := e)

abbrev secI (e : ℕ) : Ideal (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :=
  secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)

abbrev Sec (e : ℕ) : Type :=
  SecAlg (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)

abbrev xj (e : ℕ) : Sec Q e :=
  secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D) j

abbrev Chart (e : ℕ) : Type :=
  Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (X : Par e n → MvPolynomial (Par e n) D) j)

def toChart (e : ℕ) : MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* Chart Q j e :=
  algebraMap _ (Chart Q j e)

theorem toChart_apply (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toChart Q j e a =
      algebraMap (Sec Q e) (Chart Q j e) (Ideal.Quotient.mk (secI Q e) a) := rfl

def toPoly (e : ℕ) : Chart Q j e →+* MvPolynomial (Par e n) (Base Q j) :=
  IsLocalization.Away.lift (xj Q j e)
    (g := Ideal.Quotient.lift (secI Q e) (evalF Q j e) (fun _ ha => RingHom.mem_ker.mp (secIdeal_le_ker Q j ha))) (by
      simp only [xj, secCoord, Ideal.Quotient.lift_mk, evalF, coe_eval₂Hom, eval₂_X]
      exact IsUnit.of_mul_eq_one _ (cx_mul_cinv Q j (e := e)))

theorem toPoly_toChart (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toPoly Q j e (toChart Q j e a) = evalF Q j e a := by
  rw [toChart_apply, toPoly, IsLocalization.Away.lift_eq, Ideal.Quotient.lift_mk]

theorem toChart_eq_zero {e : ℕ} {a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)} (ha : a ∈ secI Q e) :
    toChart Q j e a = 0 := by
  rw [toChart_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

def quotToChart (e : ℕ) : MvPolynomial (Fin n) D ⧸ Q →+* Chart Q j e :=
  Ideal.Quotient.lift Q ((toChart Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (fun _ hq => toChart_eq_zero Q j (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))))

def baseToChart (e : ℕ) : Base Q j →+* Chart Q j e :=
  IsLocalization.Away.lift (Ideal.Quotient.mk Q (X j)) (g := quotToChart Q j e) (by
    rw [quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply, map_X, toChart_apply]
    exact IsLocalization.Away.algebraMap_isUnit (xj Q j e))

def fromPoly (e : ℕ) : MvPolynomial (Par e n) (Base Q j) →+* Chart Q j e :=
  eval₂Hom (baseToChart Q j e) fun p => toChart Q j e (C (X p))

theorem baseToChart_mk (p : MvPolynomial (Fin n) D) :
    baseToChart Q j e (algebraMap _ (Base Q j) (Ideal.Quotient.mk Q p)) =
      toChart Q j e (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D) p) := by
  rw [baseToChart, IsLocalization.Away.lift_eq, quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply]

theorem fromPoly_cx (l : Fin n) : fromPoly Q j e (cx Q j e l) = toChart Q j e (X l) := by
  rw [cx, fromPoly, coe_eval₂Hom, eval₂_C, baseToChart_mk, map_X]

theorem fromPoly_X (p : Par e n) : fromPoly Q j e (X p) = toChart Q j e (C (X p)) := by
  rw [fromPoly, coe_eval₂Hom, eval₂_X]

theorem fromPoly_secForm (i : Fin e) :
    fromPoly Q j e (∑ m, X (.inl (i, m)) * cx Q j e m) = 0 := by
  have hmem : secForm (X : Par e n → MvPolynomial (Par e n) D) i ∈ secI Q e :=
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  rw [← toChart_eq_zero Q j hmem]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, fromPoly_X, fromPoly_cx, secForm, linForm]

theorem fromPoly_chartForm :
    fromPoly Q j e (∑ m, X (.inr m) * cx Q j e m - 1) = 0 := by
  have hmem : chartForm (X : Par e n → MvPolynomial (Par e n) D) - 1 ∈ secI Q e :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← toChart_eq_zero Q j hmem]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_sub, map_one, fromPoly_X, fromPoly_cx, chartForm, linForm]

theorem fromPoly_toPoly_toChart :
    ((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e) = toChart Q j e := by
  apply MvPolynomial.ringHom_ext
  · intro c
    have h : (((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e)).comp C =
        (toChart Q j e).comp C := by
      apply MvPolynomial.ringHom_ext
      · intro d
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, κ, coe_eval₂Hom, eval₂_C, fromPoly,
          baseToChart_mk, map_C]
      · intro p
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_C, eval₂_X]
        rcases p with ⟨i, l⟩ | l
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_secForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_chartForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
    exact RingHom.congr_fun h c
  · intro l
    simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_X, fromPoly_cx]

theorem fromPoly_comp_toPoly : (fromPoly Q j e).comp (toPoly Q j e) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xj Q j e))
  apply Ideal.Quotient.ringHom_ext
  exact fromPoly_toPoly_toChart Q j

theorem toPoly_algebraMap (d : D) : toPoly Q j e (algebraMap D (Chart Q j e) d) = κ Q j e d := by
  rw [IsScalarTower.algebraMap_apply D (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) (Chart Q j e),
    MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  exact (toPoly_toChart Q j e _).trans (by simp [evalF])

end ChartDomain


open ChartDomain in
theorem ChartDomain.proof : ChartDomain.Statement := by
  intro D _ _ n e Q j hQ hQD hXj
  have hxj : Ideal.Quotient.mk Q (X j) ≠ 0 := fun h => hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (MvPolynomial (Fin n) D ⧸ Q) := Ideal.Quotient.isDomain Q
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hxj
  have : IsDomain (Base Q j) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (toPoly Q j e) :=
    Function.LeftInverse.injective (g := fromPoly Q j e) fun x => RingHom.congr_fun (fromPoly_comp_toPoly Q j) x
  refine ⟨Function.Injective.isDomain _ hinj, ?_⟩
  intro a b hab
  have h := congrArg (toPoly Q j e) hab
  rw [toPoly_algebraMap, toPoly_algebraMap] at h
  have h2 := IsLocalization.injective (Base Q j) hle (C_injective _ _ h)
  have h3 : C (a - b) ∈ Q := by rw [map_sub]; exact Ideal.Quotient.eq.mp h2
  exact sub_eq_zero.mp (hQD _ h3)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecCompDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem homogeneousComponent_map_coeffs {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem SpecCompDim.proof (hCone : ConeDimOfChowForm.Statement) (hFib : FibreCompDim.Statement) :
    SpecCompDim.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : I.IsPrime := hI.isPrime
  let k := v.asIdeal.ResidueField
  let φ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k :=
    MvPolynomial.map (algebraMap (𝓞 K) k)
  let ψ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) K :=
    MvPolynomial.map (algebraMap (𝓞 K) K)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hker : RingHom.ker φ = Ideal.map C v.asIdeal := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWprime : W.IsPrime := hWmin.1.1
  have hkerW : RingHom.ker φ ≤ W := hker ▸ le_sup_right.trans hWmin.1.2

  have hP : (integralModel I).IsPrime := Ideal.comap_isPrime ψ I
  have hPC : (integralModel I).comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, integralModel, Ideal.mem_bot]
    constructor
    · intro h
      by_contra hc
      have hu : IsUnit (ψ (C c)) := by
        rw [show ψ (C c) = C (algebraMap (𝓞 K) K c) from map_C _ _]
        exact (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc)).map C
      exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    · rintro rfl
      simp
  have hPloc : (integralModel I).map ψ = I := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := 𝓞 K) (S := K)
    have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (𝓞 K)) K
    exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin n)))
      (MvPolynomial (Fin n) K) I
  have hdim := hFib (𝓞 K) K n (integralModel I) W v hP hPC hWmin
  rw [hPloc, hCone K n (e + 1) I f hI hf] at hdim
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hkerW, ?_, ?_⟩, hdim⟩
  ·
    have hmin : reduceMod v W ∈ (reduceMod v (integralModel I)).minimalPrimes := by
      change W.map φ ∈ ((integralModel I).map φ).minimalPrimes
      rw [Ideal.minimalPrimes_map_of_surjective hφ, hker]
      exact ⟨W, hWmin, rfl⟩
    refine MinimalPrimeHomog.proof k n _ _ ?_ hmin
    intro g hg d
    change g ∈ (integralModel I).map φ at hg
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hg
    rw [homogeneousComponent_map_coeffs]
    refine Ideal.mem_map_of_mem φ ?_
    change ψ (homogeneousComponent d p) ∈ I
    rw [← homogeneousComponent_map_coeffs]
    exact hI.isHomog _ hp d
  ·
    obtain ⟨j, hj⟩ := hWrel
    refine ⟨j, fun h => hj ?_⟩
    have h' : X j ∈ (W.map φ).comap φ := by
      rw [Ideal.mem_comap, map_X]
      exact h
    rwa [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerW] at h'

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (P J : Ideal A) (ψ : A ⧸ P →+* L)
    (hloc : IsLocalHom (ψ.comp (Ideal.Quotient.mk P))) (hflat : ψ.Flat)
    (hmax : (IsLocalRing.maximalIdeal A).map (ψ.comp (Ideal.Quotient.mk P)) =
      IsLocalRing.maximalIdeal L) :
    Module.length L (L ⧸ J.map (ψ.comp (Ideal.Quotient.mk P))) =
      Module.length A (A ⧸ (P ⊔ J)) := by
  have : Nontrivial (A ⧸ P) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg ψ h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := ψ.toAlgebra
  have : Module.Flat (A ⧸ P) L := hflat
  have : IsLocalHom (algebraMap (A ⧸ P) L) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (hloc.map_nonunit a ha).map _
  have hq : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk P) =
      IsLocalRing.maximalIdeal (A ⧸ P) := by
    have h : (IsLocalRing.maximalIdeal (A ⧸ P)).comap (Ideal.Quotient.mk P) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hmax' : (IsLocalRing.maximalIdeal (A ⧸ P)).map (algebraMap (A ⧸ P) L) =
      IsLocalRing.maximalIdeal L := by
    rw [← hq, Ideal.map_map]
    exact hmax
  have key := IsLocalRing.length_baseChange (A ⧸ P) L ((A ⧸ P) ⧸ J.map (Ideal.Quotient.mk P))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L
    (J.map (Ideal.Quotient.mk P))).toLinearEquiv.length_eq, hmax'] at key
  have h1 : Module.length L (L ⧸ IsLocalRing.maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one, Ideal.map_map, RingHom.algebraMap_toAlgebra] at key
  rw [key, ← Module.length_eq_of_surjective (S := A) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A P J).toLinearEquiv.length_eq

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (u : Fin n → R) :
    (linForm u).map φ = linForm (fun j => φ (u j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

theorem secLin_eq_mk_map {K : Type*} [Field K] [NumberField K] {n e : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (u : Fin n → 𝓞 K) :
    secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      Ideal.Quotient.mk _ ((linForm u).map (algebraMap (𝓞 K) (ParDVR e n v))) := by
  rw [secLin, map_linForm]

theorem SpecLength.proof (h1 : SpecChart.Statement) (h2 : FiniteOrd.Statement)
    (h3 : ParDVRIsDVR.Statement) (h4 : SecBFinite.Statement) (h5 : SecBLinInj.Statement) :
    SpecLength.Statement := by
  classical
  intro K _ _ n e I f u v hI hf hu 𝔫 W hW hWn
  have hWp : W.IsPrime := hW.1.1.1
  obtain ⟨ψ, hψ, hloc, hflat, hmax⟩ := h1 K n e I v hI 𝔫 W hW hWn
  have := h3 K e n v
  have := h4 K n e I f v hI hf
  have hfin := h2 (ParDVR e n v) (SecB e I v) _ (h5 K n e I f u v hI hf hu) 𝔫
  have hx : algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
      (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))) =
      (ψ.comp (Ideal.Quotient.mk _)) (algebraMap _ (Localization.AtPrime W) (linForm u)) := by
    rw [RingHom.comp_apply, hψ]
    exact congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)) (secLin_eq_mk_map I v u)
  have hlen0 := length_quot_map_of_flat (A := Localization.AtPrime W)
    (L := Localization.AtPrime 𝔫.asIdeal)
    (P := (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
    (J := Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}) (ψ := ψ) hloc hflat
  have hlen := hlen0 hmax
  rw [Ideal.map_span, Set.image_singleton, ← hx] at hlen
  have hmult : localMult (integralModel I ⊔ Ideal.span {linForm u}) W =
      (Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸
        ((integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
          Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}))).toNat := by
    rw [localMult, dite_eq_left hWp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  unfold Ring.ord at hfin ⊢
  rw [hlen] at hfin ⊢
  split_ifs with hlW
  · rw [hmult, ENat.natCast_toNat hfin]
  · have hunit : IsUnit (algebraMap _ (Localization.AtPrime W) (linForm u)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ W _).mpr hlW
    have htop : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
        Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)} = ⊤ :=
      eq_top_iff.mpr (le_sup_of_le_right (Ideal.span_singleton_eq_top.mpr hunit).ge)
    rw [htop]
    have : Subsingleton (Localization.AtPrime W ⧸ (⊤ : Ideal (Localization.AtPrime W))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenChowIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace GenChowIrreducible

variable {n e : ℕ}

theorem map_specRest {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;> simp [eval₂_mul, hp]

theorem constantCoeff_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {δ : ℕ}
    (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) R} (hf : IsMultiHomog δ f)
    (y : Par e n → S) : constantCoeff (specRest φ f y) = 0 := by
  unfold specRest
  rw [← coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rw [coe_eval₂Hom, eval₂_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨j, hj⟩ : ∃ j, d (0, j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := congrFun (hf (mem_support_iff.mp hd)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero] at h0
    · omega
    · rintro ⟨i, j'⟩ _
      simp only [groupWeight, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi; simp [hcon j']
      · simp [Ne.symm hi]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (0, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

def parVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Fin n ⊕ Par e n :=
  Fin.cases (motive := fun _ => Fin n ⊕ Par e n) (.inl ij.2) (fun i => .inr (.inl (i, ij.2))) ij.1

theorem parVar_injective : Function.Injective (parVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parVar]

theorem specRest_X {k : Type*} [Field k] (f : MvPolynomial (Fin (e + 1) × Fin n) k) :
    specRest (algebraMap k (MvPolynomial (Par e n) k)) f X =
      sumAlgEquiv k (Fin n) (Par e n) (rename (parVar e n) f) := by
  unfold specRest
  rw [MvPolynomial.algebraMap_eq]
  induction f using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;>
      simp [eval₂_mul, hp, parVar, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]

theorem proof (h1 : GroundTheory.Heights₂.Heights.IncIdealPrime.Statement)
    (h2 : GroundTheory.Heights₂.Heights.ChowFormMultiHomog.Statement) : GenChowIrreducible.Statement := by
  intro k _ n e Q g hQ hg

  have hspan : GroundTheory.Heights₂.Heights.incIdeal Q (e + 1) = Ideal.span {g} := by
    ext p
    rw [Ideal.mem_span_singleton, ← hg.2 p]
    simp [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have := h1 k n (e + 1) Q hQ.isPrime hQ.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hg.1).mp this
  obtain ⟨δ, hδ, hhom⟩ := h2 k n (e + 1) Q g hQ hg

  have hren : Prime (rename (parVar e n) g) := by
    have e1 : rename (parVar e n) g = rename ((↑) : Set.range (parVar e n) → _)
        (rename (Equiv.ofInjective _ parVar_injective) g) := by
      rw [rename_rename]; rfl
    rw [e1, prime_rename_iff]
    exact (MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective _ parVar_injective))).mpr hprime
  have hpP : Prime (specRest (algebraMap k (MvPolynomial (Par e n) k)) g X) := by
    rw [specRest_X]
    exact (MulEquiv.prime_iff (sumAlgEquiv k (Fin n) (Par e n))).mpr hren
  set p := specRest (algebraMap k (MvPolynomial (Par e n) k)) g X with hp
  have hq : specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
      p.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)) := by
    rw [hp, map_specRest, ← IsScalarTower.algebraMap_eq]; rfl

  let _ : Algebra (MvPolynomial (Fin n) (MvPolynomial (Par e n) k))
      (MvPolynomial (Fin n) (GenParField k e n)) := algebraMvPolynomial
  have hc0 : constantCoeff p = 0 := constantCoeff_specRest _ hδ hhom _
  have hdisj : Disjoint
      (((nonZeroDivisors (MvPolynomial (Par e n) k)).map (C (σ := Fin n)) : Submonoid _) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Par e n) k))) ↑(Ideal.span {p}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hmem
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hmem
    obtain ⟨s, hs⟩ := hmem
    have := congrArg constantCoeff hs
    rw [constantCoeff_C, map_mul, hc0, zero_mul] at this
    exact nonZeroDivisors.ne_zero hr this
  have hpr := IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial (Par e n) k)).map (C (σ := Fin n)))
    (MvPolynomial (Fin n) (GenParField k e n)) (Ideal.span {p})
    ((Ideal.span_singleton_prime hpP.ne_zero).mpr hpP) hdisj
  rw [Ideal.map_span, Set.image_singleton, algebraMap_def] at hpr
  have hq0 : p.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)) ≠ 0 := by
    intro h
    apply hpP.ne_zero
    apply map_injective _ (IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n))
    rw [h, map_zero]
  rw [hq]
  exact ((Ideal.span_singleton_prime hq0).mp hpr).irreducible

end GenChowIrreducible

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecAlgFinite

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}

def lineSub (y : Par e n → E) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial E :=
  Fin.cases (motive := fun _ => Polynomial E)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def transVar (m : Fin n) (ij : Fin (e + 1) × Fin n) : MvPolynomial (Par e n) k :=
  Fin.cases (motive := fun _ => MvPolynomial (Par e n) k)
    (X (.inr ij.2) - if ij.2 = m then 1 else 0) (fun i => X (.inl (i, ij.2))) ij.1

def transVarInv (m : Fin n) : Par e n → MvPolynomial (Fin (e + 1) × Fin n) k
  | .inl ij => X (ij.1.succ, ij.2)
  | .inr j => X (0, j) + if j = m then 1 else 0

theorem transVar_injective (m : Fin n) :
    Function.Injective (aeval (R := k) (transVar (k := k) (e := e) m)) := by
  have h : (aeval (R := k) (transVarInv (k := k) (e := e) m)).comp (aeval (R := k) (transVar m)) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.cases with
    | zero => by_cases hj : j = m <;> simp [transVar, transVarInv, hj]
    | succ i => simp [transVar, transVarInv]
  refine Function.LeftInverse.injective (g := aeval (R := k) (transVarInv m)) fun p => ?_
  simpa using DFunLike.congr_fun h p

theorem coord_integral (h1 : IncidenceNull.Statement) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (hy : AlgebraicIndependent k y)
    (hg : IsChowForm Q (e + 1) g) (m : Fin n) :
    IsIntegral E (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  set x := secCoord Q' y with hx
  have hC : ∀ a : E, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap E (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k E) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap E (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap E (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap E (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
          Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := h1 k n (e + 1) Q g hg
  set P : Polynomial E := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj
  have hP0 : P ≠ 0 := by
    intro h0
    have h1' : Polynomial.aeval (1 : E) P = aeval y (aeval (transVar (k := k) m) g) := by
      have ha := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (1 : E)).restrictScalars k)) g
      have hb := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (transVar (k := k) m) (aeval y)) g
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at ha hb
      have hfun : (fun ij => Polynomial.aeval (1 : E) (lineSub y m ij)) =
          fun ij => aeval y (transVar (k := k) m ij) := by
        funext ⟨i, j⟩
        induction i using Fin.cases with
        | zero => by_cases hj : j = m <;> simp [lineSub, transVar, hj]
        | succ i => simp [lineSub, transVar]
      rw [hP, ha, hb, hfun]
    rw [h0, map_zero] at h1'
    exact hg.1 (transVar_injective m ((hy.eq_zero_of_aeval_eq_zero _ h1'.symm).trans
      (map_zero (aeval (R := k) (transVar (k := k) (e := e) m))).symm))
  obtain ⟨N, hN⟩ := hnil
  exact isAlgebraic_iff_isIntegral.1 ⟨P ^ N, pow_ne_zero _ hP0, by rw [map_pow, hN]⟩

end SecAlgFinite

theorem SecAlgFinite.proof (h1 : IncidenceNull.Statement) : SecAlgFinite.Statement := by
  intro k E _ _ _ n e Q g y hy _ hg
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  have htop : Algebra.adjoin E (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ E (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective E _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecAlgFinite.coord_integral h1 Q g y hy hg m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

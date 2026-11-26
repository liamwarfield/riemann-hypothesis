module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

variable {F : Type} [Field F] {n k : ℕ}

theorem chowForm_degree_unique {I : Ideal (MvPolynomial (Fin n) F)}
    {f g : MvPolynomial (Fin k × Fin n) F} (hk : 0 < k) (hf : IsChowForm I k f)
    (hg : IsChowForm I k g) {δ δ' : ℕ} (hδ : IsMultiHomog δ f) (hδ' : IsMultiHomog δ' g) :
    δ = δ' := by
  obtain ⟨q, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨r, hr⟩ : f * q ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
  have hqr : q * r = 1 := by
    have h' : f * (q * r) = f * 1 := by
      rw [mul_one, ← mul_assoc]
      exact hr.symm
    exact mul_left_cancel₀ hf.1 h'
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := q)).mp (IsUnit.of_mul_eq_one r hqr)
  have h1 : IsWeightedHomogeneous (groupWeight k n) (f * C c) ((fun _ => δ) + 0) :=
    IsWeightedHomogeneous.mul hδ (isWeightedHomogeneous_C _ c)
  rw [add_zero] at h1
  exact congrFun (IsWeightedHomogeneous.inj_right hg.1 h1 hδ') ⟨0, hk⟩

theorem ChowFormHomog.proof : ChowFormHomog.Statement := by
  intro F _ n k I f hf
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact fun d _ => funext fun i => i.elim0
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  have hdeg : chowDegree I k = a ⟨0, hk⟩ := by
    apply le_antisymm
    · exact Nat.sInf_le ⟨f, hf, hδ⟩
    · exact le_csInf ⟨_, f, hf, hδ⟩ fun δ ⟨g, hg, hδg⟩ =>
        (chowForm_degree_unique hk hf hg hδ hδg).le
  rw [hdeg]
  exact hδ

theorem chowFormHomog : ChowFormHomog.Statement := ChowFormHomog.proof

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenSecKer.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      RingHom.ker ((Ideal.Quotient.mk
          (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
        (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def SecPointSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (L : Type) [Field L] [Algebra k L]
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    [Module.Finite (GenParField k e n) L] (x : Fin n → L),
    Algebra.adjoin (GenParField k e n) (Set.range x) = ⊤ →
    (∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0) →
    ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1 →
    (∀ j₀, x j₀ ≠ 0 →
      Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable (GenParField k e n) L

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem specRest_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem ChowNormForm.proof (h₁ : ChowNormFormGeneric.Statement)
    (h₂ : SecAlgFieldChange.Statement) : ChowNormForm.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  have hinj : Function.Injective
      ((MvPolynomial.aeval y : MvPolynomial (Par e n) k →ₐ[k] E) : MvPolynomial (Par e n) k →+* E) :=
    hy
  set φ : GenParField k e n →+* E := IsFractionRing.lift hinj with hφ
  have hφC : φ.comp (algebraMap k (GenParField k e n)) = algebraMap k E := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k),
      hφ, IsFractionRing.lift_algebraMap]
    simp
  have hy' : y = φ ∘ genPar k e n := by
    funext p
    simp [hφ, genPar, IsFractionRing.lift_algebraMap]
  have hQ' : Q.map (MvPolynomial.map (algebraMap k E)) =
      (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))).map (MvPolynomial.map φ) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun p => by rw [RingHom.comp_apply, map_map, hφC]
  obtain ⟨hfin₀, c, hc, heq⟩ := h₁ k n e Q g hQ hg
  obtain ⟨hfin, hnorm⟩ := h₂ (GenParField k e n) E φ n e _ (genPar k e n) hfin₀
  rw [hQ', hy']
  refine ⟨hfin, φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [← hnorm, ← hφC, ← specRest_map, heq, _root_.map_mul, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormFormGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

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

theorem secCoord_adjoin {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _

theorem secCoord_chart {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

theorem ChowNormFormGeneric.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : GenSecSeparable.Statement) (h₄ : ChowSecDvd.Statement)
    (h₅ : NormFormIrreducible.Statement) (h₆ : GenChowIrreducible.Statement)
    (h₇ : NormFormDvd.Statement) : ChowNormFormGeneric.Statement := by
  intro k _ _ n e Q g hQ hg
  have hfin := h₁ k (GenParField k e n) n e Q g (genPar k e n)
    (genPar_algebraicIndependent k e n) hQ hg
  refine ⟨hfin, ?_⟩
  have := h₂ k n e Q g hQ hg
  have := h₃ k n e Q g hQ hg
  have hirr := h₅ (GenParField k e n) (GenSec k e Q) n _ (fun j => genPar k e n (.inr j))
    (secCoord_adjoin _ _) (secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := h₄ k (GenParField k e n) n e Q g (genPar k e n) hQ hg
  have hd := h₇ (GenParField k e n) (GenSec k e Q) n _
    ((specRest (algebraMap k (GenParField k e n)) g (genPar k e n)) ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  obtain ⟨u, hu⟩ := hirr.prime.dvd_of_dvd_pow hd
  rcases (h₆ k n e Q g hQ hg).isUnit_or_isUnit hu with hN | hu'
  · exact absurd hN hirr.not_isUnit
  obtain ⟨c, hc, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu'
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormDvd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section DvdBasis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

private def tensorPolyAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

private theorem tensorPolyAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    tensorPolyAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [tensorPolyAlgEquiv]

private def tensorPolyEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := tensorPolyAlgEquiv R A n
  invFun := (tensorPolyAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (tensorPolyAlgEquiv R A n).symm_apply_apply
  right_inv := (tensorPolyAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, tensorPolyAlgEquiv_tmul, tensorPolyAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add (f := _), map_add (f := _), hs, ht, smul_add]

private def tensorPolyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (tensorPolyEquiv R A n)

end DvdBasis

theorem NormFormDvd.proof : NormFormDvd.Statement := by
  intro R A _ _ _ _ _ n x p hdvd
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨h, hh⟩ := hdvd
  let b := Module.Free.chooseBasis R A
  let bP := tensorPolyBasis b n
  have hmap : (p.map (algebraMap R A) : MvPolynomial (Fin n) A) =
      algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p := by
    rw [MvPolynomial.algebraMap_def]
  have hnorm : Algebra.norm (MvPolynomial (Fin n) R)
      (algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p) = p ^ Module.finrank R A := by
    rw [Algebra.norm_algebraMap_of_basis bP, Module.finrank_eq_card_basis b]
  refine ⟨Algebra.norm (MvPolynomial (Fin n) R) h, ?_⟩
  rw [← hnorm, ← hmap, hh, map_mul]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem secIdealOf_eq_map (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : secIdealOf e I v W = W.map (toSecB e I v) :=
  Ideal.map_map _ _

theorem toSecB_C (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    toSecB e I v (C a) = algebraMap (ParDVR e n v) (SecB e I v)
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  simp only [toSecB, RingHom.comp_apply, MvPolynomial.map_C]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

omit [NumberField K] in
theorem mem_maximalIdeal_of_mem (e : ℕ) (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a) ∈
      IsLocalRing.maximalIdeal (ParDVR e n v) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (ParDVR e n v) (parPrime e n v) _).mpr (Ideal.mem_map_of_mem _ ha)

theorem exists_secCoord_not_mem (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (J : Ideal (SecB e I v)) (hJ : J ≠ ⊤) : ∃ j, toSecB e I v (X j) ∉ J := by
  by_contra! h
  apply hJ
  rw [Ideal.eq_top_iff_one]
  have h1 : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1, chartForm, linForm, map_sum]
  refine J.sum_mem fun j _ => ?_
  rw [map_mul]
  refine J.mul_mem_left _ ?_
  simpa [toSecB] using h j

theorem SpecMax.proof (h1 : SecBFinite.Statement) (h2 : SecIdealOfPrime.Statement) : SpecMax.Statement := by
  intro K _ _ n e I f v hI hf
  have := h1 K n e I f v hI hf
  have hcomp : ∀ W ∈ specComps I v, integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := fun W hW => hW.1.1.2

  have hmax : ∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal := by
    intro W hW
    obtain ⟨hprime, -⟩ := h2 K n e I f v hI hf W hW
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap (ParDVR e n v) (SecB e I v)) (algebraMap_isIntegral_iff.mpr inferInstance)
      (secIdealOf e I v W) ?_
    have hle : IsLocalRing.maximalIdeal (ParDVR e n v) ≤
        (secIdealOf e I v W).comap (algebraMap (ParDVR e n v) (SecB e I v)) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      change Ideal.map C v.asIdeal ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap]
      rw [← toSecB_C, secIdealOf_eq_map]
      exact Ideal.mem_map_of_mem _ (hcomp W hW (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))
    rw [← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨hmax, fun 𝔫 h𝔫 => ?_⟩

  set W' := 𝔫.comap (toSecB e I v) with hW'
  have hR : 𝔫.comap (algebraMap (ParDVR e n v) (SecB e I v)) = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap (ParDVR e n v) (SecB e I v)) (algebraMap_isIntegral_iff.mpr inferInstance) 𝔫)
  have hle : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W' := by
    refine sup_le (fun p hp => ?_) ?_
    · have h0 : toSecB e I v p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))
      rw [hW', Ideal.mem_comap, h0]
      exact 𝔫.zero_mem
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, hW', Ideal.mem_comap, toSecB_C, ← Ideal.mem_comap, hR]
      exact mem_maximalIdeal_of_mem e v ha
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le (J := W') hle
  obtain ⟨j, hj⟩ := exists_secCoord_not_mem e I v 𝔫 h𝔫.ne_top
  have hW : W ∈ specComps I v := ⟨hWmin, ⟨j, fun h => hj (hWle h)⟩⟩
  have heq : secIdealOf e I v W = 𝔫 := by
    refine (hmax W hW).eq_of_le h𝔫.ne_top ?_
    rw [secIdealOf_eq_map, Ideal.map_le_iff_le_comap]
    exact hWle
  refine ⟨W, ⟨hW, heq⟩, fun W₁ ⟨hW₁, heq₁⟩ => ?_⟩
  rw [← (h2 K n e I f v hI hf W₁ hW₁).2, ← (h2 K n e I f v hI hf W hW).2, heq, heq₁]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem SpecResidue.proof (hCSD : ChowSecDegree.Statement) (hCNF : ChowNormForm.Statement)
    (hDim : SpecCompDim.Statement) (hExist : ChowFormExists.Statement)
    (hInd : ResidueAlgIndep.Statement) : SpecResidue.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  obtain ⟨hQ, hQdim⟩ := hDim K n e I f v hI hf W hW
  obtain ⟨g, hg⟩ := hExist k n (e + 1) (reduceMod v W) hQ hQdim
  have hind := hInd K e n v
  have hfin := (hCNF k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg).1
  have hdeg := hCSD k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg

  let ι : 𝓞 K →+* R := algebraMap (𝓞 K) R
  let ρ : R →+* E := algebraMap R E
  have hρ : Function.Surjective ρ := Ideal.algebraMap_residueField_surjective _
  let Ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) E := MvPolynomial.map ρ
  have hΨ : Function.Surjective Ψ := MvPolynomial.map_surjective _ hρ
  have hcomp : ρ.comp ι = (algebraMap k E).comp (algebraMap (𝓞 K) k) := by
    ext a
    exact (Ideal.ResidueField.map_algebraMap _ _ _ _ a).symm
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p

  have hJW : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := hW.1.1.2
  let WR : Ideal (MvPolynomial (Fin n) R) := W.map (MvPolynomial.map ι)
  let S := secIdeal (modelR e I v) (parY e n v)
  let QE := (reduceMod v W).map (MvPolynomial.map (algebraMap k E))
  let T := secIdeal QE (parYκ e n v)
  have hWR : WR.map Ψ = QE := by
    simp only [WR, QE, reduceMod, Ideal.map_map, Ψ, hmm, hcomp]
    rfl
  have hM : (modelR e I v).map Ψ ≤ QE := by
    rw [← hWR]
    exact Ideal.map_mono (Ideal.map_mono (le_sup_left.trans hJW))
  have hA : (Ideal.span (Set.range (secForm (parY e n v)))).map Ψ =
      Ideal.span (Set.range (secForm (parYκ e n v))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [Ψ, secForm, linForm, parYκ, ρ]
    rfl
  have hB : (Ideal.span {chartForm (parY e n v) - 1}).map Ψ =
      Ideal.span {chartForm (parYκ e n v) - 1} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Ψ, chartForm, linForm, parYκ, ρ]
    rfl
  have hT : (S ⊔ WR).map Ψ = T := by
    simp only [S, T, secIdeal, Ideal.map_sup, hA, hB, hWR]
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (hM.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right) (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)
  have hkerΨ : RingHom.ker Ψ ≤ WR := by
    have h1 : ι = (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R).comp C :=
      IsScalarTower.algebraMap_eq _ _ _
    have hmax : IsLocalRing.maximalIdeal R = v.asIdeal.map ι := by
      rw [h1, ← Ideal.map_map]
      exact Localization.AtPrime.map_eq_maximalIdeal.symm
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField, hmax, Ideal.map_map,
      ← MvPolynomial.map_comp_C, ← Ideal.map_map]
    exact Ideal.map_mono (le_sup_right.trans hJW)

  let Φ : MvPolynomial (Fin n) R →ₐ[R] SecAlg QE (parYκ e n v) :=
    { toRingHom := (Ideal.Quotient.mk T).comp Ψ
      commutes' := fun r ↦ by
        simp [Ψ, ρ]
        rfl }
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp hΨ
  have hker : RingHom.ker Φ = S ⊔ WR := by
    have : RingHom.ker Φ = T.comap Ψ := by
      ext x
      simp [Φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [this, ← hT, Ideal.comap_map_of_surjective _ hΨ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr (hkerΨ.trans le_sup_right)
  have hsec : secIdealOf e I v W = WR.map (Ideal.Quotient.mkₐ R S) := rfl
  let eq : (SecB e I v ⧸ secIdealOf e I v W) ≃ₐ[R] SecAlg QE (parYκ e n v) :=
    ((Ideal.quotientEquivAlgOfEq R hsec).trans (DoubleQuot.quotQuotEquivQuotSupₐ R S WR)).trans
      ((Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hΦ))
  rw [eq.toLinearEquiv.length_eq, Module.length_eq_of_surjective hρ, Module.length_eq_finrank,
    hdeg]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFieldChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial
open scoped TensorProduct

noncomputable section

namespace SecAlgFieldChange

theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) {n : ℕ} (x : Fin n → A) :
    normForm A x = Matrix.det (Matrix.of fun i k => ∑ j, X j * C (b.repr (x j * b k) i)) := by
  letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
    MvPolynomial.algebraMvPolynomial
  let e₀ : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[R] MvPolynomial (Fin n) A :=
    (Algebra.TensorProduct.comm R _ A).trans
      ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)
  have he₀ : ∀ a : A, e₀ (1 ⊗ₜ a) = C a := by
    intro a; simp [e₀, MvPolynomial.smul_eq_C_mul]
  have he₁ : ∀ p, e₀ (p ⊗ₜ 1) = MvPolynomial.map (algebraMap R A) p := by
    intro p; simp [e₀]
  let e : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun p => by
      simp [Algebra.TensorProduct.algebraMap_apply, he₁])
  let B := (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map e.toLinearEquiv
  have hB : ∀ i, B i = C (b i) := by
    intro i
    simp only [B, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact he₀ (b i)
  unfold normForm
  rw [Algebra.norm_eq_matrix_det B]
  congr 1
  ext i k
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply]
  have key : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * B k =
      ∑ i, (∑ j, X j * C (b.repr (x j * b k) i)) • B i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hB, Algebra.smul_def, MvPolynomial.algebraMap_def, map_sum, map_mul,
      MvPolynomial.map_X, MvPolynomial.map_C, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← C_mul]
    conv_lhs => rw [← b.sum_repr (x j * b k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.mul_sum, Algebra.smul_def, C_mul, mul_assoc]
  rw [key, B.repr_sum_self]

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (u : Fin n → R) : MvPolynomial.map φ (linForm u) = linForm (φ ∘ u) := by
  simp [linForm]

theorem secIdeal_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e : ℕ}
    (Q₀ : Ideal (MvPolynomial (Fin n) R)) (y₀ : Par e n → R) :
    secIdeal (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀) =
      (secIdeal Q₀ y₀).map (MvPolynomial.map φ) := by
  have h1 : (MvPolynomial.map φ) ∘ secForm y₀ = secForm (φ ∘ y₀) := by
    funext i; simp [secForm, map_linForm]; rfl
  have h2 : MvPolynomial.map φ (chartForm y₀) = chartForm (φ ∘ y₀) := by
    simp [chartForm, map_linForm]; rfl
  simp only [secIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_sub, map_one, h2,
    ← Set.range_comp, h1]

end SecAlgFieldChange

theorem SecAlgFieldChange.proof : SecAlgFieldChange.Statement := by
  intro E₀ E _ _ φ n e Q₀ y₀ hfin
  classical
  letI : Algebra E₀ E := φ.toAlgebra
  have hI := SecAlgFieldChange.secIdeal_map φ Q₀ y₀
  set Q := Q₀.map (MvPolynomial.map φ)
  set y : Par e n → E := φ ∘ y₀

  let g : SecAlg Q₀ y₀ →ₐ[E₀] SecAlg Q y :=
    Ideal.quotientMapₐ (secIdeal Q y) (MvPolynomial.mapAlgHom (Algebra.ofId E₀ E))
      (by rw [hI]; exact Ideal.le_comap_map)
  have hg : ∀ p, g (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map φ p) := by
    intro p; rfl

  let ψ : SecAlg Q y →ₐ[E] E ⊗[E₀] SecAlg Q₀ y₀ :=
    Ideal.Quotient.liftₐ (secIdeal Q y)
      (aeval fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) (by
        intro a ha
        rw [hI] at ha
        have hle : (secIdeal Q₀ y₀).map (MvPolynomial.map φ) ≤
            RingHom.ker
              (MvPolynomial.aeval (R := E) fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j).toRingHom := by
          rw [Ideal.map_le_iff_le_comap]
          intro p hp
          rw [Ideal.mem_comap, RingHom.mem_ker]
          change aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j)
            (MvPolynomial.map (algebraMap E₀ E) p) = 0
          rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_one_tmul]
          have h0 : aeval (secCoord Q₀ y₀) p = 0 := by
            rw [show secCoord Q₀ y₀ = (Ideal.Quotient.mkₐ E₀ (secIdeal Q₀ y₀)) ∘ X from rfl,
              ← MvPolynomial.aeval_unique, Ideal.Quotient.mkₐ_eq_mk]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [h0, TensorProduct.tmul_zero]
        exact RingHom.mem_ker.mp (hle ha))
  have hψ : ∀ p, ψ (Ideal.Quotient.mk _ p) = aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) p :=
    fun p => rfl
  let θ : E ⊗[E₀] SecAlg Q₀ y₀ →ₐ[E] SecAlg Q y :=
    Algebra.TensorProduct.lift (Algebra.ofId E _) g (fun _ _ => Commute.all _ _)
  have hθ : ∀ a, θ (1 ⊗ₜ a) = g a := by
    intro a; simp [θ]
  let eqv : E ⊗[E₀] SecAlg Q₀ y₀ ≃ₐ[E] SecAlg Q y :=
    AlgEquiv.ofAlgHom θ ψ
      (by
        apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro j
        show θ (ψ (Ideal.Quotient.mk _ (X j))) = Ideal.Quotient.mk _ (X j)
        rw [hψ, aeval_X, hθ, secCoord, hg, map_X])
      (by
        apply Algebra.TensorProduct.ext
        · exact Subsingleton.elim _ _
        · apply Ideal.Quotient.algHom_ext
          apply MvPolynomial.algHom_ext
          intro j
          show ψ (θ (1 ⊗ₜ Ideal.Quotient.mk _ (X j))) = 1 ⊗ₜ Ideal.Quotient.mk _ (X j)
          rw [hθ, hg, map_X, hψ, aeval_X]
          rfl)
  haveI := hfin
  let b := Module.Free.chooseBasis E₀ (SecAlg Q₀ y₀)
  let B := (Algebra.TensorProduct.basis E b).map eqv.toLinearEquiv
  have hB : ∀ a i, B.repr (g a) i = φ (b.repr a i) := by
    intro a i
    have : g a = eqv.toLinearEquiv (1 ⊗ₜ a) := (hθ a).symm
    simp [B, this]
    rfl
  have hBk : ∀ k, B k = g (b k) := by
    intro k; simp [B, eqv, hθ]
  have hx : ∀ j, secCoord Q y j = g (secCoord Q₀ y₀ j) := by
    intro j; simp [secCoord, hg]
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [SecAlgFieldChange.normForm_eq_det b, SecAlgFieldChange.normForm_eq_det B, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i k => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_X, MvPolynomial.map_C, hx, hBk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_mul, hB]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormIdentity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Lemmas

variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

def chartVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (.inr ij.2) (fun i => .inl (i, ij.2)) ij.1

theorem chartVar_injective (e n : ℕ) : Function.Injective (chartVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;>
    simp_all [chartVar, Fin.cases_zero, Fin.cases_succ]

theorem parToFrac_algebraMap' (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (x : MvPolynomial (Par e n) (𝓞 K)) :
    parToFrac e n v (algebraMap _ (ParDVR e n v) x) = algebraMap _ (ParFrac K e n) x := by
  rw [parToFrac, IsLocalization.lift_eq]

theorem kToFrac_algebraMap (e n : ℕ) (a : 𝓞 K) :
    kToFrac K e n (algebraMap (𝓞 K) K a) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (C a) := by
  rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

theorem eval_specRest_chart (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    eval (fun j => parYF K e n (.inr j))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename (chartVar e n) g) := by
  have h : ((eval fun j => parYF K e n (.inr j)).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp (rename (chartVar e n)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [chartVar, parYF]
  exact congrArg (fun φ => φ g) h

theorem eval_specRest_lin (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) :
    eval (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j)))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename Sum.inl (specFirst g u)) := by
  have h : ((eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp
        ((rename (Sum.inl : Fin e × Fin n → Par e n)).toRingHom.comp (bind₁ (specFirstVar u)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [specFirstVar, parYF, kToFrac_algebraMap]
  exact congrArg (fun φ => φ g) h

theorem secLin_eq_sum {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R}
    (w : Fin n → R) : secLin Q y w = ∑ j, algebraMap R (SecAlg Q y) (w j) * secCoord Q y j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secLin, linForm, map_sum, map_mul]
  rfl

theorem chart_sum_eq_one {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)}
    {y : Par e n → R} : ∑ j, algebraMap R (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  rw [← secLin_eq_sum]
  have hmem : chartForm y - 1 ∈ secIdeal Q y := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have h := Ideal.Quotient.eq.mpr hmem
  rw [map_one] at h
  exact h

end Lemmas

theorem NormIdentity.proof (hcn : ChowNormForm.Statement) (hfin : SecBFinite.Statement)
    (htf : SecBTorsionFree.Statement) (hgen : SecBGeneric.Statement)
    (hloc : NormFormLocalization.Statement) (hev : NormFormEval.Statement)
    (hai : ParAlgIndep.Statement) (hfr : ParFracIsFractionRing.Statement)
    (hdvr : ParDVRIsDVR.Statement) : NormIdentity.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  obtain ⟨φ, hφc, hφr, hφloc⟩ := hgen K n e I v hI
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I _ v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  let _iRF : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have hFR : IsFractionRing (ParDVR e n v) (ParFrac K e n) := hfr K e n v
  let _iKF : Algebra K (ParFrac K e n) := (kToFrac K e n).toAlgebra
  let _iBL : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have _t1 : IsScalarTower (ParDVR e n v) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) :=
    IsScalarTower.of_algebraMap_eq (R := ParDVR e n v) (S := SecB e I v)
      (A := SecAlg (idealF e I) (parYF K e n)) fun r => (hφr r).symm
  have hNL := hloc (ParDVR e n v) (ParFrac K e n) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) n
    (secCoord (modelR e I v) (parY e n v))
  have hxs : (fun j => algebraMap (SecB e I v) (SecAlg (idealF e I) (parYF K e n))
      (secCoord (modelR e I v) (parY e n v) j)) = secCoord (idealF e I) (parYF K e n) := funext hφc
  rw [hxs] at hNL
  obtain ⟨-, c, -, hcn'⟩ := hcn K (ParFrac K e n) n e I (g.map (algebraMap (𝓞 K) K)) (parYF K e n)
    (hai K e n) hI hf
  set P := normForm (R := ParDVR e n v) (SecB e I v) (secCoord (modelR e I v) (parY e n v)) with hP
  replace hcn' : specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n) =
      C c * P.map (algebraMap (ParDVR e n v) (ParFrac K e n)) := by
    rw [hNL]
    exact hcn'

  have hevP : ∀ z : Fin n → ParDVR e n v,
      eval (fun j => parToFrac e n v (z j)) (P.map (algebraMap (ParDVR e n v) (ParFrac K e n))) =
        parToFrac e n v (Algebra.norm (ParDVR e n v)
          (∑ j, algebraMap (ParDVR e n v) (SecB e I v) (z j) * secCoord (modelR e I v) (parY e n v) j)) := by
    intro z
    rw [eval_map, ← hev (ParDVR e n v) (SecB e I v) n _ z, ← hP]
    show eval₂ _ _ P = parToFrac e n v (eval₂ (RingHom.id _) z P)
    rw [hom_eval₂]
    rfl

  have hT := congrArg (eval fun j => parYF K e n (.inr j)) hcn'
  rw [eval_specRest_chart, map_mul, eval_C] at hT
  have hTpt : (fun j => parYF K e n (.inr j)) = fun j => parToFrac e n v (parY e n v (.inr j)) := by
    funext j
    rw [parY, parToFrac_algebraMap']
    rfl
  rw [hTpt, hevP, chart_sum_eq_one, map_one, map_one, mul_one] at hT

  have hU := congrArg (eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) hcn'
  rw [eval_specRest_lin, map_mul, eval_C] at hU
  have hUpt : (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) =
      fun j => parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) (u j)) := by
    funext j
    rw [kToFrac_algebraMap, IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K))
      (ParDVR e n v), parToFrac_algebraMap']
    rfl
  rw [hUpt, hevP, ← secLin_eq_sum, ← hT, ← parToFrac_algebraMap', ← parToFrac_algebraMap', ← map_mul] at hU
  have hinj : Function.Injective (parToFrac e n v) := IsFractionRing.injective (ParDVR e n v) (ParFrac K e n)
  have hUR := hinj hU

  obtain ⟨m, hm⟩ := hprim
  have hnot : rename (chartVar e n) g ∈ (parPrime e n v).primeCompl := by
    intro hmem
    have hmem' : rename (chartVar e n) g ∈ Ideal.map C v.asIdeal := hmem
    rw [MvPolynomial.mem_map_C_iff] at hmem'
    have hmem := hmem'
    have := hmem (Finsupp.mapDomain (chartVar e n) m)
    rw [coeff_rename_mapDomain _ (chartVar_injective e n)] at this
    exact hm this
  have hunit : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (chartVar e n) g)) :=
    IsLocalization.map_units (ParDVR e n v) (⟨_, hnot⟩ : (parPrime e n v).primeCompl)
  exact ⟨hunit.unit, hUR⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def ChartPointTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∀ (x : Fin n → L) (j₀ : Fin n), (∀ f ∈ Q, aeval x f = 0) → x j₀ ≠ 0 →
        Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParFracIsFractionRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem ParFracIsFractionRing.proof : ParFracIsFractionRing.Statement := by
  intro K _ _ e n v
  let := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = parToFrac e n v (algebraMap _ _ x)
      unfold parToFrac
      rw [IsLocalization.lift_eq]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl
    (ParDVR e n v) (ParFrac K e n)

end

end GroundTheory.Heights₂.Heights.Vertical
end

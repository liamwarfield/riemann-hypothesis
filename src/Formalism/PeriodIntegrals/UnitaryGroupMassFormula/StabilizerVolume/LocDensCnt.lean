module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHL

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntD
noncomputable section

namespace PI.VolStabS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨_, hE, _, hτ⟩ := hCM
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    haveI := hE
    have hc := IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
    apply hc
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hτ, hall]
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv]
  abel

theorem anti_coeff (σ : E →ₐ[F] E) {δ : E} (hδ0 : δ ≠ 0) (hσδ : σ δ = -δ) (s t : F)
    (h : σ (s • (1 : E) + t • δ) = s • 1 + t • δ) : t = 0 := by
  simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgHom.commutes, map_one, hσδ, mul_one] at h
  have h2 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (algebraMap F E).injective (by rw [h4, map_zero])
    · exact absurd h4 hδ0

theorem exists_basis_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      apply anti_coeff σ hδ0 hσδ s t
      rw [hst, map_zero]
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right one_ne_zero, rfl⟩
  let c := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hc : ⇑c = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  obtain ⟨s, t, hst⟩ : ∃ s t : F, δ * δ = s • (1 : E) + t • δ := by
    have hsum := c.sum_repr (δ * δ)
    rw [Fin.sum_univ_two, hc] at hsum
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
    exact ⟨_, _, hsum.symm⟩
  have ht : t = 0 := by
    apply anti_coeff σ hδ0 hσδ s t
    rw [← hst, map_mul, hσδ, neg_mul_neg]
  subst ht
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  refine ⟨δ, s, c, hδ0, hσδ, hst, ?_, by simp [hc], by simp [hc]⟩
  rintro rfl
  rw [map_zero] at hst
  exact hδ0 (mul_self_eq_zero.mp hst)

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntQ
noncomputable section

namespace PI.VolStabS

open Polynomial

private theorem bijective_algebraMap_add_mul_of_finrank_two {k K : Type} [Field k] [CommRing K]
    [Algebra k K] [Module.Finite k K] (hK : Module.finrank k K = 2) (r : K)
    (h0 : ∀ a b : k, algebraMap k K a + algebraMap k K b * r = 0 → a = 0 ∧ b = 0) :
    Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  let L : (k × k) →ₗ[k] K :=
    (LinearMap.fst k k k).smulRight (1 : K) + (LinearMap.snd k k k).smulRight r
  have hL : ∀ p : k × k, L p = algebraMap k K p.1 + algebraMap k K p.2 * r := by
    intro p
    simp [L, Algebra.smul_def]
  have hfun : (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) = ⇑L :=
    funext fun p => (hL p).symm
  rw [hfun]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    obtain ⟨h1, h2⟩ := h0 p.1 p.2 hp
    exact Prod.ext h1 h2
  have H : Module.finrank k (k × k) = Module.finrank k K := by
    rw [hK]
    simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mp hinj⟩

private theorem exists_algEquiv_prod_swap (k : Type) [Field k] :
    ∃ σ : (k × k) ≃ₐ[k] (k × k), ∀ x, σ x = x.swap :=
  ⟨{ toFun := Prod.swap
     invFun := Prod.swap
     left_inv := fun x => Prod.swap_swap x
     right_inv := fun x => Prod.swap_swap x
     map_mul' := fun x y => rfl
     map_add' := fun x y => rfl
     commutes' := fun c => rfl }, fun x => rfl⟩

private theorem isQuadInv_and_bijective_of_not_isSquare (k K : Type) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) (hsq : ¬ IsSquare D)
    (hK : Module.finrank k K = 2) (r : K) (hr : r * r = algebraMap k K D)
    (σ' : K ≃ₐ[k] K) (hσ : σ' r = -r) (hinv : ∀ x, σ' (σ' x) = x) :
    IsQuadInv k K σ' ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h11 : algebraMap k K (1 + 1) = 0 := by
      rw [map_add (f := _), map_one]
      linear_combination h
    have h11' : (1 + 1 : k) = 0 := (algebraMap k K).injective (h11.trans (map_zero _).symm)
    exact h2 (by linear_combination h11')
  refine ⟨⟨hinv, Or.inl ⟨Field.toIsField K, hK, ?_⟩⟩, ?_⟩
  · intro hσr
    have h1 : r = -r := by
      simpa [hσr] using hσ
    have hr0 : r = 0 := by
      have h2r : (2 : K) * r = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2r).resolve_left h2K
    apply hD
    apply (algebraMap k K).injective
    rw [← hr, hr0, mul_zero, map_zero]
  · apply bijective_algebraMap_add_mul_of_finrank_two hK r
    intro a b h
    by_cases hb : b = 0
    · subst hb
      simp only [map_zero, zero_mul, add_zero] at h
      refine ⟨?_, rfl⟩
      apply (algebraMap k K).injective
      rw [h, map_zero]
    · exfalso
      apply hsq
      refine ⟨-a / b, ?_⟩
      apply (algebraMap k K).injective
      have hbK : algebraMap k K b ≠ 0 := (_root_.map_ne_zero _).mpr hb
      have hrc : r = algebraMap k K (-a / b) := by
        rw [map_div₀, map_neg, eq_div_iff hbK]
        linear_combination h
      rw [← hr, hrc, map_mul]

theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  by_cases hsq : IsSquare D
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hD (by rw [hs, h, mul_zero])
    obtain ⟨σ, hσ⟩ := exists_algEquiv_prod_swap k
    refine ⟨k × k, inferInstance, inferInstance, σ, (s, -s), ?_, ?_, ?_, ?_⟩
    · refine ⟨fun x => by rw [hσ, hσ, Prod.swap_swap], Or.inr ⟨AlgEquiv.refl, fun x => ?_⟩⟩
      rw [hσ]
      rfl
    · ext <;> simp [hs]
    · rw [hσ]
      ext <;> simp
    · apply bijective_algebraMap_add_mul_of_finrank_two
      · simp
      · intro a b h
        have e1 : a + b * s = 0 := by
          exact congrArg Prod.fst h
        have e2 : a + b * -s = 0 := by
          exact congrArg Prod.snd h
        have hb : (2 * s) * b = 0 := by linear_combination e1 - e2
        have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h2 hs0)
        refine ⟨?_, hb0⟩
        linear_combination e1 - s * hb0
  · have hroot : ∀ b : k, b ^ 2 ≠ D := fun b hb => hsq ⟨b, by rw [← hb, sq]⟩
    have hirr : Irreducible (X ^ 2 - C D : k[X]) := by
      exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
    have : Fact (Irreducible (X ^ 2 - C D : k[X])) := ⟨hirr⟩
    have hf0 : (X ^ 2 - C D : k[X]) ≠ 0 := hirr.ne_zero
    have hfin : Module.finrank k (AdjoinRoot (X ^ 2 - C D : k[X])) = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]
    have : Module.Finite k (AdjoinRoot (X ^ 2 - C D : k[X])) := (AdjoinRoot.powerBasis hf0).finite
    have hr : AdjoinRoot.root (X ^ 2 - C D : k[X]) * AdjoinRoot.root (X ^ 2 - C D : k[X]) =
        algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])) D := by
      have h0 : aeval (AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simp only [map_sub, aeval_X_pow, aeval_C] at h0
      linear_combination h0
    have hneg : aeval (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      simp only [map_sub, aeval_X_pow, aeval_C]
      linear_combination hr
    have hneg' : eval₂ (algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])))
        (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      rw [← aeval_def]
      exact hneg
    obtain ⟨τ, hτr⟩ : ∃ τ : AdjoinRoot (X ^ 2 - C D : k[X]) →ₐ[k] AdjoinRoot (X ^ 2 - C D : k[X]),
        τ (AdjoinRoot.root _) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) := by
      exact ⟨{ AdjoinRoot.lift (algebraMap k _) (-AdjoinRoot.root _) hneg' with
          commutes' := fun c => by simp [AdjoinRoot.algebraMap_eq] }, AdjoinRoot.lift_root hneg'⟩
    have hττ : τ.comp τ = AlgHom.id k _ := by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hτr, map_neg, hτr, neg_neg, AlgHom.id_apply]
    let σ' := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσ : σ' (AdjoinRoot.root (X ^ 2 - C D : k[X])) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) :=
      hτr
    have hinv : ∀ x, σ' (σ' x) = x := fun x => DFunLike.congr_fun hττ x
    obtain ⟨hq, hbij⟩ := isQuadInv_and_bijective_of_not_isSquare k (AdjoinRoot (X ^ 2 - C D : k[X])) h2 D hD hsq hfin
      (AdjoinRoot.root _) hr σ' hσ hinv
    exact ⟨AdjoinRoot (X ^ 2 - C D : k[X]), inferInstance, inferInstance, σ',
      AdjoinRoot.root _, hq, hr, hσ, hbij⟩

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem sigR_incl (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  first
    | rfl
    | simp [sigR, inclR]

theorem two_ne_zero_k (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1) :
    (2 : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
  intro h0
  have hmem : (2 : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    first
      | (rw [map_ofNat]; exact h0)
      | exact h0
      | exact_mod_cast h0
  have hv : v.intValuation (2 : 𝓞 F) = 1 := by
    have e : algebraMap F (Fv F v) 2 = ((2 : F) : v.adicCompletion F) := rfl
    have e2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', e2,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at h2
    exact h2
  have hlt : v.intValuation (2 : 𝓞 F) < 1 := by
    first
      | exact (v.intValuation_lt_one_iff_mem _).2 hmem
      | exact (v.intValuation_lt_one_iff_dvd _).2 ((Ideal.dvd_span_singleton).2 hmem)
  exact absurd hv (ne_of_lt hlt)

end Place

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)
  (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)

def entL {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F) :
    Matrix (Fin n) (Fin n) (lamC v A hD) :=
  Matrix.of fun p q => ⟨inclR (Fv F v) (G p q), incl_mem v A hD _ (hG p q)⟩

variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
  (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)

include hσr in
theorem cnt_herm {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (hGs : ∀ i j, σ (G j i) = G i j)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (i j : Fin n) :
    σ' (((entL v A hD G hG).map (rho v A hD r hr)) j i) = ((entL v A hD G hG).map (rho v A hD r hr)) i j := by
  simp only [Matrix.map_apply]
  rw [← rho_sig v A hD r hr σ' hσr]
  congr 1
  apply Subtype.ext
  rw [coe_sigC]
  show sigR (Fv F v) σ (inclR (Fv F v) (G j i)) = inclR (Fv F v) (G i j)
  rw [sigR_incl, hGs]

theorem cnt_unit {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (u : E) (hu : G.det * u = 1)
    (hui : ∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) :
    IsUnit ((entL v A hD G hG).map (rho v A hD r hr)).det := by
  have hdet : ((entL v A hD G hG).det : Fv F v ⊗[F] E) = inclR (Fv F v) G.det := by
    have e1 := RingHom.map_det (lamC v A hD).subtype (entL v A hD G hG)
    rw [RingHom.mapMatrix_apply] at e1
    have e2 := RingHom.map_det (inclR (Fv F v) (F := F) (E := E)) G
    rw [RingHom.mapMatrix_apply] at e2
    rw [show ((entL v A hD G hG).det : Fv F v ⊗[F] E) = (lamC v A hD).subtype (entL v A hD G hG).det
      from rfl, e1, e2]
    rfl
  have hu' : (entL v A hD G hG).det * ⟨inclR (Fv F v) u, incl_mem v A hD u hui⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdet, Subring.coe_one]
    show inclR (Fv F v) G.det * inclR (Fv F v) u = 1
    rw [← map_mul, hu, map_one]
  have e3 := RingHom.map_det (rho v A hD r hr) (entL v A hD G hG)
  rw [RingHom.mapMatrix_apply] at e3
  rw [← e3]
  exact (isUnit_iff_exists_inv.2 ⟨_, hu'⟩).map _

variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))

include hσr hbij in
set_option maxHeartbeats 400000 in
theorem cnt_meas [Finite K] (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K)
          ((entL v A hD J hJi).map (rho v A hD r hr)) X = (entL v A hD T hTi).map (rho v A hD r hr)} : ENNReal) *
          μ (lamF b v a M 0) := by
  classical
  have rs := rho_sig v A hD r hr σ' hσr
  have rz := rho_eq_zero v A hD r hr hbij
  have rsu := rho_surj v A hD r hr hbij
  generalize rho v A hD r hr = ρ at rs rz rsu ⊢
  obtain ⟨rT, rT_eq⟩ : ∃ f : Fv F v ⊗[F] E → K, ∀ z (h : z ∈ lamC v A hD), f z = ρ ⟨z, h⟩ :=
    ⟨fun z => if h : z ∈ lamC v A hD then ρ ⟨z, h⟩ else 0, fun z h => dif_pos h⟩
  have memL : ∀ Y, Y ∈ latSub b v a M ↔ ∀ i p, Y i p ∈ lamC v A hD := by
    intro Y
    show (∀ i p k, _ ∈ _) ↔ _
    refine forall_congr' fun i => forall_congr' fun p => ?_
    rw [int_iff v b A.c hbc hcb, Fin.forall_fin_two]
    exact Iff.rfl
  have memN : ∀ Y, Y ∈ lamF b v a M 0 ↔
      ∀ i p, ∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = Y i p := by
    intro Y
    rw [lamF, mem_smulSub, zero_add, pow_one]
    constructor
    · rintro ⟨Y', hY', rfl⟩ i p
      exact ⟨Y' i p, (memL Y').1 hY' i p, rfl⟩
    · intro h
      choose f hf1 hf2 using h
      exact ⟨f, (memL f).2 hf1, funext fun i => funext fun p => hf2 i p⟩
  have hsm : ∀ w : lamC v A hD,
      (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = (w : Fv F v ⊗[F] E)) ↔ ρ w = 0 := by
    intro w
    rw [smul_char v A hD, rz]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  have hNL : lamF b v a M 0 ≤ latSub b v a M := by
    intro Y hY
    rw [memN] at hY
    rw [memL]
    intro i p
    obtain ⟨z', hz', e⟩ := hY i p
    rw [← e]
    exact ((smul_char v A hD _).1 ⟨z', hz', rfl⟩).1
  have hker : ∀ Y ∈ latSub b v a M, (fun i p => rT (Y i p)) = 0 ↔ Y ∈ lamF b v a M 0 := by
    intro Y hY
    rw [memN, funext_iff]
    refine forall_congr' fun i => ?_
    rw [funext_iff]
    refine forall_congr' fun p => ?_
    have h1 := (memL Y).1 hY i p
    rw [hsm ⟨Y i p, h1⟩]
    show rT (Y i p) = 0 ↔ _
    rw [rT_eq _ h1]
  have hadd : ∀ Y ∈ latSub b v a M, ∀ Y' ∈ latSub b v a M,
      (fun i p => rT ((Y + Y') i p)) = (fun i p => rT (Y i p)) + (fun i p => rT (Y' i p)) := by
    intro Y hY Y' hY'
    funext i p
    have h1 := (memL Y).1 hY i p
    have h2 := (memL Y').1 hY' i p
    show rT (Y i p + Y' i p) = rT (Y i p) + rT (Y' i p)
    rw [rT_eq _ (add_mem h1 h2), rT_eq _ h1, rT_eq _ h2, ← map_add (f := _)]
    rfl
  have hsurj : ∀ W : Fin a → Fin M → K, ∃ Y ∈ latSub b v a M, (fun i p => rT (Y i p)) = W := by
    intro W
    choose g hg using fun i p => rsu (W i p)
    refine ⟨fun i p => (g i p : Fv F v ⊗[F] E), (memL _).2 fun i p => (g i p).2, ?_⟩
    funext i p
    show rT (g i p : Fv F v ⊗[F] E) = W i p
    rw [rT_eq _ (g i p).2]
    exact hg i p
  have rT_mul : ∀ z w, z ∈ lamC v A hD → w ∈ lamC v A hD → rT (z * w) = rT z * rT w := by
    intro z w hz hw
    rw [rT_eq _ (mul_mem hz hw), rT_eq _ hz, rT_eq _ hw, ← map_mul]
    rfl
  have rT_sub : ∀ z w, z ∈ lamC v A hD → w ∈ lamC v A hD → rT (z - w) = rT z - rT w := by
    intro z w hz hw
    rw [rT_eq _ (sub_mem hz hw), rT_eq _ hz, rT_eq _ hw, ← map_sub]
    rfl
  have rT_sig : ∀ z, z ∈ lamC v A hD → rT (sigR (Fv F v) σ z) = σ' (rT z) := by
    intro z hz
    rw [rT_eq _ (sig_mem v A hD hz), rT_eq _ hz, ← rs ⟨z, hz⟩]
    rfl
  have rT_sum : ∀ (s : Finset (Fin M)) (f : Fin M → Fv F v ⊗[F] E),
      (∀ p, f p ∈ lamC v A hD) → rT (∑ p ∈ s, f p) = ∑ p ∈ s, rT (f p) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, rT_eq _ (zero_mem _), ← map_zero ρ]
      rfl
    | insert p s hp ih =>
      have hs : ∑ q ∈ s, f q ∈ lamC v A hD := sum_mem fun q _ => hf q
      rw [Finset.sum_insert hp, Finset.sum_insert hp, ← ih, rT_eq _ (add_mem (hf p) hs),
        rT_eq _ (hf p), rT_eq _ hs, ← map_add]
      rfl
  have hsm' : ∀ z, z ∈ lamC v A hD →
      ((∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔ rT z = 0) := by
    intro z hz
    rw [rT_eq _ hz]
    exact hsm ⟨z, hz⟩
  have hentry : ∀ Y, (∀ i p, Y i p ∈ lamC v A hD) → ∀ i j,
      ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) ∈ lamC v A hD ∧
      rT ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) =
        ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) (fun i p => rT (Y i p)) i j := by
    intro Y hY i j
    have e1 : ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) =
        ∑ p, ∑ q, sigR (Fv F v) σ (Y i p) * inclR (Fv F v) (J p q) * Y j q := rfl
    have hmem : ∀ p q, sigR (Fv F v) σ (Y i p) * inclR (Fv F v) (J p q) * Y j q ∈ lamC v A hD :=
      fun p q => mul_mem (mul_mem (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q))) (hY j q)
    rw [e1]
    refine ⟨sum_mem fun p _ => sum_mem fun q _ => hmem p q, ?_⟩
    rw [rT_sum _ _ fun p => sum_mem fun q _ => hmem p q]
    show _ = ∑ p, ∑ q, (σ' : K →+* K) (rT (Y i p)) * ρ (entL v A hD J hJi p q) * rT (Y j q)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rT_sum _ _ fun q => hmem p q]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [rT_mul _ _ (mul_mem (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q))) (hY j q),
      rT_mul _ _ (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q)), rT_sig _ (hY i p),
      rT_eq _ (incl_mem v A hD _ (hJi p q))]
    rfl
  have hFm : ∀ S : HermR (Fv F v) σ a, S ∈ hF b v σ a 0 ↔
      ∀ i j, ∃ z', z' ∈ lamC v A hD ∧
        unifV v • z' = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
    intro S
    rw [hF, mem_smulSub, zero_add, pow_one]
    constructor
    · rintro ⟨S', hS', rfl⟩ i j
      have hS'' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F := hS'
      have hc := (int_iff v b A.c hbc hcb _).1 (hS'' i j)
      exact ⟨(S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, ⟨hc 0, hc 1⟩, rfl⟩
    · intro h
      choose f hf1 hf2 using h
      refine ⟨(unifV v)⁻¹ • S, ?_, ?_⟩
      · intro i j
        show ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((((unifV v)⁻¹ • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ _
        rw [coe_hermSMul, Matrix.smul_apply, ← hf2 i j, smul_smul,
          inv_mul_cancel₀ (unifV_spec v).1, one_smul]
        exact (int_iff v b A.c hbc hcb _).2 (Fin.forall_fin_two.2 (hf1 i j))
      · apply Subtype.ext
        rw [coe_hermSMul, coe_hermSMul, smul_smul, mul_inv_cancel₀ (unifV_spec v).1, one_smul]
  have hset : latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
        {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0} =
      {Y | Y ∈ latSub b v a M ∧ (fun i p => rT (Y i p)) ∈
        {X | ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) X = (entL v A hD T hTi).map ρ}} := by
    ext Y
    show (Y ∈ latSub b v a M ∧ _) ↔ (Y ∈ latSub b v a M ∧ _)
    refine and_congr_right fun hY => ?_
    have hY' := (memL Y).1 hY
    show _ ∈ hF b v σ a 0 ↔ ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) (fun i p => rT (Y i p)) =
      (entL v A hD T hTi).map ρ
    rw [hFm, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    obtain ⟨hg1, hg2⟩ := hentry Y hY' i j
    have hTm := incl_mem v A hD _ (hTi i j)
    have e : ((gramH (Fv F v) σ hσ J hJ Y - hermOf (Fv F v) σ T hT : HermR (Fv F v) σ a) :
        Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
        (gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j -
          inclR (Fv F v) (T i j) := rfl
    rw [e, hsm' _ (sub_mem hg1 hTm), rT_sub _ _ hg1 hTm, sub_eq_zero, hg2, rT_eq _ hTm]
    exact Iff.rfl
  rw [hset, measure_count μ (latSub b v a M) (lamF b v a M 0) hNL hNm (fun Y i p => rT (Y i p))
    hadd hker hsurj]
  rfl

end Meas

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem cnt_at (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
    (hDu : Valued.v (algebraMap F (Fv F v) A.D0) = 1)
    (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
      (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
      IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧
      (∀ u : E, J.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit J'.det) ∧
      (∀ i j, σ' (T' j i) = T' i j) ∧
      (∀ u : E, T.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit T'.det) ∧
      Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
      μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
          μ (lamF b v a M 0) := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let fk : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have h2k := two_ne_zero_k v h2
  have hDk : red v (algebraMap F (Fv F v) A.D0) ≠ 0 := by
    rw [Ne, red_eq_zero_iff v hD, hDu]; exact lt_irrefl 1
  obtain ⟨K, iK, iA, σ', r, hQ, hr, hσr, hbij⟩ := exists_quadAlg (𝓞 F ⧸ v.asIdeal) h2k _ hDk
  have : Finite K := Finite.of_surjective _ hbij.2
  exact ⟨𝓞 F ⧸ v.asIdeal, K, fk, hfin, iK, iA, σ', (entL v A hD J hJi).map (rho v A hD r hr),
    (entL v A hD T hTi).map (rho v A hD r hr), hQ, h2k,
    cnt_herm v A hD r hr σ' hσr J hJ hJi, fun u hu hui => cnt_unit v A hD r hr J hJi u hu hui,
    cnt_herm v A hD r hr σ' hσr T hT hTi, fun u hu hui => cnt_unit v A hD r hr T hTi u hu hui, rfl,
    cnt_meas v A hD r hr σ' hσr hbij hσ J hJ T hT b hbc hcb hJi hTi hNm μ⟩

end Place

theorem cntAA_holds : CntAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨δ, D0, c, hδ0, hσδ, hδ, hD0, hc0, hc1⟩ := exists_basis_anti σ hCM
  let A : AntiB F E σ := ⟨δ, D0, c, hc0, hc1, hδ, hσδ, hD0⟩
  have hJdet : J.det ≠ 0 := hJ.2
  filter_upwards [ev_int (F := F) D0, ev_unit hD0, ev_unit (two_ne_zero : (2 : F) ≠ 0),
    eventually_all.2 fun j => eventually_all.2 fun k => ev_int (F := F) (b.repr (c j) k),
    eventually_all.2 fun k => eventually_all.2 fun j => ev_int (F := F) (c.repr (b k) j),
    eventually_all.2 fun p => eventually_all.2 fun q => eventually_all.2 fun j =>
      ev_int (F := F) (c.repr (J p q) j),
    eventually_all.2 fun p => eventually_all.2 fun q => eventually_all.2 fun j =>
      ev_int (F := F) (c.repr (gramE σ J X0 p q) j),
    eventually_all.2 fun j => ev_int (F := F) (c.repr (J.det)⁻¹ j),
    eventually_all.2 fun j => ev_int (F := F) (c.repr ((gramE σ J X0).det)⁻¹ j)]
    with v hD hDu h2 hbc hcb hJi hTi hJu hTu
  intro μ hμ
  haveI := hμ
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    ((latFacts_holds F E σ d b a M v).1 0).measurableSet
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2k, hJ', hJu', hT', hTu', hcard, hmeas⟩ :=
    cnt_at v A (sigma_invol σ hCM.2.2.2) J hJ.1 (gramE σ J X0) hT b hbc hcb hD hDu h2 hJi hTi
      hNm μ
  exact ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2k, hJ', hJu' _ (mul_inv_cancel₀ hJdet) hJu, hT',
    hTu' _ (mul_inv_cancel₀ hdet) hTu, hcard, hmeas⟩

end PI.VolStabS

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDeltaEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrient
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTraceType
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem tau_bar (A : Arith E) (τ : E →+* ℂ) :
    τ ((algebraMap (𝓞 E) E) (A.bar A.ω)) = (starRingEnd ℂ) (τ (A.ω : E)) := by
  show τ ((A.bar A.ω : 𝓞 E) : E) = _
  rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]

private theorem tau_add (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) + (starRingEnd ℂ) (τ (A.ω : E)) = (A.tr : ℂ) := by
  have h1 := congrArg (fun x : 𝓞 E => τ (x : E)) A.tr_eq
  simp only [map_add (f := _), map_intCast] at h1
  rw [tau_bar A τ] at h1
  exact h1

private theorem tau_mul (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) * (starRingEnd ℂ) (τ (A.ω : E)) = (A.nm : ℂ) := by
  have h1 := congrArg (fun x : 𝓞 E => τ (x : E)) A.nm_eq
  simp only [map_mul, map_intCast] at h1
  rw [tau_bar A τ] at h1
  exact h1

private theorem tau_im (A : Arith E) (τ : E →+* ℂ) : (τ (A.ω : E)).im ≠ 0 := by
  intro h
  have hc : (starRingEnd ℂ) (τ (A.ω : E)) = τ (A.ω : E) := Complex.conj_eq_iff_im.2 h
  have h1 := tau_add A τ
  have h2 := tau_mul A τ
  rw [hc] at h1 h2
  have h3 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : ℂ) = 0 := by
    push_cast
    rw [← h1, ← h2]
    ring
  have h4 : A.tr ^ 2 - 4 * A.nm = 0 := by exact_mod_cast h3
  have := A.disc_neg
  linarith

private theorem tau_cases (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) = A.τ₀ (A.ω : E) ∨ τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E)) := by
  have h : (τ (A.ω : E) - A.τ₀ (A.ω : E)) * (τ (A.ω : E) - (starRingEnd ℂ) (A.τ₀ (A.ω : E))) = 0 := by
    linear_combination τ (A.ω : E) * tau_add A τ - tau_mul A τ - τ (A.ω : E) * tau_add A A.τ₀ + tau_mul A A.τ₀
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

private theorem rho_ne (A : Arith E) : A.τ₀ (A.ω : E) ≠ (starRingEnd ℂ) (A.τ₀ (A.ω : E)) :=
  fun h => tau_im A A.τ₀ (Complex.conj_eq_iff_im.1 h.symm)

private theorem conj_mem (A : Arith E) (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ) (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) :=
  ComplexEmbedding.conjugate_coe_eq τ _

private theorem sum_conj (A : Arith E) [Fintype (Phi A)]
    [DecidablePred fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))]
    (f : (E →+* ℂ) → ℂ) :
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))), f τ =
      ∑ τ : Phi A, f (ComplexEmbedding.conjugate τ.1) := by
  classical
  refine Eq.trans ?_ (Finset.sum_subtype
    (Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))) (by simp)
    (fun τ => f (ComplexEmbedding.conjugate τ)))
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conj_mem, hτ', Complex.conj_conj]
  · intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conj_mem, hτ']
  · intro τ _
    exact star_star τ
  · intro τ _
    exact star_star τ
  · intro τ _
    rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ]

private theorem trace_eq (x : E) :
    (((Algebra.trace ℚ E x : ℚ) : ℂ)) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

end UpperTheory.Gal.W2.Seed

open Classical in
theorem UpperTheory.Gal.W2.Seed.pTraceType :
    TraceType := by
  intro E _ _ _ A
  have h2 := fun f => sum_conj A f
  refine ⟨fun x => ?_, h2, fun v => ?_, tau_im A A.τ₀⟩
  · apply Complex.ofReal_injective
    have h1 : ((((Algebra.trace ℚ E x : ℚ) : ℝ)) : ℂ) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by push_cast; rfl
    rw [h1, trace_eq x,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))]
    have h3 : Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (A.ω : E) = A.τ₀ (A.ω : E)) =
        Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact (tau_cases A τ).resolve_left h
      · intro h h'
        exact rho_ne A (h'.symm.trans h)
    have h4 : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E)), τ x =
        ∑ τ : Phi A, τ.1 x := Finset.sum_subtype _ (by simp) _
    rw [h3, h2 (fun τ => τ x), h4, ← Finset.sum_add_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  · have hmem : ∃ τ : Phi A, InfinitePlace.mk τ.1 = v := by
      rcases tau_cases A v.embedding with h | h
      · exact ⟨⟨v.embedding, h⟩, v.mk_embedding⟩
      · refine ⟨⟨ComplexEmbedding.conjugate v.embedding, ?_⟩, ?_⟩
        · rw [conj_mem, h, Complex.conj_conj]
        · rw [InfinitePlace.mk_conjugate_eq, v.mk_embedding]
    obtain ⟨τ, hτ⟩ := hmem
    refine ⟨τ, hτ, fun σ hσ => ?_⟩
    rcases InfinitePlace.mk_eq_iff.1 (hσ.trans hτ.symm) with h | h
    · exact Subtype.ext h
    · exfalso
      have h5 : τ.1 (A.ω : E) = (starRingEnd ℂ) (σ.1 (A.ω : E)) := by rw [← h, conj_mem]
      rw [τ.2, σ.2] at h5
      exact rho_ne A h5
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PBarEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pBarEx :
    BarEx := by
  intro E _ _ _
  refine ⟨(IsCMField.ringOfIntegersComplexConj E).toRingEquiv, fun a => ?_⟩
  exact IsCMField.coe_ringOfIntegersComplexConj E a
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDomSt
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private noncomputable def UpperTheory.Gal.W2.Seed.pDomSt_dL {I : Type} (a : I → ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun z k := a k * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' r z := by funext k; simp [mul_left_comm]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_theta_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) {n : ℕ}
    (Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ))
    (hΘ : ∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E))
    (b : 𝓞 E) (M : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E))
    (hM : ∀ x : Fin n → 𝓞 E, M (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) (x : ℝ ⊗[ℤ] (Fin n → 𝓞 E)) (k : Phi A × Fin n) :
    Θ (M x) k = k.1.1 (b : E) * Θ x k := by
  obtain ⟨τ, i⟩ := k
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    have h : r ⊗ₜ[ℤ] y = r • ((1 : ℝ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, LinearMap.map_smul, hM, LinearEquiv.map_smul, LinearEquiv.map_smul, Pi.smul_apply, Pi.smul_apply,
      hΘ, hΘ, Complex.real_smul, Complex.real_smul]
    simp [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb, mul_add]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_term (D H z : ℂ) (e : ℝ) (hD : D.re = 0) (hH : H.im = 0) :
    (D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z).re = -D.im * H.re * e * Complex.normSq z := by
  have hD' : D = (D.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hD]
  have hH' : H = (H.re : ℂ) := by
    apply Complex.ext <;> simp [hH]
  have h1 : D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z
      = D * H * e * Complex.I * (z * (starRingEnd ℂ) z) := by ring
  rw [h1, Complex.mul_conj, hD', hH']
  have h2 : (D.im : ℂ) * Complex.I * (H.re : ℂ) * (e : ℂ) * Complex.I * (Complex.normSq z : ℂ)
      = ((-D.im * H.re * e * Complex.normSq z : ℝ) : ℂ) := by
    push_cast
    linear_combination ((D.im : ℂ) * H.re * e * Complex.normSq z) * Complex.I_sq
  rw [h2, Complex.ofReal_re]
  simp

private theorem UpperTheory.Gal.W2.Seed.pDomSt_sum {I : Type} [Fintype I] [DecidableEq I] (k0 : I) (y : I → ℝ) :
    ∑ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * y k0 - ∑ k, y k := by
  have h : ∀ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * (if k = k0 then y k else 0) - y k := by
    intro k
    split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem UpperTheory.Gal.W2.Seed.pDomSt :
    TraceType → RealIso → FormCoord → HdSign → DiagTrace → DomSt := by
  intro hT hR hF hS hD E _ _ _ A n hn
  classical
  obtain ⟨Θ, hΘ⟩ := hR E A n
  obtain ⟨-, hsum, -, him⟩ := hT E A
  let k0 : Phi A × Fin n := (⟨A.τ₀, rfl⟩, ⟨0, hn⟩)
  have hk0 : ∀ k : Phi A × Fin n,
      (InfinitePlace.mk k.1.1 = InfinitePlace.mk A.τ₀ ∧ (k.2 : ℕ) = 0) ↔ k = k0 := by
    rintro ⟨⟨τ, hτ⟩, i⟩
    constructor
    · rintro ⟨h1, h2⟩
      rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
      · exact Prod.ext (Subtype.ext h) (Fin.ext h2)
      · exfalso
        apply him
        have h3 : A.τ₀ (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) := by
          rw [← h, ComplexEmbedding.conjugate_coe_eq]
        rw [hτ] at h3
        exact Complex.conj_eq_iff_im.mp h3.symm
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  let ε : Phi A × Fin n → ℝ := fun k => if k = k0 then 1 else -1
  let a : Phi A × Fin n → ℂ := fun k => (ε k : ℂ) * Complex.I
  have ha2 : ∀ k, a k * a k = -1 := by
    intro k
    have h' : (ε k : ℂ) * (ε k) = 1 := by
      simp only [ε]
      split_ifs <;> norm_num
    simp only [a]
    linear_combination Complex.I ^ 2 * h' + Complex.I_sq
  have hca : ∀ k, (starRingEnd ℂ) (a k) = -a k := by
    intro k
    simp only [a, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  let J := Θ.symm.toLinearMap ∘ₗ pDomSt_dL a ∘ₗ Θ.toLinearMap
  have hJ : ∀ x k, Θ (J x) k = a k * Θ x k := by
    intro x k
    simp [J, pDomSt_dL]
  have hpos : ∀ k : Phi A × Fin n, 0 < -(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k) := by
    intro k
    have h1 := A.δ_sign k.1.1 k.1.2
    obtain ⟨-, -, hp, hm⟩ := hS E A n k.1.1 k.2
    have h2 : 0 < (k.1.1 (A.hd n k.2 : E)).re * ε k := by
      by_cases hk : k = k0
      · have := hp ((hk0 k).mpr hk)
        rw [show ε k = 1 from if_pos hk, mul_one]
        exact this
      · have := hm (fun h => hk ((hk0 k).mp h))
        rw [show ε k = -1 from if_neg hk, mul_neg_one]
        linarith
    exact mul_pos (by linarith) h2
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Θ.injective
    funext k
    rw [hJ, hJ, map_neg, Pi.neg_apply, ← mul_assoc, ha2]
    ring
  · intro x y
    rw [hF E A n Θ hΘ, hF E A n Θ hΘ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hJ, hJ, map_mul, hca]
    congr 2
    linear_combination (-(k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ x k * (starRingEnd ℂ) (Θ y k))) * ha2 k
  · intro x hx
    rw [hF E A n Θ hΘ]
    have hx' : Θ x ≠ 0 := by simpa using hx
    obtain ⟨k1, hk1⟩ : ∃ k, Θ x k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx' (funext h)
    have hterm : ∀ k : Phi A × Fin n,
        2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ (J x) k * (starRingEnd ℂ) (Θ x k)).re
          = 2 * ((-(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k)) * Complex.normSq (Θ x k)) := by
      intro k
      obtain ⟨hH, hD0, -, -⟩ := hS E A n k.1.1 k.2
      rw [hJ]
      simp only [a]
      rw [pDomSt_term _ _ _ _ hD0 hH]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (by norm_num) (mul_nonneg (hpos k).le (Complex.normSq_nonneg _))
    · exact ⟨k1, Finset.mem_univ _, mul_pos (by norm_num) (mul_pos (hpos k1) (Complex.normSq_pos.mpr hk1))⟩
  · intro b M hM
    apply LinearMap.ext
    intro x
    apply Θ.injective
    funext k
    simp only [LinearMap.comp_apply]
    rw [hJ, pDomSt_theta_mul A Θ hΘ b M hM, pDomSt_theta_mul A Θ hΘ b M hM, hJ]
    ring
  · intro c M hM
    dsimp only
    have htrM : LinearMap.trace ℝ _ M = 2 * (∑ k : Phi A × Fin n, k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' M Θ]
      refine hD _ (fun k : Phi A × Fin n => k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, pDomSt_theta_mul A Θ hΘ c M hM, LinearEquiv.apply_symm_apply]
    have htrJM : LinearMap.trace ℝ _ (J ∘ₗ M) = 2 * (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' (J ∘ₗ M) Θ]
      refine hD _ (fun k : Phi A × Fin n => a k * k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ, pDomSt_theta_mul A Θ hΘ c M hM,
        LinearEquiv.apply_symm_apply]
      ring
    have hre : (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re = -∑ k, ε k * (k.1.1 (c : E)).im := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [a, Complex.mul_re]
    rw [hsum (fun τ => (n : ℂ) * τ (c : E))]
    constructor
    · rw [htrM]
      simp [ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.re_sum, Finset.mul_sum]
    · rw [htrJM, hre, pDomSt_sum k0 (fun k => (k.1.1 (c : E)).im)]
      simp [k0, ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.im_sum, Finset.mul_sum]
      ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffGen
noncomputable section

open NumberField nonZeroDivisors

namespace UpperTheory.Gal.W2.Seed

private theorem exists_ideal (E : Type) [Field E] [NumberField E] :
    ∃ (a : 𝓞 E) (J : Ideal (𝓞 E)), a ≠ 0 ∧ J ≠ ⊥ ∧
      ∀ z : E, InCodiff z ↔ ∃ j ∈ J, z = (a : E)⁻¹ * (j : E) := by
  classical
  have h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef
  have hD : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  have hmem : ∀ z : E, InCodiff z ↔ z ∈ D := by
    intro z
    unfold InCodiff
    rw [hDdef, FractionalIdeal.mem_dual h1ne]
    constructor
    · rintro h b hb
      obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨m, hm⟩ := h x
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
    · intro h x
      obtain ⟨m, hm⟩ := h (x : E) ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
  set d : E := algebraMap (𝓞 E) E (D.den : 𝓞 E) with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero _)
  have key := FractionalIdeal.den_mul_self_eq_num' (𝓞 E)⁰ E D
  have key2 : D = FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← key, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd0,
      FractionalIdeal.spanSingleton_one, one_mul]
  refine ⟨(D.den : 𝓞 E), D.num, nonZeroDivisors.coe_ne_zero _, ?_, ?_⟩
  · intro h
    apply hD
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  · intro z
    rw [hmem]
    constructor
    · intro hz
      have h1 : d * z ∈ (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← key]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hz
      obtain ⟨j, hj, hjeq⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
      refine ⟨j, hj, ?_⟩
      have h2 : (j : E) = d * z := hjeq
      have h3 : ((D.den : 𝓞 E) : E) = d := rfl
      rw [h3, h2, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    · rintro ⟨j, hj, hz⟩
      have h4 : d⁻¹ * (j : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) :=
        FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
          ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩)
      rw [← key2] at h4
      rw [hz]
      exact h4

theorem pCodiffGen : CodiffGen := by
  unfold CodiffGen
  intro E _ _ M hM
  classical
  obtain ⟨a, J, ha, hJ, hcod⟩ := exists_ideal E
  have hM0 : ((M : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hI0 : J * Ideal.span {(M : 𝓞 E)} ≠ 0 := by
    refine mul_ne_zero (show J ≠ 0 from hJ) ?_
    intro h
    exact hM0 (Ideal.span_singleton_eq_bot.1 h)
  have hle : J * Ideal.span {(M : 𝓞 E)} ≤ J := Ideal.mul_le.2 fun r hr s _ => J.mul_mem_right s hr
  obtain ⟨j, hj⟩ := IsDedekindDomain.exists_sup_span_eq hle hI0
  have hjJ : j ∈ J := by
    rw [← hj]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self j)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {j} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hjJ)
  have hKM : K ⊔ Ideal.span {(M : 𝓞 E)} = ⊤ := by
    have h1 : J * (Ideal.span {(M : 𝓞 E)} ⊔ K) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hK, hj, Ideal.mul_top]
    rw [sup_comm]
    exact mul_left_cancel₀ (show J ≠ 0 from hJ) h1
  set e := Ideal.absNorm K with hedef
  have heK : (e : 𝓞 E) ∈ K := Ideal.absNorm_mem K
  refine ⟨(a : E)⁻¹ * (j : E), (hcod _).2 ⟨j, hjJ, rfl⟩, e, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun q hq hqe hqM => ?_
    have hMq : (M : 𝓞 E) ∈ Ideal.span {(q : 𝓞 E)} :=
      Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast hqM)
    have hKq : K ⊔ Ideal.span {(q : 𝓞 E)} = ⊤ := by
      rw [eq_top_iff, ← hKM]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hMq) K
    have h1 : (1 : 𝓞 E) ∈ K ⊔ Ideal.span {(q : 𝓞 E)} := by rw [hKq]; trivial
    obtain ⟨k, hk, m, hm, hkm⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hK0 : K = ⊥
    · subst hK0
      have hk0 : k = 0 := (Submodule.mem_bot _).1 hk
      rw [hk0, zero_add] at hkm
      have hunit : IsUnit (q : 𝓞 E) := isUnit_iff_exists_inv.2 ⟨t, by rw [mul_comm]; exact hkm⟩
      have htop : Ideal.span {(q : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.2 hunit
      have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) q
      rw [htop, Ideal.absNorm_top] at hn
      have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
      rcases (Nat.pow_eq_one.1 hn.symm) with h | h
      · exact hq.ne_one h
      · omega
    · haveI : Finite (𝓞 E ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK0
      haveI : Fact q.Prime := ⟨hq⟩
      have hcard : q ∣ Nat.card (𝓞 E ⧸ K) := by
        rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
        exact hqe
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hcard
      have hqx : (q : 𝓞 E ⧸ K) * x = 0 := by
        rw [← nsmul_eq_mul, ← hx]
        exact addOrderOf_nsmul_eq_zero x
      have hu : (q : 𝓞 E ⧸ K) * Ideal.Quotient.mk K t = 1 := by
        have := congrArg (Ideal.Quotient.mk K) hkm
        rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hk, zero_add, map_mul, map_one, map_natCast] at this
        rw [mul_comm]
        exact this
      have hx0 : x = 0 := by
        linear_combination (-x) * hu + (Ideal.Quotient.mk K t) * hqx
      rw [hx0, addOrderOf_zero] at hx
      exact hq.one_lt.ne hx
  · intro z hz
    obtain ⟨j', hj', rfl⟩ := (hcod z).1 hz
    have hmem : j' * (e : 𝓞 E) ∈ Ideal.span {j} := by
      rw [hK]
      exact Ideal.mul_mem_mul hj' heK
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_⟩
    have hcast : ((x : E) * (j : E)) = (j' : E) * (e : E) := by
      have := congrArg (fun w : 𝓞 E => (w : E)) hx
      simpa using this
    linear_combination (-(a : E)⁻¹) * hcast

end UpperTheory.Gal.W2.Seed
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPosGen
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPosGen :
    CodiffUnit → PosGen := by
  intro hCU E _ _ _ M hM t htc hg
  obtain ⟨hin, e, he, hz⟩ := id hg

  have h1 : InCodiff (1 : E) := by
    intro x
    have hx : IsIntegral ℤ (Algebra.trace ℚ E (x : E)) := Algebra.isIntegral_trace x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨m, by rw [one_mul, ← hm]; simp⟩

  obtain ⟨N, hN⟩ := exists_nat_gt (∑ τ : E →+* ℂ, |(τ t).re|)
  have hbound : ∀ τ : E →+* ℂ, |(τ t).re| < N := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) hN
  have hin' : InCodiff (t + (M : E) * (N : E)) := by
    intro x
    obtain ⟨a, ha⟩ := hin x
    obtain ⟨b, hb⟩ := h1 x
    refine ⟨a + M * N * b, ?_⟩
    have hs : (t + (M : E) * (N : E)) * (x : E) = t * x + ((M : ℚ) * (N : ℚ)) • (1 * (x : E)) := by
      rw [Algebra.smul_def]; simp; ring
    rw [hs, map_add (f := _), map_smul, ha, hb]
    simp
  obtain ⟨x, hx⟩ := hz 1 h1
  have hgen : GenCodiff M (t + (M : E) * (N : E)) := by
    refine hCU E M hM t _ hg hin' ?_
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro h
      have hc : ((e.gcdA M : ℤ) : 𝓞 E) * (e : 𝓞 E) + ((e.gcdB M : ℤ) : 𝓞 E) * (M : 𝓞 E) = 1 := by
        have := Nat.gcd_eq_gcd_ab e M
        rw [he.gcd_eq_one] at this
        have h2 : ((e : ℤ) * e.gcdA M + (M : ℤ) * e.gcdB M) = 1 := by
          rw [← this]; simp
        have h3 := congrArg (Int.cast : ℤ → 𝓞 E) h2
        push_cast at h3
        rw [← h3]; ring
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, ← hc]
      exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hMP)
    refine ⟨(e : 𝓞 E), (e : 𝓞 E) + (M : 𝓞 E) * ((N : 𝓞 E) * x), heP, ?_, ?_⟩
    · intro h
      exact heP ((P.add_mem_iff_left (P.mul_mem_right _ hMP)).mp h)
    · have hx' : (e : E) = t * x := by simpa using hx
      push_cast
      linear_combination ((M : E) * (N : E)) * hx'
  refine ⟨t + (M : E) * (N : E), ?_, hgen, ?_⟩
  · simp [htc]
  · intro τ
    have hb := abs_lt.mp (hbound τ)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hre : (τ (t + (M : E) * (N : E))).re = (τ t).re + (M : ℝ) * (N : ℝ) := by
      simp
    rw [hre]
    nlinarith [hb.1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHdSign
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pHdSign :
    HdSign := by
  intro E _ _ _ A n τ i
  have hcim : ∀ σ : E →+* ℂ, (σ (A.c : E)).im = 0 := by
    intro σ
    have h1 : σ ((A.bar A.c : 𝓞 E) : E) = (starRingEnd ℂ) (σ (A.c : E)) := by
      rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
    rw [A.c_real] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hre : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → (τ (A.c : E)).re < 0 := by
    intro h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · rw [h']
      exact A.c_neg
    · have h2 := A.c_neg
      rw [← h', NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
      simpa using h2
  have hδ : (τ A.δ).re = 0 := by
    have h1 : τ ((IsCMField.complexConj E) A.δ) = (starRingEnd ℂ) (τ A.δ) :=
      IsCMField.complexEmbedding_complexConj E τ A.δ
    rw [A.δ_im, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hc := hcim τ
  refine ⟨?_, hδ, ?_, ?_⟩
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [Complex.mul_im, hc]
  · rintro ⟨h, hi0⟩
    have hr := hre h
    simp only [Arith.hd, Arith.dg, if_pos hi0]
    simp
    linarith
  · intro hn
    by_cases hp : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀
    · have hi : (i : ℕ) ≠ 0 := fun hi0 => hn ⟨hp, hi0⟩
      have hr := hre hp
      simp only [Arith.hd, Arith.dg, if_neg hi]
      simp [Complex.mul_re, hc]
      nlinarith
    · have hr : 0 < (τ (A.c : E)).re := A.c_pos τ hp
      simp only [Arith.hd, Arith.dg]
      split_ifs
      · simp
        linarith
      · simp [Complex.mul_re, hc]
        nlinarith
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKqEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pKqEx :
    TraceType → KqEx := by
  intro _ E _ _ _ A
  obtain ⟨w, hw⟩ : ∃ w : E, w = (A.ω : E) := ⟨_, rfl⟩
  have h1 : w + IsCMField.complexConj E w = (A.tr : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
    simpa [A.bar_eq, hw] using h
  have h2 : w * IsCMField.complexConj E w = (A.nm : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq
    simpa [A.bar_eq, hw] using h
  have hq : w ^ 2 - (A.tr : E) * w + (A.nm : E) = 0 := by
    linear_combination w * h1 - h2
  have him : ∀ τ : E →+* ℂ, (τ w).im ≠ 0 := by
    intro τ h0
    have hz : (τ w) ^ 2 - (A.tr : ℂ) * τ w + (A.nm : ℂ) = 0 := by
      have h := congrArg τ hq
      simpa using h
    have hr : τ w = (((τ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    obtain ⟨r, hr'⟩ : ∃ r : ℝ, τ w = (r : ℂ) := ⟨_, hr⟩
    rw [hr'] at hz
    have hz' : r ^ 2 - (A.tr : ℝ) * r + (A.nm : ℝ) = 0 := by exact_mod_cast hz
    have hd : ((A.tr : ℝ)) ^ 2 - 4 * (A.nm : ℝ) < 0 := by exact_mod_cast A.disc_neg
    nlinarith [sq_nonneg (2 * r - (A.tr : ℝ))]
  have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
  have hdeg : (minpoly ℚ w).natDegree = 2 := by
    have hpd : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    have hp0 : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) ≠ 0 := by
      intro h
      rw [h] at hpd
      simp at hpd
    have hroot : Polynomial.aeval w (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) = 0 := by
      simpa using hq
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ w hroot) hp0
    have hpos := minpoly.natDegree_pos hint
    have hne : (minpoly ℚ w).natDegree ≠ 1 := by
      intro h
      obtain ⟨q, hq'⟩ := minpoly.natDegree_eq_one_iff.1 h
      apply him A.τ₀
      rw [← hq']
      simp
    omega
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {w}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have hmem : w ∈ IntermediateField.adjoin ℚ {w} := IntermediateField.mem_adjoin_simple_self ℚ w
  refine ⟨(IntermediateField.adjoin ℚ {w}).toSubfield, hw ▸ hmem, ⟨?_, fun τ => ⟨w, hmem, him τ⟩⟩, ?_⟩
  · exact hfr
  · intro x hx
    rw [← hw]
    let pb := IntermediateField.adjoin.powerBasis hint
    obtain ⟨f, hf, hfx⟩ := pb.exists_eq_aeval ⟨x, hx⟩
    have hdim : pb.dim = 2 := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have hf1 : f.natDegree ≤ 1 := by omega
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf1] at hfx
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have h := congrArg (fun z : IntermediateField.adjoin ℚ {w} => (z : E)) hfx
    simp [pb] at h
    rw [h]
    simp [add_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma hensel_root (p : ℕ) [Fact p.Prime] (tr nm r : ℤ) (hd : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (p : ℤ) ∣ r ^ 2 - tr * r + nm) :
    ∃ ρ : ℤ_[p], ρ ^ 2 - (tr : ℤ_[p]) * ρ + (nm : ℤ_[p]) = 0 := by
  have hF1 : ¬ (p : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hd
    have h2 : (p : ℤ) ∣ (2 * r - tr) ^ 2 := dvd_pow h two_ne_zero
    have h3 : (p : ℤ) ∣ 4 * (r ^ 2 - tr * r + nm) := dvd_mul_of_dvd_right hr 4
    have h4 := dvd_sub h2 h3
    have : (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [this] at h4
  set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C tr * Polynomial.X + Polynomial.C nm with hFdef
  have hval : Polynomial.aeval (r : ℤ_[p]) F = ((r ^ 2 - tr * r + nm : ℤ) : ℤ_[p]) := by
    simp [hFdef]
  have hder : Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F) = ((2 * r - tr : ℤ) : ℤ_[p]) := by
    simp [hFdef]
    left
    exact map_ofNat _ 2
  have hn1 : ‖Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F)‖ = 1 := by
    rw [hder]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    push_neg at hlt
    exact hF1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt)
  have hn0 : ‖Polynomial.aeval (r : ℤ_[p]) F‖ < 1 := by
    rw [hval]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hr
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (r : ℤ_[p])) (by rw [hn1]; simpa using hn0)
  refine ⟨z, ?_⟩
  simpa [hFdef] using hz

theorem UpperTheory.Gal.W2.Seed.pUEx :
    UEx := by
  intro E _ _ _ A p _ hsplit Kq hω hspan τ
  unfold Arith.SplitK at hsplit
  obtain ⟨hd, r, hr⟩ := hsplit
  obtain ⟨ρ, hρ⟩ := hensel_root p A.tr A.nm r hd hr
  set ι := algebraMap ℚ_[p] (PadicAlgCl p) with hι
  have hinj : Function.Injective ι := ι.injective
  set w := τ ((A.ω : 𝓞 E) : E) with hwdef
  have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]
    ring
  have h1 : ((A.ω : E)) ^ 2 - (A.tr : E) * (A.ω : E) + (A.nm : E) = 0 := by
    have := congrArg (fun x : 𝓞 E => (x : E)) h0
    simpa using this
  have hw : w ^ 2 - (A.tr : PadicAlgCl p) * w + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg τ h1
    simpa [hwdef] using this
  have hc : ι (ρ : ℚ_[p]) ^ 2 - (A.tr : PadicAlgCl p) * ι (ρ : ℚ_[p]) + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg (fun t : ℤ_[p] => ι (t : ℚ_[p])) hρ
    simpa using this
  have hprod : (w - ι (ρ : ℚ_[p])) * (w - ((A.tr : PadicAlgCl p) - ι (ρ : ℚ_[p]))) = 0 := by
    linear_combination hw - hc
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℤ_[p], w = ι (ρ₀ : ℚ_[p]) := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact ⟨ρ, sub_eq_zero.1 h⟩
    · refine ⟨(A.tr : ℤ_[p]) - ρ, ?_⟩
      rw [sub_eq_zero.1 h]
      simp
  have hex : ∀ x : Kq, ∃ q : ℚ_[p], ι q = τ (x : E) := by
    intro x
    obtain ⟨a, b, hab⟩ := hspan x x.2
    refine ⟨(a : ℚ_[p]) + (b : ℚ_[p]) * (ρ₀ : ℚ_[p]), ?_⟩
    rw [hab]
    simp [← hρ₀, hwdef]
  choose f hf using hex
  let u : Kq →+* ℚ_[p] :=
    { toFun := f
      map_one' := hinj (by rw [hf]; simp)
      map_mul' := fun x y => hinj (by rw [hf, map_mul, hf, hf]; simp)
      map_zero' := hinj (by rw [hf]; simp)
      map_add' := fun x y => hinj (by rw [hf, map_add (f := _), hf, hf]; simp) }
  refine ⟨u, ρ₀, ?_, ?_⟩
  · unfold LiesOver
    intro x
    exact (hf x).symm
  · apply hinj
    show ι (f ⟨_, hω⟩) = _
    rw [hf, ← hρ₀]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma traceCM_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private lemma conj_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    IsCMField.complexConj E (IsCMField.complexConj E z) = z :=
  IsCMField.complexConj_apply_apply E z

private lemma inCodiff_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) {y : E} (hy : InCodiff y) :
    InCodiff (IsCMField.complexConj E y) := by
  intro x
  obtain ⟨m, hm⟩ := hy (bar.symm x)
  refine ⟨m, ?_⟩
  have h : IsCMField.complexConj E y * (x : E) =
      IsCMField.complexConj E (y * ((bar.symm x : 𝓞 E) : E)) := by
    rw [map_mul, ← hbar, RingEquiv.apply_symm_apply]
  rw [h, traceCM_conj, hm]

private lemma inCodiff_mul {E : Type} [Field E] [NumberField E] {y : E} (hy : InCodiff y) (a : 𝓞 E) :
    InCodiff (y * (a : E)) := by
  intro x
  obtain ⟨m, hm⟩ := hy (a * x)
  refine ⟨m, ?_⟩
  rw [mul_assoc, ← hm]
  push_cast
  rfl

private lemma inCodiff_add {E : Type} [Field E] [NumberField E] {y z : E} (hy : InCodiff y) (hz : InCodiff z) :
    InCodiff (y + z) := by
  intro x
  obtain ⟨m, hm⟩ := hy x
  obtain ⟨n, hn⟩ := hz x
  refine ⟨m + n, ?_⟩
  rw [add_mul, map_add (f := _), hm, hn]
  push_cast
  rfl

theorem UpperTheory.Gal.W2.Seed.pRealGen :
    CodiffGen → CodiffUnit → RealGen := by
  intro hgen hunit E _ _ _ bar hbar M hM ε hε
  obtain ⟨y, hy⟩ := hgen E M hM
  by_cases hy0 : y = 0
  · subst hy0
    exact ⟨0, map_zero _, hy⟩
  obtain ⟨hyc, e, he, hegen⟩ := hy
  have hcy : InCodiff (IsCMField.complexConj E y) := inCodiff_conj bar hbar hyc
  obtain ⟨x0, hx0⟩ := hegen _ hcy
  have hx0' : (e : E) * y = IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by
    have h := congrArg (IsCMField.complexConj E) hx0
    rw [map_mul, map_mul, conj_conj', map_natCast] at h
    rw [hbar, h]
  have hnorm : x0 * bar x0 = (e : 𝓞 E) ^ 2 := by
    apply RingOfIntegers.ext
    have h1 : y * ((e : E) ^ 2) = y * ((x0 : E) * ((bar x0 : 𝓞 E) : E)) := by
      calc y * ((e : E) ^ 2) = (e : E) * ((e : E) * y) := by ring
        _ = (e : E) * IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by rw [hx0']; ring
        _ = y * (x0 : E) * ((bar x0 : 𝓞 E) : E) := by rw [hx0]
        _ = _ := by ring
    have h2 := mul_left_cancel₀ hy0 h1
    push_cast
    exact h2.symm
  set t : E := y * (ε : E) + IsCMField.complexConj E (y * (ε : E)) with ht
  refine ⟨t, ?_, ?_⟩
  · rw [ht, map_add (f := _), conj_conj', add_comm]
  · apply hunit E M hM y t ⟨hyc, e, he, hegen⟩
      (inCodiff_add (inCodiff_mul hyc ε) (inCodiff_conj bar hbar (inCodiff_mul hyc ε)))
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr he
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have h3 : ((a * e + b * M : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
      rw [← h3]
      push_cast
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hx0P : x0 ∉ P := by
      intro h
      apply heP
      have h4 : (e : 𝓞 E) ^ 2 ∈ P := hnorm ▸ P.mul_mem_right _ h
      exact hP.isPrime.mem_of_pow_mem 2 h4
    obtain ⟨h1, h2⟩ := hε P hP hMP
    refine ⟨e, e * ε + x0 * bar ε, heP, ?_, ?_⟩
    · intro hu
      rcases hP.isPrime.mem_or_mem h2 with hεP | hεP
      · apply hx0P
        have h5 : x0 = (e * ε + x0 * bar ε) - (e - x0) * ε - x0 * (ε + bar ε - 1) := by ring
        rw [h5]
        exact P.sub_mem (P.sub_mem hu (P.mul_mem_left _ hεP)) (P.mul_mem_left _ h1)
      · apply heP
        have h5 : (e : 𝓞 E) = (e * ε + x0 * bar ε) - e * (ε + bar ε - 1) + (e - x0) * bar ε := by ring
        rw [h5]
        exact P.add_mem (P.sub_mem hu (P.mul_mem_left _ h1)) (P.mul_mem_left _ hεP)
    · rw [ht, map_mul, ← hbar]
      push_cast
      linear_combination ((bar ε : 𝓞 E) : E) * hx0
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrbEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pOrbEx :
    OrbEx := by
  intro E _ _ p _ Kq u τ₁ h₁
  classical
  let S := {τ : E →+* PadicAlgCl p // LiesOver Kq u τ}
  let R : Setoid S :=
    { r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]),
        b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1
      iseqv := ⟨fun a => ⟨1, by ext x; simp⟩,
        fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩,
        fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by rw [hρ, hσ]; ext x; simp⟩⟩ }
  haveI : Finite (E →+* PadicAlgCl p) := inferInstance
  haveI : Finite S := Subtype.finite
  haveI : Finite (Quotient R) := Quotient.finite _
  let s₁ : S := ⟨τ₁, h₁⟩
  let rep : Quotient R → S := fun q => if q = Quotient.mk R s₁ then s₁ else q.out
  have hrep : ∀ q, Quotient.mk R (rep q) = q := by
    intro q
    by_cases hq : q = Quotient.mk R s₁
    · simp only [rep, if_pos hq]
      exact hq.symm
    · simp only [rep, if_neg hq]
      exact Quotient.out_eq q
  let eq := Finite.equivFin (Quotient R)
  refine ⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩
  · simp [rep, s₁]
  · intro i
    exact (rep _).2
  · intro i j σ hij
    apply eq.symm.injective
    rw [← hrep (eq.symm i), ← hrep (eq.symm j)]
    exact Quotient.sound ⟨σ, hij.symm⟩
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))
    exact ⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩
end

namespace UpperTheory.Gal.W2.Seed

theorem BarEx_holds : BarEx := pBarEx
theorem CEx_holds : CEx := pCEx
theorem CodiffGen_holds : CodiffGen := pCodiffGen
theorem DeltaEx_holds : DeltaEx := pDeltaEx
theorem DiagTrace_holds : DiagTrace := pDiagTrace
theorem FormOKSt_holds : FormOKSt := pFormOKSt
theorem FormPerfSt_holds : FormPerfSt := pFormPerfSt
theorem HdSign_holds : HdSign := pHdSign
theorem IdemEx_holds : IdemEx := pIdemEx
theorem LiftEx_holds : LiftEx := pLiftEx
theorem OrbEx_holds : OrbEx := pOrbEx
theorem PerfCof_holds : PerfCof := pPerfCof
theorem PerfOf_holds : PerfOf := pPerfOf
theorem QuadEx_holds : QuadEx := pQuadEx
theorem RepAdj_holds : RepAdj := pRepAdj
theorem RepEx_holds : RepEx := pRepEx
theorem RepLaws_holds : RepLaws := pRepLaws
theorem SetupBasic_holds : SetupBasic := pSetupBasic
theorem TraceType_holds : TraceType := pTraceType
theorem UEx_holds : UEx := pUEx
theorem UnitMod_holds : UnitMod := pUnitMod
theorem CodiffUnit_holds : CodiffUnit := pCodiffUnit UnitMod_holds
theorem FormCoord_holds : FormCoord := pFormCoord TraceType_holds
theorem KqEx_holds : KqEx := pKqEx TraceType_holds
theorem Orient_holds : Orient := pOrient TraceType_holds HdSign_holds
theorem RealIso_holds : RealIso := pRealIso TraceType_holds
theorem SigSt_holds : SigSt := pSigSt HdSign_holds
theorem AtPEx_holds : AtPEx := pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds
theorem DomSt_holds : DomSt := pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds
theorem PosGen_holds : PosGen := pPosGen CodiffUnit_holds
theorem RealGen_holds : RealGen := pRealGen CodiffGen_holds CodiffUnit_holds
theorem SetupEx_holds : SetupEx := pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds

end UpperTheory.Gal.W2.Seed

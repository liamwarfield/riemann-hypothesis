module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PolyChartSmoothFractionLift
namespace GlobalTheory

open MvPolynomial

section PolyChart

variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)

noncomputable def polyChartHom :
    MvPolynomial V R₀ →ₐ[K] FractionRing (MvPolynomial V F₀) :=
  (IsScalarTower.toAlgHom K (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))).comp
    (MvPolynomial.mapAlgHom R₀.val)

theorem polyChartHom_apply (p : MvPolynomial V R₀) :
    polyChartHom V R₀ p = algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (MvPolynomial.map (R₀.val : R₀ →+* F₀) p) := rfl

theorem polyChartHom_injective : Function.Injective (polyChartHom V R₀) := by
  intro p q h
  rw [polyChartHom_apply, polyChartHom_apply] at h
  exact MvPolynomial.map_injective _ Subtype.val_injective
    (IsFractionRing.injective (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) h)

theorem polyChartHom_C (a : R₀) :
    polyChartHom V R₀ (C a) = algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a := by
  rw [polyChartHom_apply, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply F₀ (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))]
  rfl

theorem polyChartHom_X (v : V) :
    polyChartHom V R₀ (X v) =
      algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v) := by
  rw [polyChartHom_apply, MvPolynomial.map_X]

theorem polyChartHom_range :
    (polyChartHom V R₀).range = Algebra.adjoin K
      ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪
        Set.range fun v : V =>
          algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change polyChartHom V R₀ p ∈ _
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [polyChartHom_C]
      exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul, polyChartHom_X]
      exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨v, rfl⟩))
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨C ⟨a, ha⟩, polyChartHom_C V R₀ ⟨a, ha⟩⟩
    · exact ⟨X v, polyChartHom_X V R₀ v⟩

theorem polyChart_clear (h : ∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a)
    (p : MvPolynomial V F₀) :
    ∃ b : R₀, (b : F₀) ≠ 0 ∧ ∃ q : MvPolynomial V R₀,
      p * C (b : F₀) = MvPolynomial.map (R₀.val : R₀ →+* F₀) q := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h x
    refine ⟨⟨b, hb⟩, hb0, C ⟨a, ha⟩, ?_⟩
    rw [MvPolynomial.map_C, ← map_mul]
    exact congrArg C e
  | add p q hp hq =>
    obtain ⟨b, hb, p', e⟩ := hp
    obtain ⟨c, hc, q', f⟩ := hq
    refine ⟨b * c, mul_ne_zero hb hc, p' * C c + q' * C b, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e, ← f]
    change (p + q) * C ((b : F₀) * c) = p * C (b : F₀) * C (c : F₀) + q * C (c : F₀) * C (b : F₀)
    rw [map_mul]
    ring
  | mul_X p v hp =>
    obtain ⟨b, hb, p', e⟩ := hp
    refine ⟨b, hb, p' * X v, ?_⟩
    rw [map_mul, MvPolynomial.map_X, ← e]
    ring

end PolyChart

theorem polyChart_smooth_fraction_lift : ∀ (K F₀ V : Type) [Field K] [Field F₀] [Algebra K F₀] [Finite V] (R₀ : Subalgebra K F₀) (R : Subalgebra K (FractionRing (MvPolynomial V F₀))), R = Algebra.adjoin K ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪ Set.range fun v : V => algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v)) → (Algebra.Smooth K R₀ → Algebra.Smooth K R) ∧ ((∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∀ x : FractionRing (MvPolynomial V F₀), ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) ∧ ∀ (S : Type) [CommRing S] [Algebra K S] (ψ : R₀ →ₐ[K] S) (t : V → S), ∃! ψ' : R →ₐ[K] S, (∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈ R), ψ' ⟨_, h⟩ = ψ a) ∧ ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (MvPolynomial.X v) ∈ R), ψ' ⟨_, h⟩ = t v := by
  intro K F₀ V _ _ _ _ R₀ R hR
  rw [← polyChartHom_range] at hR
  subst hR
  let e : MvPolynomial V R₀ ≃ₐ[K] (polyChartHom V R₀).range :=
    AlgEquiv.ofInjective _ (polyChartHom_injective V R₀)
  have he : ∀ p, ((e p : (polyChartHom V R₀).range) : FractionRing (MvPolynomial V F₀))
      = polyChartHom V R₀ p := fun p => rfl
  have heC : ∀ (a : R₀) (h : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
      (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (C a) :=
    fun a h => Subtype.ext (polyChartHom_C V R₀ a).symm
  have heX : ∀ (v : V) (h : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (X v) ∈ (polyChartHom V R₀).range), (⟨_, h⟩ : (polyChartHom V R₀).range) = e (X v) :=
    fun v h => Subtype.ext (polyChartHom_X V R₀ v).symm
  refine ⟨fun hs => ?_, fun h x => ?_, fun S _ _ ψ t => ?_⟩
  · have : Algebra.Smooth R₀ (MvPolynomial V R₀) := ⟨inferInstance, inferInstance⟩
    have : Algebra.Smooth K (MvPolynomial V R₀) := Algebra.Smooth.comp K R₀ _
    exact Algebra.Smooth.of_equiv e
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial V F₀) x
    obtain ⟨b, hb, p', e1⟩ := polyChart_clear V R₀ h p
    obtain ⟨c, hc, q', e2⟩ := polyChart_clear V R₀ h q
    have hq0 : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have hne : ∀ d : F₀, d ≠ 0 →
        algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (C d) ≠ 0 := by
      intro d hd h0
      rw [IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero] at h0
      exact hd h0
    have h1 : polyChartHom V R₀ (p' * C c) =
        algebraMap (MvPolynomial V F₀) _ (p * C (b : F₀) * C (c : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e1]; rfl
    have h2 : polyChartHom V R₀ (q' * C b) =
        algebraMap (MvPolynomial V F₀) _ (q * C (c : F₀) * C (b : F₀)) := by
      rw [polyChartHom_apply, map_mul, MvPolynomial.map_C, e2]; rfl
    refine ⟨_, ⟨_, h1⟩, _, ⟨_, h2⟩, ?_, ?_⟩
    · rw [map_mul, map_mul]
      exact mul_ne_zero (mul_ne_zero hq0 (hne _ hc)) (hne _ hb)
    · simp only [map_mul]
      field_simp
  · let φ : MvPolynomial V R₀ →ₐ[K] S := MvPolynomial.aevalTower ψ t
    refine ⟨φ.comp e.symm.toAlgHom, ⟨fun a h => ?_, fun v h => ?_⟩, ?_⟩
    · rw [heC]
      simp [φ]
    · rw [heX]
      simp [φ]
    · rintro χ ⟨hC, hX⟩
      have : χ.comp e.toAlgHom = φ := by
        apply MvPolynomial.algHom_ext'
        · ext a
          have hm : algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a ∈
            (polyChartHom V R₀).range := ⟨C a, polyChartHom_C V R₀ a⟩
          have := (congrArg χ (heC a hm)).symm.trans (hC a hm)
          simpa [φ] using this
        · intro v
          have hm : algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
            (X v) ∈ (polyChartHom V R₀).range := ⟨X v, polyChartHom_X V R₀ v⟩
          have := (congrArg χ (heX v hm)).symm.trans (hX v hm)
          simpa [φ] using this
      rw [← this]
      ext x
      simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEigenProjectorRingOfIntegers
open NumberField

namespace GlobalTheory

open NumberField Matrix in
open Polynomial in
private theorem aeval_mulVec_of_eigenvector {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (μ : K) (x : Fin n → R) (hx : M *ᵥ x = algebraMap K R μ • x)
    (p : K[X]) : (aeval M p) *ᵥ x = algebraMap K R (p.eval μ) • x := by
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ x = algebraMap K R (μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hx, smul_smul, pow_succ',
        map_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_eq_sum_range, Matrix.sum_mulVec, eval_eq_sum_range, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.smul_mulVec, hpow, map_mul, mul_smul, algebraMap_smul]


open NumberField Matrix in
open Polynomial in
theorem _root_.GlobalTheory.exists_eigen_projector_ringOfIntegers : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K)), Function.Injective emb → ∀ τ : E →+* ℂ, ∃ (m : ℕ) (a : Fin m → 𝓞 E) (κ : Fin m → K), ∀ (R : Type) [CommRing R] [Algebra K R] (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R), (∀ b : 𝓞 E, ρ b * (∑ k, algebraMap K R (κ k) • ρ (a k)) = algebraMap K R (emb τ (b : E)) • ∑ k, algebraMap K R (κ k) • ρ (a k)) ∧ ∀ x : Fin n → R, (∀ b : 𝓞 E, (ρ b).mulVec x = algebraMap K R (emb τ (b : E)) • x) → (∑ k, algebraMap K R (κ k) • ρ (a k)).mulVec x = x := by
  intro E K _ _ _ emb hemb τ
  classical
  haveI : CharZero K := ⟨fun a b h => by
    have : (emb τ) (a : E) = (emb τ) (b : E) := by simpa using h
    exact Nat.cast_injective ((emb τ).injective this)⟩
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic α0)).exists_integral_multiple
  let θ : 𝓞 E := ⟨y • α0, hyint⟩
  have hθ : (θ : E) = y • α0 := rfl
  have hadj : Algebra.adjoin ℚ {α0} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α0), hα0, IntermediateField.top_toSubalgebra]

  have hsep : ∀ σ σ' : E →+* K, σ θ = σ' θ → σ = σ' := by
    intro σ σ' h
    rw [hθ, map_zsmul, map_zsmul] at h
    have h' : σ α0 = σ' α0 := smul_right_injective K (by exact_mod_cast hy0) h
    have := AlgHom.ext_of_adjoin_eq_top (φ₁ := σ.toRatAlgHom) (φ₂ := σ'.toRatAlgHom) hadj
      (by rintro _ rfl; exact h')
    ext z
    exact congrArg (fun φ : E →ₐ[ℚ] K => φ z) this
  have hpoly : ∀ b : 𝓞 E, ∃ D : ℤ, D ≠ 0 ∧ ∃ h : ℤ[X], (D : 𝓞 E) * b = aeval θ h := by
    intro b
    have hb : (b : E) ∈ Algebra.adjoin ℚ {α0} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨p, hp⟩ := hb
    obtain ⟨c, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (p.comp (C ((y : ℚ)⁻¹) * X))
    refine ⟨c, nonZeroDivisors.ne_zero hc.1, IsLocalization.integerNormalization (nonZeroDivisors ℤ)
      (p.comp (C ((y : ℚ)⁻¹) * X)), ?_⟩
    have hy' : (y : E) ≠ 0 := by exact_mod_cast hy0
    have hθα : aeval (θ : E) (C ((y : ℚ)⁻¹) * X) = α0 := by
      rw [hθ, zsmul_eq_mul]
      simp only [map_mul, aeval_C, aeval_X, map_inv₀, map_intCast]
      field_simp
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← aeval_algebraMap_apply]
    have hθc : algebraMap (𝓞 E) E θ = (θ : E) := rfl
    rw [hθc, ← aeval_map_algebraMap ℚ, hc.2, map_zsmul, aeval_comp, hθα]
    have hp' : aeval α0 p = (b : E) := hp
    rw [hp', zsmul_eq_mul, map_mul, map_intCast]
  have hθint : IsIntegral ℤ (θ : E) := hyint
  have hfmon : (minpoly ℤ (θ : E)).Monic := minpoly.monic hθint
  have hθc : algebraMap (𝓞 E) E θ = (θ : E) := rfl
  have hf0 : aeval θ (minpoly ℤ (θ : E)) = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← aeval_algebraMap_apply, map_zero, hθc]
    exact minpoly.aeval ℤ (θ : E)
  let σ : (E →+* ℂ) → K := fun τ' => emb τ' (θ : E)
  have hσinj : Function.Injective σ := fun τ1 τ2 h => hemb (hsep _ _ h)
  let P : K[X] := ∏ τ' : E →+* ℂ, (X - C (σ τ'))
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hPdeg : P.natDegree = Fintype.card (E →+* ℂ) := by
    simp only [P]
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  have hfK : (minpoly ℤ (θ : E)).map (algebraMap ℤ K) = P := by
    refine eq_of_monic_of_dvd_of_natDegree_le hPmon (hfmon.map _) ?_ ?_
    · apply Finset.prod_dvd_of_coprime
      · exact (pairwise_coprime_X_sub_C hσinj).set_pairwise _
      · intro τ' _
        rw [dvd_iff_isRoot, IsRoot, eval_map_algebraMap,
          show σ τ' = (emb τ').toIntAlgHom (θ : E) from rfl, aeval_algHom_apply, minpoly.aeval,
          map_zero]
    · rw [hPdeg, hfmon.natDegree_map, NumberField.Embeddings.card E ℂ,
        ← hfmon.natDegree_map (algebraMap ℤ ℚ),
        ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint]
      exact minpoly.natDegree_le _
  have hPρ : ∀ (R : Type) [CommRing R] [Algebra K R] (n : ℕ)
      (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R), aeval (ρ θ) P = 0 := by
    intro R _ _ n ρ
    rw [← hfK, aeval_map_algebraMap, show ρ θ = ρ.toIntAlgHom θ from rfl, aeval_algHom_apply, hf0,
      map_zero]
  let c : K := (∏ τ' ∈ Finset.univ.erase τ, (σ τ - σ τ'))⁻¹
  let G : K[X] := C c * ∏ τ' ∈ Finset.univ.erase τ, (X - C (σ τ'))
  have hprod_ne : ∏ τ' ∈ Finset.univ.erase τ, (σ τ - σ τ') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ' h => sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h) (hσinj e).symm
  have hGev : G.eval (σ τ) = 1 := by
    simp only [G, c, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact inv_mul_cancel₀ hprod_ne
  have hXG : (X - C (σ τ)) * G = C c * P := by
    simp only [G, P]
    rw [← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (σ τ')) (Finset.mem_univ τ)]
    ring
  clear_value G c P
  refine ⟨G.natDegree + 1, fun k => θ ^ (k : ℕ), fun k => G.coeff k, ?_⟩
  intro R _ _ n ρ
  have hsum : ∑ k : Fin (G.natDegree + 1), algebraMap K R (G.coeff k) • ρ (θ ^ (k : ℕ)) =
      aeval (ρ θ) G := by
    rw [aeval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, algebraMap_smul]
  rw [hsum]
  have hsmul : ∀ (k : K) (M : Matrix (Fin n) (Fin n) R),
      algebraMap K (Matrix (Fin n) (Fin n) R) k * M = algebraMap K R k • M := by
    intro k M
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, algebraMap_smul]
  refine ⟨fun b => ?_, fun x hx => ?_⟩
  · obtain ⟨D, hD, h, hh⟩ := hpoly b
    set hK := h.map (algebraMap ℤ K) with hKdef
    set r := hK.eval (σ τ) with hrdef
    have hr : r = (D : K) * emb τ (b : E) := by
      rw [hrdef, hKdef, eval_map_algebraMap,
        show σ τ = ((emb τ).comp (algebraMap (𝓞 E) E)).toIntAlgHom θ from rfl, aeval_algHom_apply,
        ← hh]
      simp
    have hq := (mul_divByMonic_eq_iff_isRoot (p := hK - C r) (a := σ τ)).2
      (by rw [IsRoot, eval_sub, eval_C, hrdef, sub_self])
    have hkey : hK * G = C r * G + C c * ((hK - C r) /ₘ (X - C (σ τ))) * P := by
      calc hK * G = C r * G + ((X - C (σ τ)) * ((hK - C r) /ₘ (X - C (σ τ)))) * G := by
            rw [hq]; ring
        _ = C r * G + ((hK - C r) /ₘ (X - C (σ τ))) * ((X - C (σ τ)) * G) := by ring
        _ = _ := by rw [hXG]; ring
    have hev := congrArg (aeval (ρ θ)) hkey
    rw [map_add (f := _), map_mul, map_mul, map_mul, hPρ R n ρ, mul_zero, add_zero, aeval_C] at hev
    have hρh : aeval (ρ θ) hK = algebraMap K _ (D : K) * ρ b := by
      rw [hKdef, aeval_map_algebraMap, show ρ θ = ρ.toIntAlgHom θ from rfl, aeval_algHom_apply,
        ← hh]
      simp
    rw [hρh, hr, map_mul, mul_assoc, mul_assoc] at hev
    have hu : IsUnit (algebraMap K (Matrix (Fin n) (Fin n) R) (D : K)) :=
      (IsUnit.mk0 _ (by exact_mod_cast hD)).map _
    rw [hu.mul_left_cancel hev, hsmul]
  · rw [aeval_mulVec_of_eigenvector (ρ θ) (σ τ) x (hx θ) G, hGev, map_one, one_smul]

end GlobalTheory
end

module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsUnitFormSelfOfNotMem
open IsLocalRing

namespace GlobalTheory.QuadraticEtale

section Galois

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)

theorem isIntegral_of_involution (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) : Algebra.IsIntegral R S := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, ht⟩ := hfix (x + σ x) (by rw [map_add (f := _), hσ, add_comm])
  obtain ⟨n, hn⟩ := hfix (x * σ x) (by rw [map_mul, hσ, mul_comm])
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, ht, hn]
    ring

variable [IsLocalRing R]

theorem algebraMap_mem_of_isMaximal [Algebra.IsIntegral R S] (n : Ideal S) [n.IsMaximal]
    {r : R} (hr : r ∈ maximalIdeal R) : algebraMap R S r ∈ n := by
  have h := eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) n)
  rw [← h] at hr
  exact hr

theorem isUnit_or_mem_of_fixed (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range)
    {x : S} (hx : σ x = x) :
    IsUnit x ∨ x ∈ (maximalIdeal R).map (algebraMap R S) := by
  obtain ⟨r, rfl⟩ := hfix x hx
  by_cases hr : IsUnit r
  · exact Or.inl (hr.map _)
  · exact Or.inr (Ideal.mem_map_of_mem _ hr)

theorem exists_isUnit_add_mul (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) (hgal : ∃ ω, IsUnit (ω - σ ω))
    {u : S} (hu : u * σ u = 1) : ∃ a, IsUnit (a + u * σ a) := by
  haveI := isIntegral_of_involution σ hσ hfix
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ⟨0, isUnit_of_subsingleton _⟩
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  obtain ⟨ω, hω⟩ := hgal
  by_contra hcon
  push Not at hcon
  have key : ∀ a, a + u * σ a ∈ n := by
    intro a
    have hz : σ ((a + u * σ a) * σ (a + u * σ a)) = (a + u * σ a) * σ (a + u * σ a) := by
      rw [map_mul, hσ, mul_comm]
    rcases isUnit_or_mem_of_fixed σ hfix hz with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) (hcon a)
    · have h1 : (a + u * σ a) * σ (a + u * σ a) ∈ n :=
        (Ideal.map_le_iff_le_comap (I := maximalIdeal R)).2
          (fun r hr => algebraMap_mem_of_isMaximal n hr) h
      have h2 : a + u * σ a = u * σ (a + u * σ a) := by
        rw [map_add (f := _), map_mul, hσ]
        linear_combination (-a) * hu
      rcases hn.isPrime.mem_or_mem h1 with h3 | h3
      · exact h3
      · rw [h2]; exact n.mul_mem_left _ h3
  have : ω - σ ω ∈ n := by
    have := n.sub_mem (key ω) (n.mul_mem_left (σ ω) (key 1))
    convert this using 1
    rw [map_one]; ring
  exact hn.ne_top (n.eq_top_of_isUnit_mem this hω)


omit [IsLocalRing R] [Algebra R S] [CommRing R] in
theorem exists_add_eq_one (hσ : ∀ x, σ (σ x) = x) (hgal : ∃ ω, IsUnit (ω - σ ω)) :
    ∃ t, t + σ t = 1 := by
  obtain ⟨ω, hω⟩ := hgal
  obtain ⟨v, hv⟩ := hω.exists_right_inv
  have h2 := congrArg σ hv
  rw [map_mul, map_sub, hσ, map_one] at h2
  refine ⟨ω * v, ?_⟩
  rw [map_mul]
  have : σ v = -v := by linear_combination (-σ v) * hv - v * h2
  rw [this]
  linear_combination hv

variable {M : Type*} [AddCommGroup M] [Module S M]

end Galois

section Quadratic

open TensorProduct Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem exists_basis_one [IsLocalRing R] [Module.Free R S] (hrank : finrank R S = 2) :
    ∃ B : Basis (Fin 2) R S, B 0 = 1 := by
  haveI : Module.Finite R S := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial S := Module.nontrivial_of_finrank_pos (R := R) (by omega)
  have aux : ∀ b : Basis (Fin 2) R S, IsUnit (b.repr 1 0) → ∃ B : Basis (Fin 2) R S, B 0 = 1 := by
    intro b hb
    have h1 : (1 : S) = b.repr 1 0 • b 0 + b.repr 1 1 • b 1 := by
      conv_lhs => rw [← b.sum_repr 1]
      rw [Fin.sum_univ_two]
    obtain ⟨w, hw⟩ := hb.exists_left_inv
    have hli : LinearIndependent R ![(1 : S), b 1] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h0 := congrArg (fun x => b.repr x 0) hst
      have h2 := congrArg (fun x => b.repr x 1) hst
      simp at h0 h2
      have hs : s = 0 := by linear_combination w * h0 - s * hw
      exact ⟨hs, by simpa [hs] using h2⟩
    have hsp : ⊤ ≤ Submodule.span R (Set.range ![(1 : S), b 1]) := by
      rw [← b.span_eq, Submodule.span_le]
      have m1 : (1 : S) ∈ Submodule.span R (Set.range ![(1 : S), b 1]) :=
        Submodule.subset_span ⟨0, rfl⟩
      have m2 : b 1 ∈ Submodule.span R (Set.range ![(1 : S), b 1]) :=
        Submodule.subset_span ⟨1, rfl⟩
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · have : b 0 = w • (1 - b.repr 1 1 • b 1) := by
          conv_rhs => rw [sub_eq_of_eq_add h1, smul_smul, hw, one_smul]
        simp only [Fin.zero_eta, SetLike.mem_coe]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
      · exact m2
    exact ⟨Basis.mk hli hsp, by simp⟩
  let b := Module.finBasisOfFinrankEq R S hrank
  by_cases h0 : IsUnit (b.repr 1 0)
  · exact aux b h0
  by_cases h1 : IsUnit (b.repr 1 1)
  · exact aux (b.reindex (Equiv.swap 0 1)) (by simpa using h1)
  exfalso
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one, ← b.sum_repr 1, Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]
  exact n.add_mem (n.mul_mem_right _ (algebraMap_mem_of_isMaximal n h0))
    (n.mul_mem_right _ (algebraMap_mem_of_isMaximal n h1))

theorem eq_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) (x : S) :
    x = algebraMap R S (B.repr x 0) + algebraMap R S (B.repr x 1) * B 1 := by
  conv_lhs => rw [← B.sum_repr x]
  rw [Fin.sum_univ_two, hB, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem repr_coord_zero (B : Basis (Fin 2) R S) (hB : B 0 = 1) (r s : R) :
    B.repr (algebraMap R S r + algebraMap R S s * B 1) 0 = r := by
  rw [← mul_one (algebraMap R S r), ← hB, ← Algebra.smul_def, ← Algebra.smul_def]
  simp

theorem repr_coord_one (B : Basis (Fin 2) R S) (hB : B 0 = 1) (r s : R) :
    B.repr (algebraMap R S r + algebraMap R S s * B 1) 1 = s := by
  rw [← mul_one (algebraMap R S r), ← hB, ← Algebra.smul_def, ← Algebra.smul_def]
  simp

theorem coord_inj (B : Basis (Fin 2) R S) (hB : B 0 = 1) {r s r' s' : R}
    (h : algebraMap R S r + algebraMap R S s * B 1 = algebraMap R S r' + algebraMap R S s' * B 1) :
    r = r' ∧ s = s' :=
  ⟨by rw [← repr_coord_zero B hB r s, h, repr_coord_zero B hB],
    by rw [← repr_coord_one B hB r s, h, repr_coord_one B hB]⟩

theorem trace_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) {a b : R}
    (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) (r s : R) :
    Algebra.trace R S (algebraMap R S r + algebraMap R S s * B 1) = 2 * r + s * a := by
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hB, mul_one, repr_coord_zero B hB]
  have : (algebraMap R S r + algebraMap R S s * B 1) * B 1
      = algebraMap R S (s * b) + algebraMap R S (r + s * a) * B 1 := by
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap R S s) * hab
  rw [this, repr_coord_one B hB]
  ring

theorem isUnit_different [Algebra.FormallyUnramified R S] (B : Basis (Fin 2) R S) (hB : B 0 = 1)
    {a b : R} (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) :
    IsUnit (2 * B 1 - algebraMap R S a) := by
  haveI : Module.Finite R S := Module.Finite.of_basis B
  let L : S ⊗[R] S →ₗ[R] S :=
    LinearMap.mul' R S ∘ₗ LinearMap.lTensor S (Algebra.linearMap R S ∘ₗ B.coord 1)
  have hL : ∀ x y, L (x ⊗ₜ y) = x * algebraMap R S (B.repr y 1) := fun x y => by simp [L]
  have h1 : ∀ (s : S) z, L ((s ⊗ₜ 1) * z) = s * L z := by
    intro s z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [Algebra.TensorProduct.tmul_mul_tmul, hL, hL, one_mul, mul_assoc]
    | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  have h2 : ∀ z, Algebra.TensorProduct.lmul' R (S := S) z
      = L ((1 ⊗ₜ B 1) * z) + (B 1 - algebraMap R S a) * L z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, hL, hL, one_mul,
        Algebra.TensorProduct.lmul'_apply_tmul]
      have hy := eq_coord B hB y
      have : B 1 * y = algebraMap R S (B.repr y 1 * b)
          + algebraMap R S (B.repr y 0 + B.repr y 1 * a) * B 1 := by
        simp only [map_add (f := _), map_mul]
        linear_combination (algebraMap R S (B.repr y 1)) * hab + B 1 * hy
      rw [this, repr_coord_one B hB]
      simp only [map_add (f := _), map_mul]
      linear_combination x * hy
    | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; ring
  have h3 := h2 (Algebra.FormallyUnramified.elem R S)
  rw [Algebra.FormallyUnramified.lmul_elem, Algebra.FormallyUnramified.one_tmul_mul_elem, h1] at h3
  exact IsUnit.of_mul_eq_one (L (Algebra.FormallyUnramified.elem R S)) (by linear_combination -h3)

theorem apply_eq_of_ne_one [IsLocalRing R] [Algebra.FormallyUnramified R S]
    (B : Basis (Fin 2) R S) (hB : B 0 = 1)
    {a b : R} (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1)
    (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) : σ (B 1) = algebraMap R S a - B 1 := by
  haveI : Module.Finite R S := Module.Finite.of_basis B
  haveI : Nontrivial S := ⟨⟨B 0, 0, B.ne_zero 0⟩⟩
  have hD : IsUnit (a ^ 2 + 4 * b) := by
    by_contra hD
    obtain ⟨n, hn⟩ := Ideal.exists_maximal S
    have h1 := algebraMap_mem_of_isMaximal n (r := a ^ 2 + 4 * b) hD
    have h2 := (isUnit_different B hB hab).pow 2
    refine hn.ne_top (n.eq_top_of_isUnit_mem h1 ?_)
    convert h2 using 1
    simp only [map_add (f := _), map_mul, map_pow, map_ofNat]
    linear_combination (-4) * hab
  obtain ⟨c, d, hcd⟩ : ∃ c d : R, σ (B 1) = algebraMap R S c + algebraMap R S d * B 1 :=
    ⟨_, _, eq_coord B hB _⟩
  have hd : IsUnit d := by
    obtain ⟨r, s, hrs⟩ : ∃ r s : R, σ.symm (B 1) = algebraMap R S r + algebraMap R S s * B 1 :=
      ⟨_, _, eq_coord B hB _⟩
    have h1 := congrArg σ hrs
    rw [AlgEquiv.apply_symm_apply, map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
      hcd] at h1
    have h2 := coord_inj B hB (r := r + s * c) (s := d * s) (r' := 0) (s' := 1) (by
      simp only [map_add (f := _), map_mul, map_zero, map_one]; linear_combination -h1)
    exact IsUnit.of_mul_eq_one s h2.2
  have h1 := congrArg σ hab
  rw [map_add (f := _), map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcd] at h1
  obtain ⟨e1, e2⟩ := coord_inj B hB (r := c ^ 2 + d ^ 2 * b) (s := d * (2 * c + d * a))
    (r' := b + a * c) (s' := d * a) (by
      simp only [map_add (f := _), map_mul, map_pow, map_ofNat]
      linear_combination h1 - (algebraMap R S d) ^ 2 * hab)
  have e3 : 2 * c + d * a = a := hd.mul_left_cancel e2
  have e4 : (1 - d) * (1 + d) = 0 := by
    apply hD.mul_left_cancel
    linear_combination (-4) * e1 + (2 * c - a - d * a) * e3
  have e5 : c * (c - a) = 0 := by linear_combination e1 + b * e4
  have hne : ¬ (c = 0 ∧ d = 1) := by
    rintro ⟨rfl, rfl⟩
    apply hσ
    ext x
    rw [eq_coord B hB x]
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hcd, AlgEquiv.one_apply]
    simp
  have h2a : IsUnit (2 : R) ∨ IsUnit a := by
    rcases isUnit_or_isUnit_of_isUnit_add hD with h | h
    · exact Or.inr (isUnit_pow_iff two_ne_zero |>.1 h)
    · refine Or.inl (isUnit_of_mul_isUnit_left (y := 2 * b) ?_)
      convert h using 1; ring
  have main : c = a ∧ d = -1 := by
    by_cases hd1 : IsUnit (1 - d)
    · have hd' : d = -1 := by
        have : 1 + d = 0 := hd1.mul_left_cancel (by rw [e4, mul_zero])
        linear_combination this
      subst hd'
      have h2 : IsUnit (2 : R) := by convert hd1 using 1; ring
      exact ⟨h2.mul_left_cancel (by linear_combination e3), rfl⟩
    · rcases h2a with h2 | ha
      · exfalso
        have h3 : IsUnit (1 + d) := by
          have : IsUnit ((1 - d) + (1 + d)) := by convert h2 using 1; ring
          exact (isUnit_or_isUnit_of_isUnit_add this).resolve_left hd1
        have hd' : d = 1 := by
          have : 1 - d = 0 := h3.mul_right_cancel (by rw [e4, zero_mul])
          linear_combination -this
        subst hd'
        exact hne ⟨h2.mul_left_cancel (by linear_combination e3), rfl⟩
      · have : IsUnit (c + (a - c)) := by convert ha using 1; ring
        rcases isUnit_or_isUnit_of_isUnit_add this with hc | hc
        · have hca : c = a := by
            have : c - a = 0 := hc.mul_left_cancel (by rw [e5, mul_zero])
            linear_combination this
          subst hca
          exact ⟨rfl, ha.mul_left_cancel (by linear_combination e3)⟩
        · exfalso
          have hc0 : c = 0 := hc.mul_left_cancel (by linear_combination -e5)
          subst hc0
          exact hne ⟨rfl, ha.mul_left_cancel (by linear_combination e3)⟩
  rw [hcd, main.1, main.2]
  simp only [map_neg, map_one]
  ring

end Quadratic

section Unramified

open Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]

theorem add_apply_eq_trace (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) (x : S) :
    x + σ x = algebraMap R S (Algebra.trace R S x) := by
  obtain ⟨B, hB⟩ := exists_basis_one hrank
  have hab := eq_coord B hB (B 1 * B 1)
  have h := apply_eq_of_ne_one B hB hab σ hσ
  rw [eq_coord B hB x, trace_coord B hB hab]
  simp only [map_add (f := _), map_mul, AlgEquiv.commutes, h, map_ofNat]
  ring

theorem existsUnique_ne_one (hrank : finrank R S = 2) : ∃! σ : S ≃ₐ[R] S, σ ≠ 1 := by
  haveI : Nontrivial S := Module.nontrivial_of_finrank_pos (R := R) (by omega)
  refine existsUnique_of_exists_of_unique ?_ fun σ τ hσ hτ => ?_
  swap
  · ext x
    linear_combination add_apply_eq_trace hrank σ hσ x - add_apply_eq_trace hrank τ hτ x
  obtain ⟨B, hB⟩ := exists_basis_one hrank
  obtain ⟨a, b, hab⟩ : ∃ a b, B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1 :=
    ⟨_, _, eq_coord B hB _⟩
  let f : S →ₗ[R] S := Algebra.linearMap R S ∘ₗ Algebra.trace R S - LinearMap.id
  have hf : ∀ r s, f (algebraMap R S r + algebraMap R S s * B 1)
      = algebraMap R S (r + s * a) + algebraMap R S (-s) * B 1 := by
    intro r s
    simp only [f, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      Algebra.linearMap_apply, trace_coord B hB hab]
    simp only [map_add (f := _), map_mul, map_neg, map_ofNat]
    ring
  have hc : ∀ x, ∃ r s, x = algebraMap R S r + algebraMap R S s * B 1 :=
    fun x => ⟨_, _, eq_coord B hB _⟩
  have hone : f 1 = 1 := by simpa using hf 1 0
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    obtain ⟨r, s, rfl⟩ := hc x
    obtain ⟨r', s', rfl⟩ := hc y
    have : (algebraMap R S r + algebraMap R S s * B 1) * (algebraMap R S r' + algebraMap R S s' * B 1)
        = algebraMap R S (r * r' + s * s' * b)
          + algebraMap R S (r * s' + s * r' + s * s' * a) * B 1 := by
      simp only [map_add (f := _), map_mul]
      linear_combination (algebraMap R S s * algebraMap R S s') * hab
    rw [this, hf, hf, hf]
    simp only [map_add (f := _), map_mul, map_neg]
    linear_combination (-(algebraMap R S s * algebraMap R S s')) * hab
  have hinv : ∀ x, f (f x) = x := by
    intro x
    obtain ⟨r, s, rfl⟩ := hc x
    rw [hf, hf]
    simp only [map_add (f := _), map_mul, map_neg]
    ring
  let g : S →ₐ[R] S := AlgHom.ofLinearMap f hone hmul
  refine ⟨AlgEquiv.ofAlgHom g g (AlgHom.ext hinv) (AlgHom.ext hinv), fun h => ?_⟩
  have h1 : f (B 1) = B 1 := congrArg (fun σ : S ≃ₐ[R] S => σ (B 1)) h
  have h2 := hf 0 1
  simp only [map_zero, map_one, zero_add, one_mul, map_neg, h1] at h2
  have h3 := isUnit_different B hB hab
  rw [show 2 * B 1 - algebraMap R S a = 0 by linear_combination h2] at h3
  exact not_isUnit_zero h3

section Star

variable [StarRing S]

end Star

end Unramified

end GlobalTheory.QuadraticEtale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BinaryFormUniversal
universe u_1

namespace GlobalTheory.BinaryFormUniversal

open Polynomial

theorem binary_form_universal {k : Type u_1} [Field k] [Finite k] {a n : k}
    (hD : a ^ (2 : ℕ) - (4 : k) * n ≠ (0 : k)) (u : k) :
    ∃ (r : k) (s : k), r ^ (2 : ℕ) + a * r * s + n * s ^ (2 : ℕ) = u := by
  classical
  by_cases h2 : ringChar k = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 u
    exact ⟨r, 0, by rw [hr]; ring⟩
  · letI := Fintype.ofFinite k
    have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
    have hD' : -(a ^ 2 - 4 * n) ≠ 0 := neg_ne_zero.mpr hD
    have hf : degree (X ^ 2 : k[X]) = 2 := by simp
    have hg : degree (C (-(a ^ 2 - 4 * n)) * X ^ 2 + C 0 * X + C (-(4 * u)) : k[X]) = 2 :=
      degree_quadratic hD'
    obtain ⟨x, s, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
    refine ⟨(x - a * s) / 2, s, ?_⟩
    field_simp
    linear_combination h

end GlobalTheory.BinaryFormUniversal
end

open Matrix IsLocalRing

namespace GlobalTheory.UnramifiedHermitian

section Diagonal

variable {R : Type*} [CommRing R] (c : R →+* R) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_shear (G : Matrix ι ι R) (p : ι) (τ : ι → R) (hτ : τ p = 0) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ ∀ x y, (Pᵀ * G * P.map c) x y
      = G x y + τ x * G p y + c (τ y) * G x p + τ x * c (τ y) * G p p := by
  refine ⟨1 + vecMulVec (Pi.single p 1) τ, ?_, fun x y => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := 1 - vecMulVec (Pi.single p 1) τ) ?_
    rw [mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec]
    simp [hτ]
  · simp only [Matrix.mul_apply, transpose_apply, map_apply, Matrix.add_apply, vecMulVec_apply,
      Matrix.one_apply, Pi.single_apply, map_add, map_mul, apply_ite c, map_one, map_zero,
      add_mul, mul_add, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring


omit [DecidableEq ι] in
theorem hermitian_congr (hc : ∀ x, c (c x) = x) {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a)
    (P : Matrix ι ι R) (a b : ι) : c ((Pᵀ * G * P.map c) a b) = (Pᵀ * G * P.map c) b a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hG,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_congr (G P : Matrix ι ι R) :
    (Pᵀ * G * P.map c).det = P.det * c P.det * G.det := by
  rw [det_mul, det_mul, det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  ring


omit [DecidableEq ι] in
theorem congr_mul (G P Q : Matrix ι ι R) :
    (P * Q)ᵀ * G * (P * Q).map c = Qᵀ * (Pᵀ * G * P.map c) * Q.map c := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem exists_congr_symm {G H P : Matrix ι ι R} (hP : IsUnit P.det)
    (h : Pᵀ * G * P.map c = H) : ∃ Q : Matrix ι ι R, IsUnit Q.det ∧ G = Qᵀ * H * Q.map c := by
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det P hP, ?_⟩
  rw [← h, ← congr_mul, Matrix.mul_nonsing_inv P hP]
  simp

theorem mem_of_fixed_of_not_isUnit (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) {x : R} (hx : c x = x) (hu : ¬ IsUnit x)
    (n : Ideal R) [hn : n.IsMaximal] : x ∈ n := by
  by_contra hxn
  obtain ⟨r, y, hy, hry⟩ := hn.exists_inv hxn
  have hfix : c (x * (r + c r - x * (r * c r))) = x * (r + c r - x * (r * c r)) := by
    simp only [map_mul, map_sub, map_add (f := _), hc, hx]; ring
  rcases hloc _ hfix with h | h
  · exact hu (isUnit_of_mul_isUnit_left h)
  · refine hn.ne_top (n.eq_top_of_isUnit_mem ?_ h)
    have hy' : y = 1 - r * x := by linear_combination hry
    have := n.mul_mem_right (c y) hy
    convert this using 1
    rw [hy']
    simp only [map_mul, map_sub, map_one, hx]
    ring

theorem mem_of_forall_trace_mem (hc : ∀ x, c (c x) = x) (hw : ∃ w, w + c w = 1)
    (n : Ideal R) [hn : n.IsMaximal] {g : R} (hg : ∀ t, t * g + c (t * g) ∈ n) : g ∈ n := by
  obtain ⟨w, hw⟩ := hw
  by_contra hgn
  have h1 : g * c g ∈ n := by
    convert hg (w * c g) using 1
    simp only [map_mul, hc]
    linear_combination (-(g * c g)) * hw
  have h2 : c g ∈ n := (hn.isPrime.mem_or_mem h1).resolve_left hgn
  have h3 := n.sub_mem (hg 1) h2
  apply hgn
  simpa using h3

theorem exists_congr_insert (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) (hw : ∃ w, w + c w = 1)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det)
    (s : Finset ι) (hs : ∀ a ∈ s, ∀ b, b ≠ a → G a b = 0) (hne : ∃ a, a ∉ s) :
    ∃ p ∉ s, ∃ P : Matrix ι ι R, IsUnit P.det ∧
      ∀ a ∈ insert p s, ∀ b, b ≠ a → (Pᵀ * G * P.map c) a b = 0 := by

  have clear : ∀ {G : Matrix ι ι R}, (∀ a b, c (G a b) = G b a) →
      (∀ a ∈ s, ∀ b, b ≠ a → G a b = 0) → ∀ p ∉ s, IsUnit (G p p) →
      ∃ P : Matrix ι ι R, IsUnit P.det ∧
        ∀ a ∈ insert p s, ∀ b, b ≠ a → (Pᵀ * G * P.map c) a b = 0 := by
    intro G hG hs p hp hu
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have hv' : c v * G p p = 1 := by
      have := congrArg c hv
      rwa [map_mul, hG, map_one] at this
    obtain ⟨P, hP, h⟩ := exists_shear c G p (fun x => if x = p then 0 else -(v * G x p)) (by simp)
    refine ⟨P, hP, fun a ha b hb => ?_⟩
    rw [h]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · simp only [if_true, if_neg hb, map_neg, map_mul, hG]
      linear_combination (-G a b) * hv'
    · have hap : p ≠ a := fun h => hp (h ▸ ha)
      simp [hs a ha b hb, hs a ha p hap]
  rcases subsingleton_or_nontrivial R with hR | hR
  · obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, 1, by simp, fun _ _ _ _ => Subsingleton.elim _ _⟩
  by_cases hd : ∃ p ∉ s, IsUnit (G p p)
  · obtain ⟨p, hp, hu⟩ := hd
    exact ⟨p, hp, clear hG hs p hp hu⟩
  push Not at hd
  obtain ⟨n, hn⟩ := Ideal.exists_maximal R
  have hdn : ∀ p ∉ s, G p p ∈ n := fun p hp =>
    mem_of_fixed_of_not_isUnit c hc hloc (hG p p) (hd p hp) n
  by_cases hx : ∃ p ∉ s, ∃ q ∉ s, p ≠ q ∧ ∃ t,
      IsUnit (G p p + t * G q p + c t * G p q + t * c t * G q q)
  · obtain ⟨p, hp, q, hq, hpq, t, hu⟩ := hx
    obtain ⟨P, hP, h⟩ := exists_shear c G q (Pi.single p t) (by simp [hpq])
    obtain ⟨Q, hQ, h'⟩ := clear (hermitian_congr c hc hG P) (fun a ha b hb => by
      have hap : p ≠ a := fun h => hp (h ▸ ha)
      have haq : q ≠ a := fun h => hq (h ▸ ha)
      rw [h]
      simp [hs a ha b hb, hs a ha q haq, hap.symm]) p hp (by rw [h]; simpa using hu)
    exact ⟨p, hp, P * Q, by rw [det_mul]; exact hP.mul hQ, by rwa [congr_mul]⟩
  exfalso
  push Not at hx
  obtain ⟨q, hq⟩ := hne
  have hrow : ∀ p, G q p ∈ n := by
    intro p
    by_cases hp : p ∈ s
    · have hqp : q ≠ p := fun h => hq (h ▸ hp)
      rw [← hG, hs p hp q hqp, map_zero]
      exact n.zero_mem
    by_cases hpq : p = q
    · rw [hpq]; exact hdn q hq
    refine mem_of_forall_trace_mem c hc hw n fun t => ?_
    have h1 := mem_of_fixed_of_not_isUnit c hc hloc (by
      simp only [map_add (f := _), map_mul, hc, hG]; ring) (hx p hp q hq hpq t) n
    have h2 := n.sub_mem (n.sub_mem h1 (hdn p hp)) (n.mul_mem_left (t * c t) (hdn q hq))
    convert h2 using 1
    rw [map_mul, hG]
    ring
  refine hn.ne_top (n.eq_top_of_isUnit_mem ?_ hdet)
  rw [Matrix.det_apply']
  refine n.sum_mem fun σ _ => n.mul_mem_left _ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (σ.symm q)), Equiv.apply_symm_apply]
  exact n.mul_mem_right _ (hrow _)

theorem exists_eq_diagonal_of_isUnit_or (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) (hw : ∃ w, w + c w = 1)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ (P : Matrix ι ι R) (d : ι → R), IsUnit P.det ∧ (∀ a, IsUnit (d a)) ∧ (∀ a, c (d a) = d a) ∧
      G = Pᵀ * diagonal d * P.map c := by
  have hdet' : ∀ P : Matrix ι ι R, IsUnit P.det → IsUnit (Pᵀ * G * P.map c).det := fun P hP => by
    rw [det_congr]; exact (hP.mul (hP.map c)).mul hdet
  have key : ∀ k ≤ Fintype.card ι, ∃ s : Finset ι, s.card = k ∧ ∃ P : Matrix ι ι R, IsUnit P.det ∧
      ∀ a ∈ s, ∀ b, b ≠ a → (Pᵀ * G * P.map c) a b = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨∅, rfl, 1, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hsk, P, hP, h⟩ := ih (by omega)
      obtain ⟨p, hp, Q, hQ, h'⟩ := exists_congr_insert c hc hloc hw (hermitian_congr c hc hG P)
        (hdet' P hP) s h (by
          by_contra hcon
          push Not at hcon
          have := Finset.eq_univ_of_forall hcon
          rw [this, Finset.card_univ] at hsk
          omega)
      exact ⟨insert p s, by rw [Finset.card_insert_of_notMem hp, hsk], P * Q,
        by rw [det_mul]; exact hP.mul hQ, by rwa [congr_mul]⟩
  obtain ⟨s, hs, P, hP, h⟩ := key _ le_rfl
  rw [Finset.card_eq_iff_eq_univ] at hs
  subst hs
  have hdiag : Pᵀ * G * P.map c = diagonal fun a => (Pᵀ * G * P.map c) a a := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [diagonal_apply_ne _ hab, h a (Finset.mem_univ a) b (Ne.symm hab)]
  obtain ⟨Q, hQ, hGQ⟩ := exists_congr_symm c hP hdiag
  refine ⟨Q, _, hQ, fun a => ?_, fun a => hermitian_congr c hc hG P a a, hGQ⟩
  have := hdet' P hP
  rw [hdiag, det_diagonal] at this
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => (Pᵀ * G * P.map c) i i)
    (Finset.mem_univ a)) this

theorem exists_eq_transpose_mul_map_of_isUnit_or (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) (hw : ∃ w, w + c w = 1)
    (hnorm : ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ G = Pᵀ * P.map c := by
  obtain ⟨P, d, hP, hd, hcd, h⟩ := exists_eq_diagonal_of_isUnit_or c hc hloc hw hG hdet
  choose x hx using fun a => hnorm (d a) (hcd a) (hd a)
  have hGe : G = (diagonal x * P)ᵀ * (diagonal x * P).map c := by
    have := congr_mul c 1 (diagonal x) P
    rw [Matrix.mul_one, Matrix.mul_one, diagonal_transpose, diagonal_map (map_zero c),
      diagonal_mul_diagonal] at this
    rw [this, h]
    simp only [hx]
  refine ⟨diagonal x * P, ?_, hGe⟩
  rw [hGe, det_mul, det_transpose] at hdet
  exact isUnit_of_mul_isUnit_left hdet

end Diagonal

section Base

variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] (c : R →+* R)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isUnit_or_of_fixed [IsLocalRing R₀]
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (x : R) (hx : c x = x) :
    IsUnit x ∨ IsUnit (1 - x) := by
  obtain ⟨r, rfl⟩ := hfix x hx
  refine (isUnit_or_isUnit_one_sub_self r).imp (fun h => h.map _) fun h => ?_
  simpa using h.map (algebraMap R₀ R)

theorem exists_eq_transpose_mul_map [IsLocalRing R₀] (hc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (hw : ∃ w, w + c w = 1)
    (hnorm : ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ G = Pᵀ * P.map c :=
  exists_eq_transpose_mul_map_of_isUnit_or c hc (isUnit_or_of_fixed c hfix) hw hnorm hG hdet

end Base

section Split

variable {R₀ R : Type*} [CommRing R₀] [CommRing R] (c : R →+* R)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

section Norm

open Polynomial

theorem exists_binary_eq_of_finite {k : Type*} [Field k] [Finite k] {a n : k}
    (hD : a ^ 2 - 4 * n ≠ 0) (u : k) : ∃ r s, r ^ 2 + a * r * s + n * s ^ 2 = u := by
  apply _root_.GlobalTheory.BinaryFormUniversal.binary_form_universal <;> assumption

theorem exists_add_mul_sq_eq {R₀ : Type*} [CommRing R₀] (I : Ideal R₀) [HenselianRing R₀ I]
    (n : R₀) {e : R₀} (he : e ∈ I) : ∃ t, t + n * t ^ 2 = e := by
  obtain ⟨z, hz, hz1⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X - C (n * e))
    (by monicity!) 1 (by simpa using I.mul_mem_left n he) (by
      simp only [derivative_sub, derivative_X_pow, derivative_X, derivative_C]
      norm_num)
  have hu : IsUnit z := by
    simpa using (Ring.mem_jacobson_iff (R := R₀)).1 (HenselianRing.jac hz1) 1
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hz
  refine ⟨e * y, ?_⟩
  linear_combination (-(e * y ^ 2)) * hz + e * (z * y + 1 - y) * hy

variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] [IsLocalRing R₀]
  [HenselianRing R₀ (maximalIdeal R₀)] [Finite (ResidueField R₀)]

theorem exists_norm_eq_of_henselian (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (hgal : ∃ ω, IsUnit (ω - c ω))
    {u : R} (hcu : c u = u) (hu : IsUnit u) : ∃ x, x * c x = u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI := QuadraticEtale.isIntegral_of_involution c hc hfix
  have hunit : ∀ r : R₀, IsUnit (algebraMap R₀ R r) → IsUnit r := by
    intro r hr
    by_contra h
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    exact hm.ne_top (m.eq_top_of_isUnit_mem (QuadraticEtale.algebraMap_mem_of_isMaximal m h) hr)
  obtain ⟨w, hw⟩ := QuadraticEtale.exists_add_eq_one c hc hgal
  obtain ⟨ω, hω⟩ := hgal
  obtain ⟨a, ha⟩ := hfix (ω + c ω) (by rw [map_add (f := _), hc, add_comm])
  obtain ⟨n, hn⟩ := hfix (ω * c ω) (by rw [map_mul, hc, mul_comm])
  obtain ⟨n', hn'⟩ := hfix (w * c w) (by rw [map_mul, hc, mul_comm])
  obtain ⟨u, rfl⟩ := hfix u hcu
  have hu' := hunit u hu
  have hD : IsUnit (a ^ 2 - 4 * n) := by
    refine hunit _ ?_
    convert hω.pow 2 using 1
    simp only [map_sub, map_mul, map_pow, map_ofNat, ha, hn]
    ring
  obtain ⟨r, s, hrs⟩ := exists_binary_eq_of_finite (a := residue R₀ a) (n := residue R₀ n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R₀)).ne_zero)
    (residue R₀ u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R₀ (r ^ 2 + a * r * s + n * s ^ 2) = residue R₀ u := by
    simpa only [map_add (f := _), map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + a * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu'.map _).ne_zero
  obtain ⟨v, hv⟩ := hNu.exists_right_inv
  have he : u * v - 1 ∈ maximalIdeal R₀ := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hv, sub_self]
  obtain ⟨t, ht⟩ := exists_add_mul_sq_eq (maximalIdeal R₀) n' he
  have hfinal : (r ^ 2 + a * r * s + n * s ^ 2) * (1 + (t + n' * t ^ 2)) = u := by
    rw [ht]; linear_combination u * hv
  refine ⟨(algebraMap R₀ R r + algebraMap R₀ R s * ω) * (1 + algebraMap R₀ R t * w), ?_⟩
  rw [← hfinal]
  simp only [map_add (f := _), map_mul, map_pow, map_one, hbase, ha, hn, hn']
  linear_combination (algebraMap R₀ R r + algebraMap R₀ R s * ω)
    * (algebraMap R₀ R r + algebraMap R₀ R s * c ω) * algebraMap R₀ R t * hw

theorem exists_eq_transpose_mul_map_of_henselian (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (hgal : ∃ ω, IsUnit (ω - c ω))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ G = Pᵀ * P.map c :=
  exists_eq_transpose_mul_map (R₀ := R₀) c hc hfix (QuadraticEtale.exists_add_eq_one c hc hgal)
    (fun _ h1 h2 => exists_norm_eq_of_henselian (R₀ := R₀) c hc hbase hfix hgal h1 h2) hG hdet

variable [Module.Free R₀ R] [Algebra.FormallyUnramified R₀ R]

end Norm

end GlobalTheory.UnramifiedHermitian

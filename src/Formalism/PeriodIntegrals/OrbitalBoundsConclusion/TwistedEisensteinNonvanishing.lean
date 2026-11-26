module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.ChangeVariablesDeterminantOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TestFunctionPeriodicity

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfRemaining
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnfoldingMatrixFreeCoordinate
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Vec

variable {E : Type} [Field E]

theorem gh_eN_lt {N s : ℕ} (h : s < N) : eN E N s = Pi.single (⟨s, h⟩ : Fin N) 1 := by
  funext l
  simp [eN, Pi.single_apply, Fin.ext_iff]

theorem gh_eN_ge {N s : ℕ} (h : N ≤ s) : eN E N s = 0 := by
  funext l
  have := l.2
  simp only [eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem gh_decomp {N : ℕ} (v : Fin N → E) : v = ∑ m : Fin N, v m • eN E N m.1 := by
  funext l
  simp [eN, Finset.sum_apply, Fin.val_inj]

theorem gh_apply {M N : ℕ} (f : (Fin M → E) →ₗ[E] (Fin N → E)) (v : Fin M → E) (l : Fin N) :
    f v l = ∑ m : Fin M, v m * f (eN E M m.1) l := by
  conv_lhs => rw [gh_decomp v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Finset.sum_apply, mul_comm]

theorem gh_atN_add {N : ℕ} (v w : Fin N → E) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  unfold atN
  split_ifs <;> simp

theorem gh_chArg_add {n' c' n c : ℕ} (x z : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    chArg (n := n) (c := c) (x + z) = chArg (n := n) (c := c) x + chArg (n := n) (c := c) z := by
  unfold chArg
  simp [LinearMap.add_apply, gh_atN_add, Finset.sum_add_distrib]

theorem unfolding_matrix_free_coordinate {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (p : FC n' c' n c) :
    xx1 y t (eN E (n' + c') p.1.2.1) p.1.1 = t p := by
  have he : eN E (n' + c') p.1.2.1 = Pi.single p.1.2 1 := gh_eN_lt p.1.2.2
  rw [he]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact dif_pos p.2

private theorem xx1_eN_apply {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) {s : ℕ} (hs : s < n' + c') (l : Fin (n + c)) :
    xx1 y t (eN E (n' + c') s) l =
      if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩
      else if hs' : s < n' then (if hl : l.1 < n then LinearMap.toMatrix' y ⟨l.1, hl⟩ ⟨s, hs'⟩ else 0)
      else if l.1 = n + (s - n') then 1 else 0 := by
  rw [gh_eN_lt hs]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

theorem unfolding_matrix_sub {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t t' : FC n' c' n c → E) (s : ℕ) (l : Fin (n + c)) :
    (xx1 y t - xx1 y t') (eN E (n' + c') s) l =
      if hs : s < n' + c' then (if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩ - t' ⟨(l, ⟨s, hs⟩), hf⟩ else 0) else 0 := by
  by_cases hs : s < n' + c'
  · rw [dif_pos hs, LinearMap.sub_apply, Pi.sub_apply, xx1_eN_apply y t hs, xx1_eN_apply y t' hs]
    split_ifs <;> first | rfl | exact sub_self _
  · rw [dite_eq_right hs, gh_eN_ge (not_lt.mp hs)]
    simp

end Vec

section Bd

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

end Bd

theorem character_argument_bounded : ChArgBddP := by
  intro E _ _ P n' c' n c j x hx
  unfold chArg
  rw [Finset.mul_sum]
  apply ia_sum (P := P)
  intro i _
  unfold atN
  split_ifs with h
  · exact hx _ _
  · rw [mul_zero]; exact ia_zero (P := P)

theorem translated_function_support : GSuppP := by
  intro E K _ _ _ P hp a b mu v sq g₀ h Φ j hΦ hg hh x hx s l
  set y := h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap with hy
  have hy0 : Φ y ≠ 0 := by
    intro h0; apply hx; simp only [om]; rw [← hy, h0, mul_zero]
  have hyI := hΦ y hy0
  set w := y (g₀.symm (eN E a s)) with hw
  have e1 : x (eN E a s) l = h w l := by simp [hw, hy]
  have e2 := gh_apply h.toLinearMap w l
  simp only [LinearEquiv.coe_coe] at e2
  rw [e1, e2, Finset.mul_sum]
  apply ia_sum (P := P)
  intro m _
  rw [mul_left_comm]
  refine ia_mul (P := P) ?_ (hh m.1 l)
  have e3 := gh_apply y (g₀.symm (eN E a s)) m
  rw [← hw] at e3
  rw [e3]
  apply ia_sum (P := P)
  intro k _
  exact ia_mul (P := P) (hg s k) (hyI k.1 m)

theorem translated_function_invariance : GPerP := by
  intro E K _ _ _ P hp a b mu v sq g₀ h Φ e hΦ hg hh x δ hδ
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  simp only [om]
  congr 1
  rw [LinearMap.add_comp, LinearMap.comp_add]
  apply hΦ
  intro s l
  have e1 := gh_apply h.symm.toLinearMap (δ (g₀ (eN E a s))) l
  simp only [LinearEquiv.coe_coe] at e1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e1, Finset.sum_div]
  apply ia_sum (P := P)
  intro k _
  rw [gh_apply δ (g₀ (eN E a s)) k, Finset.sum_mul, Finset.sum_div]
  apply ia_sum (P := P)
  intro m _
  have e3 : g₀ (eN E a s) m * δ (eN E a m.1) k * h.symm (eN E b k.1) l / (qOf P : E)
      = ((qOf P : E) ^ e * g₀ (eN E a s) m) * (δ (eN E a m.1) k / (qOf P : E) ^ (e + 1))
        * h.symm (eN E b k.1) l := by
    field_simp
    ring
  rw [e3]
  exact ia_mul (P := P) (ia_mul (P := P) (hg s m) (hδ m.1 k)) (hh k.1 l)

theorem unfolding_integrand_good : HGoodP := by
  intro E K _ _ _ _ P hp n' c' n c D j hjD psi hpsi G hGs hGp y
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  refine ⟨?_, ?_⟩
  · intro t ht l
    have hGne : G (xx1 y t) ≠ 0 := by
      intro h0; apply ht; simp only [h0, zero_mul]
    rw [← unfolding_matrix_free_coordinate y t l]
    exact hGs _ hGne _ _
  · intro t δ hδ
    set X := xx1 y t with hX
    set Dm := xx1 y (t + δ) - X with hDm
    have hsplit : xx1 y (t + δ) = X + Dm := by rw [hDm]; abel
    have hD : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
      intro s l
      rw [hDm, hX, unfolding_matrix_sub]
      split_ifs with hs hf
      · simp only [Pi.add_apply, add_sub_cancel_left]; exact hδ _
      · rw [zero_div]; exact ia_zero (P := P)
      · rw [zero_div]; exact ia_zero (P := P)
    have hDint : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l) := by
      intro s l
      have e : Dm (eN E (n' + c') s) l
          = (qOf P : E) ^ j * (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
        field_simp
      rw [e]; exact ia_mul (P := P) (ia_qpow (P := P) j) (hD s l)
    have hGeq : G (X + Dm) = G X := hGp X Dm hD
    simp only
    rw [hsplit, hGeq]
    by_cases hG : G X = 0
    · rw [hG, zero_mul, zero_mul]
    · have hB : IntAt P (chArg (n := n) (c := c) Dm) := by
        have := character_argument_bounded E P n' c' n c 0 Dm (fun s l => by rw [pow_zero, one_mul]; exact hDint s l)
        rwa [pow_zero, one_mul] at this
      have hA : IntAt P ((qOf P : E) ^ j * chArg (n := n) (c := c) X) :=
        character_argument_bounded E P n' c' n c j X (hGs X hG)
      have hA' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) X) :=
        ia_up (P := P) hjD (by rw [mul_neg]; exact ia_neg (P := P) hA)
      have hB' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) Dm) :=
        ia_mul (P := P) (ia_qpow (P := P) D) (ia_neg (P := P) hB)
      rw [gh_chArg_add, neg_add, hpsi.1 _ _ hA' hB', hpsi.2.1 _ (ia_neg (P := P) hB), mul_one]

end PI.TwistedEisensteinNonvanishing.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.FreeCoordinateAffineInvertible
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section XX

variable {E : Type} [Field E]

theorem xxw_eN_eq {N : ℕ} (s : Fin N) : eN E N s.1 = Pi.single s 1 := by
  funext l
  simp only [eN, Pi.single_apply]
  by_cases h : l = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Fin.ext h')

theorem xxw_mem_Ufl {n c i : ℕ} (v : Fin (n + c) → E) : v ∈ Ufl E n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by
  show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _
  simp only [Set.mem_setOf_eq, not_lt]

theorem xxw_entry {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (s : Fin (n' + c')) (l : Fin (n + c)) :
    xx1 xj t (Pi.single s 1) l =
      if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  simp only [xx1, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

theorem xxw_res {n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : R1cond E n c ρ) (v : Fin n → E) :
    ρ (inX E n c v) = inX E n c (resX ρ v) := by
  have hinX : ∀ u : Fin n → E, inX E n c u ∈ Ufl E n c 0 := by
    intro u
    rw [xxw_mem_Ufl]
    intro l hl
    simp only [inX, LinearMap.pi_apply, dif_neg (show ¬ l.1 < n by omega), LinearMap.zero_apply]
  have hsum : inX E n c v = ∑ p : Fin n, v p • eN E (n + c) p.1 := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, eN, mul_ite, mul_one, mul_zero]
    by_cases hl : l.1 < n
    · simp only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply]
      rw [Finset.sum_eq_single ⟨l.1, hl⟩]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro h
        exact hp (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [if_neg]
      intro h
      have := p.isLt
      omega
  funext l
  set_option synthInstance.maxHeartbeats 100000 in
   by_cases hl : l.1 < n
  · rw [hsum, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply, resX, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_comm]
    rfl
  · have h1 := hρ.1 0 _ (hinX v)
    rw [xxw_mem_Ufl] at h1
    rw [h1 l (by omega)]
    simp only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]

theorem xxw_step {n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : R1cond E n c ρ) (i : ℕ)
    (v : Fin (n + c) → E) (hv : v ∈ Ufl E n c (i + 1)) : ρ v - v ∈ Ufl E n c i := by
  by_cases hi : n + i < n + c
  · have hw : v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i) ∈ Ufl E n c i := by
      rw [xxw_mem_Ufl] at hv ⊢
      intro l hl
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eN]
      by_cases hli : l.1 = n + i
      · have hl' : l = ⟨n + i, hi⟩ := Fin.ext hli
        rw [if_pos hli, hl']
        simp
      · rw [if_neg hli, mul_zero, sub_zero]
        exact hv l (by omega)
    have h1 := hρ.1 i _ hw
    have h2 := hρ.2.2 i
    have e1 : ρ v - v = (ρ (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i)) -
        (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i))) +
        v ⟨n + i, hi⟩ • (ρ (eN E (n + c) (n + i)) - eN E (n + c) (n + i)) := by
      rw [map_sub, map_smul, smul_sub]
      abel
    rw [e1]
    exact (Ufl E n c i).add_mem ((Ufl E n c i).sub_mem h1 hw) ((Ufl E n c i).smul_mem _ h2)
  · rw [xxw_mem_Ufl]
    intro l hl
    have := l.isLt
    omega

private theorem xx1_single_eq_of_not_lt {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : ¬ s.1 < n') :
    xx1 xj t (Pi.single s 1) = xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t (Pi.single s 1) := by
  funext l
  simp only [xxw_entry, dif_neg hs]

private theorem xx1_single_eq_inX_of_lt {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : s.1 < n') :
    xx1 xj t (Pi.single s 1) = inX E n c (xj (Pi.single ⟨s.1, hs⟩ 1)) := by
  funext l
  rw [xxw_entry]
  have hnf : ¬ IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
  rw [dif_neg hnf, dif_pos hs]
  simp only [inX, LinearMap.pi_apply]
  by_cases hl : l.1 < n
  · rw [dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply]
  · rw [dif_neg hl, dif_neg hl, LinearMap.zero_apply]

private theorem xx1_single_apply_eq_eN_of_le {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : ¬ s.1 < n') (hj : s.1 - n' < c) :
    ∀ l : Fin (n + c), n + (s.1 - n') ≤ l.1 →
      xx1 xj t (Pi.single s 1) l = eN E (n + c) (n + (s.1 - n')) l := by
  intro l hl
  rw [xxw_entry]
  have hnf : ¬ IsFree n' n c l.1 s.1 := by
    rintro ⟨-, h | ⟨-, h⟩⟩
    · omega
    · omega
  rw [dif_neg hnf, dif_neg hs]
  rfl

theorem unfolding_affine_space_invariant : XXP := by
  intro E _ n' c' n c ρ hρ xj t
  obtain ⟨h1, -⟩ := hρ
  apply (Pi.basisFun E (Fin (n' + c'))).ext
  intro s
  rw [Pi.basisFun_apply]
  funext l
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [xxw_entry]
  by_cases hf : IsFree n' n c l.1 s.1
  · rw [dif_pos hf]
    have hs : ¬ s.1 < n' := by have := hf.1; omega
    rw [xx1_single_eq_of_not_lt xj t s hs]
    show _ = (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t) (eN E (n' + c') s.1) l
    rw [xxw_eN_eq]
    rfl
  · rw [dif_neg hf]
    by_cases hs : s.1 < n'
    · rw [dif_pos hs, xx1_single_eq_inX_of_lt xj t s hs, xxw_res h1]
      simp only [inX, LinearMap.pi_apply]
      by_cases hl : l.1 < n
      · rw [dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply,
          LinearMap.comp_apply]
      · rw [dif_neg hl, dif_neg hl, LinearMap.zero_apply]
    · rw [dif_neg hs]
      have hj : s.1 - n' < c := by
        by_contra hj
        apply hf
        refine ⟨by omega, ?_⟩
        by_cases hjc : s.1 - n' = c
        · exact Or.inl hjc
        · exact Or.inr ⟨by omega, by have := l.isLt; omega⟩
      by_cases hj0 : s.1 - n' = 0
      · have hcol : xx1 xj t (Pi.single s 1) = eN E (n + c) n := by
          funext l'
          rw [xxw_entry]
          have hnf : ¬ IsFree n' n c l'.1 s.1 := by
            rintro ⟨-, h | ⟨h, -⟩⟩ <;> omega
          rw [dif_neg hnf, dif_neg hs, hj0, add_zero]
          rfl
        rw [hcol, h1.2.1, hj0, add_zero]
        rfl
      · have hl : n + (s.1 - n') ≤ l.1 := by
          by_contra hl
          apply hf
          exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
        have hu : xx1 xj t (Pi.single s 1) - eN E (n + c) (n + (s.1 - n')) ∈ Ufl E n c (s.1 - n') := by
          rw [xxw_mem_Ufl]
          intro l' hl'
          rw [Pi.sub_apply, xx1_single_apply_eq_eN_of_le xj t s hs hj l' hl', sub_self]
        have hA := h1.1 _ _ hu
        have hB := h1.2.2 (s.1 - n')
        have hC := (Ufl E n c (s.1 - n')).add_mem hA hB
        rw [map_sub, xxw_mem_Ufl] at hC
        have h3 := hC l hl
        simp only [Pi.add_apply, Pi.sub_apply] at h3
        have e2 : ρ (xx1 xj t (Pi.single s 1)) l = eN E (n + c) (n + (s.1 - n')) l := by
          linear_combination h3
        rw [e2]
        rfl

theorem xxw_inX_inj {n c : ℕ} {v w : Fin n → E} (h : inX E n c v = inX E n c w) : v = w := by
  funext p
  have h1 := congrFun h (Fin.castAdd c p)
  simpa [inX, LinearMap.pi_apply, Fin.coe_castAdd, p.isLt] using h1

theorem restriction_to_affine_surjective : ResXSurjP := by
  intro E _ n' n c ρ hρ y
  obtain ⟨h1, h2⟩ := hρ
  refine ⟨resX ρ⁻¹ ∘ₗ y, ?_⟩
  have key : ∀ u : Fin n → E, resX ρ (resX ρ⁻¹ u) = u := by
    intro u
    apply xxw_inX_inj (c := c)
    rw [← xxw_res h1, ← xxw_res h2, ← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  exact key (y x)

theorem xxw_diff {n' c' n c : ℕ} (t : FC n' c' n c → E) (s : Fin (n' + c')) :
    xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t (Pi.single s 1) - xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) =
      fun l => if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else 0 := by
  funext l
  simp only [Pi.sub_apply, xxw_entry]
  split_ifs <;> simp

def xxwLin {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : (FC n' c' n c → E) →ₗ[E] (FC n' c' n c → E) where
  toFun t f := ρ (fun l => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) f.1.1
  map_add' t t' := by
    funext f
    have hv : (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then (t + t') ⟨(l, f.1.2), hf⟩ else 0) =
        (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) +
        (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t' ⟨(l, f.1.2), hf⟩ else 0) := by
      funext l
      simp only [Pi.add_apply]
      split_ifs <;> simp
    show ρ _ f.1.1 = ρ _ f.1.1 + ρ _ f.1.1
    rw [hv, map_add (f := _)]
    rfl
  map_smul' a t := by
    funext f
    have hv : (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then (a • t) ⟨(l, f.1.2), hf⟩ else 0) =
        a • (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) := by
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    show ρ _ f.1.1 = a * ρ _ f.1.1
    rw [hv, map_smul]
    rfl

theorem xxw_tr_eq {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (t : FC n' c' n c → E) :
    Tr ρ t = xxwLin ρ t + Tr ρ 0 := by
  funext f
  simp only [Tr, Pi.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [xxw_eN_eq]
  have h := xxw_diff (E := E) t f.1.2
  rw [sub_eq_iff_eq_add] at h
  rw [h, map_add (f := _), Pi.add_apply]
  rfl

theorem xxw_tr_inv {n' c' n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : ρ ∈ R1 E n c) (t : FC n' c' n c → E) :
    Tr ρ⁻¹ (Tr ρ t) = t := by
  have hρi : ρ⁻¹ ∈ R1 E n c := inv_mem hρ
  have e1 := unfolding_affine_space_invariant E n' c' n c ρ hρ 0 t
  have e2 := unfolding_affine_space_invariant E n' c' n c ρ⁻¹ hρi 0 (Tr ρ t)
  rw [LinearMap.comp_zero] at e1 e2
  have e3 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (Tr ρ⁻¹ (Tr ρ t)) =
      xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t := by
    rw [← e2, ← e1]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  funext f
  have h := congrFun (LinearMap.congr_fun e3 (Pi.single f.1.2 1)) f.1.1
  rw [xxw_entry, xxw_entry, dif_pos f.2, dif_pos f.2] at h
  exact h

theorem free_coordinate_affine_invertible : TrAffP := by
  intro E _ n' c' n c ρ hρ
  have hρi : ρ⁻¹ ∈ R1 E n c := inv_mem hρ
  have key : ∀ σ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), σ ∈ R1 E n c →
      ∀ t : FC n' c' n c → E, xxwLin σ⁻¹ (xxwLin σ t) = t := by
    intro σ hσ t
    have h1 := xxw_tr_inv hσ t
    have h0 := xxw_tr_inv hσ (0 : FC n' c' n c → E)
    rw [xxw_tr_eq σ⁻¹, xxw_tr_eq σ t, map_add (f := _)] at h1
    rw [xxw_tr_eq σ⁻¹] at h0
    calc xxwLin σ⁻¹ (xxwLin σ t) = (xxwLin σ⁻¹ (xxwLin σ t) + xxwLin σ⁻¹ (Tr σ 0) + Tr σ⁻¹ 0) -
          (xxwLin σ⁻¹ (Tr σ 0) + Tr σ⁻¹ 0) := by abel
      _ = t - 0 := by rw [h1, h0]
      _ = t := sub_zero t
  refine ⟨{ xxwLin ρ with invFun := xxwLin ρ⁻¹, left_inv := key ρ hρ, right_inv := ?_ },
    fun t => xxw_tr_eq ρ t⟩
  intro t
  have := key ρ⁻¹ hρi t
  rwa [inv_inv] at this

theorem character_argument_constant_shift : ChArgP := by
  intro E _ n' c' n c ρ hρ xj t
  obtain ⟨h1, -⟩ := hρ
  unfold chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hic : i < c := Finset.mem_range.mp hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  by_cases hs : n' + i + 1 < n' + c'
  · obtain ⟨s, hs_eq⟩ : ∃ s : Fin (n' + c'), s.1 = n' + i + 1 := ⟨⟨_, hs⟩, rfl⟩
    rw [← hs_eq, xxw_eN_eq s]
    have hsn : ¬ s.1 < n' := by omega
    have hu : xx1 xj t (Pi.single s 1) -
        xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ∈ Ufl E n c (i + 1) := by
      rw [xx1_single_eq_of_not_lt xj t s hsn, xxw_diff, xxw_mem_Ufl]
      intro l hl
      have hlt := l.isLt
      rw [dif_neg]
      rintro ⟨-, h | ⟨-, h⟩⟩ <;> omega
    have hstep := xxw_step h1 i _ hu
    rw [xxw_mem_Ufl] at hstep
    have hn : n + i < n + c := by omega
    have h2 := hstep ⟨n + i, hn⟩ le_rfl
    have h0 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ⟨n + i, hn⟩ = 0 := by
      rw [xxw_entry, dif_pos]
      · rfl
      · refine ⟨by omega, Or.inr ⟨by omega, Or.inr ?_⟩⟩
        simp only [Fin.val_mk]
        omega
    simp only [atN, dif_pos hn]
    rw [map_sub, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0] at h2
    linear_combination h2
  · have h0 : eN E (n' + c') (n' + i + 1) = 0 := by
      funext l
      simp only [eN, Pi.zero_apply]
      rw [if_neg]
      have := l.isLt
      omega
    rw [h0]
    simp [atN]

end XX

end PI.TwistedEisensteinNonvanishing.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfHypotheses
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

theorem psi_ne {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D : ℕ}
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) (z : E) : psi z ≠ 0 := by
  obtain ⟨hmul, hint, hout⟩ := hpsi
  by_cases hz : IntAt P ((qOf P : E) ^ D * z)
  · have hz' : IntAt P ((qOf P : E) ^ D * (-z)) := by
      obtain ⟨r, s, hs, hrs⟩ := hz
      exact ⟨-r, s, hs, by rw [mul_neg, mul_neg, hrs, map_neg]⟩
    have h0 : IntAt P 0 := ⟨0, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
    have h := hmul z (-z) hz hz'
    rw [add_neg_cancel, hint 0 h0] at h
    intro hz0
    rw [hz0, zero_mul] at h
    exact one_ne_zero h
  · rw [hout z hz]
    exact one_ne_zero

private lemma intAt_add_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a b : E}
    (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h' | h'
    · exact hs1 h'
    · exact hs2 h'
  · rw [map_mul, map_add (f := _), map_mul, map_mul, ← h1, ← h2]
    ring

private lemma intAt_neg_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a : E}
    (h : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, hr⟩ := h
  exact ⟨-r, s, hs, by rw [mul_neg, hr, map_neg]⟩

private lemma intAt_qOf_pow_mul {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E}
    (h : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  obtain ⟨r, s, hs, hr⟩ := h
  refine ⟨(qOf P : 𝓞 E) ^ k * r, s, hs, ?_⟩
  rw [map_mul, map_pow, map_natCast, ← hr]
  ring

theorem key_pt {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D j : ℕ} (hjD : j ≤ D)
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) {C gx gy : K} (hC : C ≠ 0)
    {cx cy c0 : E} (hg : gx = C * gy) (hc : cy = cx + c0)
    (hbx : gx ≠ 0 → IntAt P ((qOf P : E) ^ j * cx)) (hby : gy ≠ 0 → IntAt P ((qOf P : E) ^ j * cy)) :
    gx * psi (-cx) = (C * psi c0) * (gy * psi (-cy)) := by
  by_cases hgy : gy = 0
  · rw [hg, hgy]
    ring
  · have hgx : gx ≠ 0 := by
      rw [hg]
      exact mul_ne_zero hC hgy
    have ix := hbx hgx
    have iy := hby hgy
    have lift : ∀ t : E, IntAt P ((qOf P : E) ^ j * t) → IntAt P ((qOf P : E) ^ D * t) := by
      intro t ht
      have h := intAt_qOf_pow_mul (D - j) ht
      rwa [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD] at h
    have i_cx := lift cx ix
    have i_cy := lift cy iy
    have i_c0 : IntAt P ((qOf P : E) ^ D * c0) := by
      have e : (qOf P : E) ^ D * c0 = (qOf P : E) ^ D * cy + -((qOf P : E) ^ D * cx) := by
        rw [hc]
        ring
      rw [e]
      exact intAt_add_twisted_eisenstein_coset i_cy (intAt_neg_twisted_eisenstein_coset i_cx)
    have i_ncy : IntAt P ((qOf P : E) ^ D * (-cy)) := by
      rw [mul_neg]
      exact intAt_neg_twisted_eisenstein_coset i_cy
    have hsplit := hpsi.1 (-cy) c0 i_ncy i_c0
    have e : -cy + c0 = -cx := by
      rw [hc]
      ring
    rw [e] at hsplit
    rw [hsplit, hg]
    ring

theorem RS_mul {E K : Type} [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) {ι : Type}
    [Fintype ι] [DecidableEq ι] (A B : ℕ) (C : K) (H : (ι → E) → K) :
    RS P A B (fun t => C * H t) = C * RS P A B H := by
  simp only [RS, ← Finset.mul_sum]
  ring

theorem core {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hq0 : ((qOf P : ℕ) : K) ≠ 0) (hStab : StabP) (hCoV : CoVP) (hXX : XXP) (hTA : TrAffP)
    (hRX : ResXSurjP) (hCA : ChArgP) (hCB : ChArgBddP)
    {n' c' n c D j : ℕ} (hjD : j ≤ D) {psi : E → K} (hpsi : PsiOk D P psi)
    (G G' : SF E K (n' + c') (n + c)) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (hρ : ρ ∈ R1 E n c)
    (C : K) (hC : C ≠ 0) (hCeq : ∀ x, G' x = C * G (ρ.toLinearMap ∘ₗ x))
    (hS : ∀ x, G x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hS' : ∀ x, G' x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hH : ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      Good P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))))
    (hne : ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0) :
    ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0 := by
  obtain ⟨L, hL⟩ := hTA E n' c' n c ρ hρ
  obtain ⟨cT, hcT, hcov⟩ := hCoV E K P hp hq hq0 (FC n' c' n c) L (Tr ρ 0)
  obtain ⟨a', b', hab⟩ := hcov j j
  have key : ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      G' (xx1 xj t) * psi (-chArg (xx1 xj t)) =
        (C * psi (chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E)))) *
          (G (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)) * psi (-chArg (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)))) := by
    intro xj t
    have e1 : ρ.toLinearMap ∘ₗ xx1 xj t = xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0) := by
      rw [hXX E n' c' n c ρ hρ xj t, hL t]
    rw [← e1]
    exact key_pt hjD hpsi hC (hCeq _) (hCA E n' c' n c ρ hρ xj t)
      (fun h0 => hCB E P n' c' n c j _ (hS' _ h0)) (fun h0 => hCB E P n' c' n c j _ (hS _ h0))
  obtain ⟨A0, B0, hAB⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      RS P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))) ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (hAB (max A0 j) (max B0 j) (le_max_left _ _) (le_max_left _ _))
    refine ⟨y, ?_⟩
    simp only [Pi.zero_apply] at hy
    rwa [← hStab E K P hp hq hq0 _ j j _ (hH y) _ _ (le_max_right _ _) (le_max_right _ _)]
  obtain ⟨xj, rfl⟩ := hRX E n' n c ρ hρ y
  obtain ⟨hg, heq⟩ := hab _ (hH (resX ρ ∘ₗ xj))
  refine ⟨a', b', fun A' B' hA' hB' hz => ?_⟩
  have h1 := congrFun hz xj
  simp only [Pi.zero_apply] at h1
  rw [show (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t))) = fun t =>
      (C * psi (chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E)))) *
        (G (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)) * psi (-chArg (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0))))
      from funext (key xj), RS_mul, hStab E K P hp hq hq0 _ a' b' _ hg A' B' hA' hB', heq] at h1
  exact mul_ne_zero (mul_ne_zero hC (psi_ne hpsi _)) (mul_ne_zero hcT hy) h1

theorem twisted_eisenstein_of_hypotheses (hStab : StabP) (hCoV : CoVP) (hOm : OmStepP) (hPS : PhiSuppP) (hPP : PhiPerP)
    (hBE : BddEntP) (hGS : GSuppP) (hGP : GPerP) (hHG : HGoodP) (hCB : ChArgBddP) (hXX : XXP)
    (hTA : TrAffP) (hRX : ResXSurjP) (hCA : ChArgP) : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing := by
  intro E K _ _ _ _ R P hp hq psi sq cq ξ hpsi hsq hcq i hi hal h h' hbal hbh hbh' hdc hne
  obtain ⟨r, hr, κ, hκ, rfl⟩ := hdc
  have m1 : i ≤ i * (R.t + 1) := Nat.le_mul_of_pos_right i (Nat.succ_pos _)
  have m2 : i + 1 ≤ (i + 1) * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hk := R.m_add_three_le_k
  have s1 : R.r = (R.k + (i + 1)) + cOf R (i + 1) := by
    unfold Ranks.r cOf
    omega
  have s3 : R.k + (i + 1) ≤ R.N (i + 1) := by
    unfold Ranks.N
    omega
  have s4 : R.r ≤ R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    omega
  have s5 : R.k ≤ R.N i := by
    unfold Ranks.N
    omega
  have s6 : R.k ≤ R.N (i + 1) := by
    unfold Ranks.N
    omega
  have s7 : cOf R (i + 1) < cOf R i := by
    unfold cOf
    omega
  by_cases hq0 : ((qOf P : ℕ) : K) = 0
  · exfalso
    have hFC : Nonempty (FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) :=
      ⟨⟨(⟨0, by omega⟩, ⟨R.N i + cOf R (i + 1), by omega⟩), by
        show IsFree (R.N i) (R.N (i + 1)) (cOf R (i + 1)) 0 (R.N i + cOf R (i + 1))
        unfold IsFree
        omega⟩⟩
    obtain ⟨A0, B0, hAB⟩ := hne
    refine hAB A0 (B0 + 1) le_rfl (Nat.le_succ _) ?_
    funext xj
    show (((qOf P : K) ^ (B0 + 1))⁻¹) ^ Fintype.card (FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) * _ = 0
    rw [hq0, zero_pow (Nat.succ_ne_zero _), inv_zero, zero_pow Fintype.card_ne_zero, zero_mul]
  have hρ : r⁻¹ ∈ R1 E (R.N (i + 1)) (cOf R (i + 1)) := inv_mem hr
  obtain ⟨C, hC, hCeq⟩ := hOm E K P hp hq sq cq hsq hcq ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
    (R.k + (i + 1)) s1 (Nat.le_add_right _ _) s3 s4 s5 hal h r κ hκ
  obtain ⟨bh1, bh2⟩ := hBE E P R (i + 1) h hbh
  obtain ⟨bh1', -⟩ := hBE E P R (i + 1) (r * h * κ) hbh'
  obtain ⟨ba1, ba2⟩ := hBE E P R i hal hbal
  have hPhiS := hPS E K P (qOf P) ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) s6 s5
  have hPhiP := hPP E K P hp hq ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
  have gS := hGS E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal h _ (i + 1) hPhiS ba2 bh1
  have gS' := hGS E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal (r * h * κ) _ (i + 1) hPhiS ba2 bh1'
  have gP := hGP E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal h _ i hPhiP ba1 bh2
  have hHg := hHG E K P hp (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) (2 * R.m) (i + 1) (by omega) psi hpsi _ gS gP
  exact core P hp hq hq0 hStab hCoV hXX hTA hRX hCA hCB (D := 2 * R.m) (j := i + 1) (by omega) hpsi _ _ r⁻¹ hρ
    C hC hCeq gS gS' hHg hne

end PI.TwistedEisensteinNonvanishing.W
end
end

namespace PI.TwistedEisensteinNonvanishing.W

theorem ntAll : NTAll := ⟨integer_integral_iff_dvd, integral_approximation_by_integer, element_eq_prime_power_mul_unit, valuation_exponent_unique, unit_congruent_to_integer⟩

theorem twisted_eisenstein_of_remaining (hPS : PhiSuppP) (hPP : PhiPerP) (hBE : BddEntP) : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  twisted_eisenstein_of_hypotheses (stab_of ntAll) (cov_of ntAll) (omStep_of jacobian_transformation_law (muNe_of ntAll)) hPS hPP hBE translated_function_support
    translated_function_invariance unfolding_integrand_good character_argument_bounded unfolding_affine_space_invariant free_coordinate_affine_invertible restriction_to_affine_surjective character_argument_constant_shift

end PI.TwistedEisensteinNonvanishing.W
end

theorem TwistedEisensteinNonvanishing : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  PI.TwistedEisensteinNonvanishing.W.twisted_eisenstein_of_remaining PI.TwistedEisensteinNonvanishing.W.test_function_support PI.TwistedEisensteinNonvanishing.W.test_function_periodicity PI.TwistedEisensteinNonvanishing.W.bounded_matrix_entries

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.LowAdj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem low_mk {R : Type} [CommRing R] (x y z t : R) :
    IsLow (!![1, 0, 0, 0; x, 1, 0, 0; y + t * x, t, 1, 0; z, y, -x, 1] : M4 R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · intro i
    fin_cases i <;> simp
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_adj {R : Type} [CommRing R] {m : M4 R} (h : IsLow m) : IsLow (adj m) := by
  refine ⟨sp_adj h.1, fun i => ?_, fun i j hij => ?_⟩
  · rw [adj_apply, h.2.1]
    fin_cases i <;> simp [sgn]
  · rw [adj_apply, h.2.2 _ _ (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem up_of {R : Type} [CommRing R] {w : M4 R} (h : IsGSp 1 w) (h0 : IsUnit (w 0 0))
    (h1 : w 1 0 = 0) (h2 : w 2 0 = 0) (h3 : w 3 0 = 0) (h4 : w 2 1 = 0) : IsUp w := by
  have e := sp_adj_mul h
  have e1 := congrFun (congrFun e 1) 0
  have e2 := congrFun (congrFun e 2) 0
  simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3] at e1 e2
  have a1 : w 3 2 = 0 := (h0.mul_left_eq_zero).1 e1
  have a2 : w 3 1 = 0 := (h0.mul_left_eq_zero).1 e2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption

theorem UpperTheory.V.Ws.Lab.luSp :
    ∀ (R : Type) [CommRing R] (u : M4 R), IsGSp 1 u → IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) →
      ∃ n b : M4 R, IsLow n ∧ IsGSp 1 b ∧ IsUp b ∧ u = n * b := by
  intro R _ u hu h0 hD
  obtain ⟨ai, hai⟩ := h0.exists_right_inv
  obtain ⟨di, hdi⟩ := hD.exists_right_inv
  obtain ⟨x, hx⟩ : ∃ x : R, x = -(u 1 0 * ai) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : R, s = (u 2 1 * u 1 0 - u 2 0 * u 1 1) * di := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : R, t = (u 0 1 * u 2 0 - u 0 0 * u 2 1) * di := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : R, y = s - t * x := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : R, z = (-(y * u 1 0) + x * u 2 0 - u 3 0) * ai := ⟨_, rfl⟩
  have hm := low_mk x y z t
  refine ⟨_, _, low_adj hm, sp_mul hm.1 hu, ?_, ?_⟩
  · refine up_of (sp_mul hm.1 hu) ?_ ?_ ?_ ?_ ?_
    · simpa [Matrix.mul_apply, Fin.sum_univ_four] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hx + (-u 1 0) * hai
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hy + u 0 0 * hs + u 1 0 * ht + (-u 2 0) * hdi
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hz + (-(y * u 1 0) + x * u 2 0 - u 3 0) * hai
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 1 * hy + u 0 1 * hs + u 1 1 * ht + (-u 2 1) * hdi
  · rw [← Matrix.mul_assoc, sp_adj_mul hm.1, Matrix.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.UpConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y : M4 R) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hX i k h, zero_mul]
    · rw [hY k i h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem up_adj {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := by
  intro i j h
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

theorem UpperTheory.V.Ws.Lab.upConj :
    ∀ (R : Type) [CommRing R] (b T : M4 R), IsGSp 1 b → IsUp b → IsUp T → IsUp (b * T * adj b) ∧ ∀ i, (b * T * adj b : M4 R) i i = T i i := by
  intro R _ b T hb hbu hT
  have hadj := up_adj hbu
  refine ⟨up_mul (up_mul hbu hT) hadj, fun i => ?_⟩
  have h1 : b i i * adj b i i = 1 := by
    have := congrFun (congrFun (sp_mul_adj hb) i) i
    rw [up_mul_diag hbu hadj] at this
    simpa using this
  rw [up_mul_diag (up_mul hbu hT) hadj, up_mul_diag hbu hT]
  linear_combination (T i i) * h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ResFlag
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem resFlag_field {k : Type} [Field k] (u T : M4 k) (d : Fin 4 → k) (hu : IsGSp 1 u)
    (hT : IsUp T) (e : Matrix.diagonal d * u = u * T) (hd : ∀ i j, lamW i ≠ lamW j → d i - T j j ≠ 0) :
    u 1 0 = 0 ∧ u 3 0 = 0 ∧ (u 0 0 ≠ 0 ∨ u 2 0 ≠ 0) ∧
      (u 0 0 ≠ 0 → u 0 0 * u 1 1 - u 0 1 * u 1 0 ≠ 0 ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0) := by
  have t10 : T 1 0 = 0 := hT _ _ (by decide)
  have t20 : T 2 0 = 0 := hT _ _ (by decide)
  have t30 : T 3 0 = 0 := hT _ _ (by decide)
  have t21 : T 2 1 = 0 := hT _ _ (by decide)
  have t31 : T 3 1 = 0 := hT _ _ (by decide)
  have c0 : ∀ i, (d i - T 0 0) * u i 0 = 0 := fun i => by
    have := congrFun (congrFun e i) 0
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t10, t20, t30] at this
    linear_combination this
  have c1 : ∀ i, (d i - T 1 1) * u i 1 = u i 0 * T 0 1 := fun i => by
    have := congrFun (congrFun e i) 1
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t21, t31] at this
    linear_combination this
  have h10 : u 1 0 = 0 := (mul_eq_zero.1 (c0 1)).resolve_left (hd _ _ (by decide))
  have h30 : u 3 0 = 0 := (mul_eq_zero.1 (c0 3)).resolve_left (hd _ _ (by decide))
  have s := sp_adj_mul hu
  have s00 := congrFun (congrFun s 0) 0
  have s10 := congrFun (congrFun s 1) 0
  have s11 := congrFun (congrFun s 1) 1
  have s31 := congrFun (congrFun s 3) 1
  rw [Matrix.mul_apply, Fin.sum_univ_four] at s00 s10 s11 s31
  rw [Matrix.one_apply_eq] at s00 s11
  rw [Matrix.one_apply_ne (by decide)] at s10 s31
  have a30 : adj u 3 0 = - u 3 0 := by simp [adj_apply, sgn, Fin.rev]
  have a31 : adj u 3 1 = - u 2 0 := by simp [adj_apply, sgn, Fin.rev]
  have a32 : adj u 3 2 = u 1 0 := by simp [adj_apply, sgn, Fin.rev]
  have a33 : adj u 3 3 = u 0 0 := by simp [adj_apply, sgn, Fin.rev]
  rw [a30, a31, a32, a33] at s31
  refine ⟨h10, h30, ?_, fun h00 => ?_⟩
  · by_contra hn
    push Not at hn
    rw [hn.1, hn.2, h10, h30] at s00
    simp at s00
  · have hA : d 0 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have hB : d 2 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have key : u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hB)
      linear_combination (d 0 - T 1 1) * u 0 0 * c1 2 - (d 2 - T 1 1) * u 2 0 * c1 0
        + u 2 0 * T 0 1 * c0 0 - u 0 0 * T 0 1 * c0 2
    refine ⟨fun hn => ?_, key⟩
    rw [h10, mul_zero, sub_zero] at hn
    have h11 : u 1 1 = 0 := (mul_eq_zero.1 hn).resolve_left h00
    rw [h10, h30, h11] at s31
    have h31 : u 3 1 = 0 := by
      apply mul_left_cancel₀ h00
      linear_combination s31
    rw [h10, h30] at s10
    rw [h11, h31] at s11
    apply h00
    linear_combination u 0 1 * s10 - u 0 0 * s11 + adj u 1 2 * key

theorem UpperTheory.V.Ws.Lab.resFlag :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R) (d d' : Fin 4 → R), Cg (maximalIdeal R) X (Matrix.diagonal d) → IsGSp 1 u →
      IsUp (adj u * X * u) → (∀ i, (adj u * X * u : M4 R) i i - d' i ∈ maximalIdeal R) → (∀ i j, lamW i ≠ lamW j → IsUnit (d i - d' j)) →
      u 1 0 ∈ maximalIdeal R ∧ u 3 0 ∈ maximalIdeal R ∧ (IsUnit (u 0 0) ∨ IsUnit (u 2 0)) ∧
        (IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 ∈ maximalIdeal R) := by
  intro R _ _ X u d d' hX hu hUp hdi hsep
  have hX' : X.map (residue R) = Matrix.diagonal fun i => residue R (d i) := by
    ext i j
    have := (residue_eq_zero_iff _).2 (hX i j)
    rw [map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.diagonal_apply_ne _ e]
  have hu' : IsGSp 1 (u.map (residue R)) := by simpa using gsp_map (residue R) hu
  have e : X * u = u * (adj u * X * u) := by
    rw [← mul_assoc, ← mul_assoc, sp_mul_adj hu, one_mul]
  have e' := congrArg (fun M : M4 R => M.map (residue R)) e
  beta_reduce at e'
  rw [Matrix.map_mul, Matrix.map_mul (L := u), hX'] at e'
  have H := resFlag_field (u.map (residue R)) ((adj u * X * u).map (residue R)) _ hu'
    (fun i j h => by rw [Matrix.map_apply, hUp i j h, map_zero]) e' (fun i j h => by
      have h1 := (residue_eq_zero_iff _).2 (hdi j)
      rw [map_sub, sub_eq_zero] at h1
      rw [Matrix.map_apply, h1, ← map_sub]
      exact ((hsep i j h).map _).ne_zero)
  simp only [Matrix.map_apply, ← map_mul, ← map_sub, residue_eq_zero_iff, Ne] at H
  simpa only [notMem_maximalIdeal] using H
end

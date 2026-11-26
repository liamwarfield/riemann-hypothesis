module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_diagonal_rep_matrix_eq {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) :
    (GG.map (algebraMap O R) (r0 η Ψ g)).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
  rw [GG.map_mat]
  show ((tor O (Ψ g)).val).map (algebraMap O R) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]
  rfl

private theorem conjBy_inv_one {R D : Type} [CommRing R] [Group D] (r : D →* @UpperTheory.V.U3.GG 3 R _) :
    conjBy (1 : GL (Fin 3) R)⁻¹ r = r := by
  ext1 g
  simp [conjBy]

private theorem diagIn_one {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* @UpperTheory.V.U3.GG 3 R _)
    (hr : ∀ g, (r g).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g)) : DiagIn η Ψ I r 1 := by
  have hne : ∀ a b : Fin 3, wt a b ≠ 0 → a ≠ b := by
    intro a b h hab
    subst hab
    simp [wt] at h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne)
  · intro s _ _ a
    rw [conjBy_inv_one, hr, Matrix.diagonal_apply_eq]
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne')

theorem UpperTheory.V.UnitaryThreeInertia.isPt_rz :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)], F.IsPt g₁ (F.rz R) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hok g₁ R _ _ _ _
  have hmat : ∀ g, (F.rz R g).mat = diagonal fun a => algebraMap O R (psi F.Ψ a g) :=
    fun g => map_diagonal_rep_matrix_eq F.η F.Ψ g
  have hinhat : InHat (1 : GL (Fin 3) R) := by
    intro a b
    simp
  have hloc : ∀ v, ∀ s, ((F.rz R).comp (F.loc v) s).mat =
      diagonal fun a => algebraMap O R (psi (F.Ψv v) a s) := fun v s => hmat _
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro g
    rfl
  · intro g a b
    have e : (F.rz R g).mat = (r0 F.η F.Ψ g).mat.map (algebraMap O R) := GG.map_mat _ _
    rw [e, sub_self, Matrix.zero_apply]
    exact zero_mem _
  · intro v
    refine ⟨fun _ => ⟨1, hinhat, (diagIn_one _ _ _ _ (hloc v)).toTriIn⟩,
      fun _ => ⟨1, hinhat, diagIn_one _ _ _ _ (hloc v)⟩, fun hv s hs => ?_⟩
    have h1 : F.Ψ (F.loc v s) = 1 := hok.teich v hv s hs
    have h2 : F.η (F.loc v s) = 1 := hs.1.2
    show GG.map (algebraMap O R) (r0 F.η F.Ψ (F.loc v s)) = 1
    have e : r0 F.η F.Ψ (F.loc v s) = 1 := by
      apply SemidirectProduct.ext
      · rw [unitaryThreeReflection_left, h1, map_one]
        rfl
      · exact h2
    rw [e, map_one]
  · have hc : ∀ a, psi F.Ψ a F.c = 1 := by
      intro a
      simp [psi, hok.Ψc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmat]
      simp [hc, Matrix.diagonal_one]
    · simp [zmat, hmat]
    · simp [zmat, hmat]
  · intro n
    have hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono
        (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit (algebraMap O R) x hx)) n
    have key : ∀ g g', Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g : O) =
        Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g' : O) → ∀ a,
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g)) =
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g')) := by
      intro g g' h a
      let q : O →* O ⧸ maximalIdeal O ^ n := (Ideal.Quotient.mk (maximalIdeal O ^ n) : O →* O ⧸ maximalIdeal O ^ n)
      have hu : Units.map q (F.Ψ g) = Units.map q (F.Ψ g') := Units.ext h
      have h2 : ((Units.map q (F.Ψ g ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) =
          ((Units.map q (F.Ψ g' ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) := by
        rw [map_zpow (Units.map q) (F.Ψ g) (wt1 a), map_zpow (Units.map q) (F.Ψ g') (wt1 a), hu]
      have h3 : Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g) =
          Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g') := h2
      rw [Ideal.Quotient.eq] at h3 ⊢
      rw [← map_sub]
      exact hle (Ideal.mem_map_of_mem _ h3)
    have hf := hok.Ψ_cont n
    rw [IsLocallyConstant.iff_exists_open] at hf ⊢
    intro x
    obtain ⟨U, hU, hxU, hUx⟩ := hf x
    refine ⟨U, hU, hxU, fun x' hx' => ?_⟩
    simp only [hmat]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact key x' x (hUx x' hx') a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEigvec
open Matrix IsLocalRing Polynomial

private theorem UpperTheory.Reformulated.B.Qf19.exists_eigvec {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R)
    (hu : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b))
    (hm : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R) (a : Fin 3) :
    ∃ (l : R) (v : Fin 3 → R), v a = 1 ∧ (∀ b, b ≠ a → v b ∈ maximalIdeal R) ∧ X *ᵥ v = l • v := by
  have hd : X.map (residue R) = diagonal fun b => residue R (X b b) := by
    ext b c
    by_cases h : b = c
    · subst h; simp
    · rw [diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]; exact hm b c h
  have hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0 := fun b hb => by
    rw [← map_sub]; exact ((hu a b hb.symm).map (residue R)).ne_zero
  have hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)
  have hc : X.charpoly.map (residue R) =
      (Polynomial.X - C (residue R (X a a))) *
        ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b))) := by
    rw [← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal,
      Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]
  obtain ⟨l, hl, hla⟩ := HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a)
    (by
      rw [← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]
      simp)
    (by
      change IsUnit (residue R _)
      rw [← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]
      simpa [eval_prod] using hP)
  have hla' : residue R l = residue R (X a a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hla
  set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM
  have hdet : M.det = 0 := by rw [hM, ← Matrix.eval_charpoly]; exact hl
  have hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b) := by
    ext b c
    have := congrFun (congrFun hd b) c
    by_cases h : b = c
    · subst h; simp [hM, hla']
    · rw [diagonal_apply_ne _ h] at this ⊢
      simpa [hM, diagonal_apply_ne _ h] using this
  have hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i,
      (residue R (X a a) - residue R (X j j))) b a := fun b => by
    have := (residue R).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal] at this
    exact congrFun (congrFun this b) a
  have hun : IsUnit (M.adjugate a a) := by
    rw [← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]; exact hP
  obtain ⟨u, hu'⟩ := hun
  have hker : M *ᵥ (fun b => M.adjugate b a) = 0 := by
    ext b
    have := congrFun (congrFun (mul_adjugate M) b) a
    rw [hdet, zero_smul] at this
    exact this
  refine ⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩
  · simp [← hu']
  · refine Ideal.mul_mem_left _ _ ?_
    rw [← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]
  · rw [hM, sub_mulVec, sub_eq_zero] at hker
    rw [mulVec_smul, ← hker, smul_comm l]
    congr 1
    ext b
    simp [mulVec_diagonal, hM]

theorem UpperTheory.Reformulated.B.Qf19.exists_canon :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (X : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
      (∀ (a b : Fin (3 : ℕ)), a ≠ b → IsUnit (X a a - X b b)) →
        (∀ (a b : Fin (3 : ℕ)), a ≠ b → X a b ∈ IsLocalRing.maximalIdeal R) →
          ∃ (h : GL (Fin (3 : ℕ)) R), UpperTheory.V.UnitaryThreeInertia.Canon X h := by
  intro R _ _ _ X hu hm
  choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm
  set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH
  have hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R := fun a b => by
    by_cases h : a = b
    · subst h; simp [hH, h1]
    · simpa [hH, one_apply_ne h] using h2 b a h
  have hmap : (residue R).mapMatrix H = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hhat a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, map_apply, this]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]
  have hdet : IsUnit H.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]; simp
  obtain ⟨h, hh⟩ := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hXH : X * H = H * diagonal l := by
    ext b a
    have := congrFun (h3 a) b
    rw [mul_diagonal, mul_comm]
    exact this
  refine ⟨h, ?_, fun a => ?_, ?_⟩
  · intro a b; rw [hh]; exact hhat a b
  · rw [hh]; exact h1 a
  · have : ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l := by
      rw [Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]
      simp
    rw [this]; exact isDiag_diagonal l
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.exists_canon :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → (∀ a b, a ≠ b → X a b ∈ maximalIdeal R) → ∃ h, Canon X h :=
  _root_.UpperTheory.Reformulated.B.Qf19.exists_canon
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem tc_conj_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem tc_res {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h) :
    (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 ∧
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
  have h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  refine ⟨h1, ?_⟩
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1 := by
    rw [Units.inv_mul]; simp
  rwa [Matrix.map_mul, h1, Matrix.mul_one] at this

private theorem tc_res_conj {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h)
    (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    residue R ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) a b) = residue R (X a b) := by
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R) := by
    rw [Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]
  exact congrFun (congrFun this a) b

private theorem tc_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem tc_up {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d20 : Δ 2 0 = 0 := hΔ (by decide)
  have d21 : Δ 2 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, d10, d12, d20, d21] at e10 e20 e21
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e10)
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_low {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, 0 < wt a b → k a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d02 : Δ 0 2 = 0 := hΔ (by decide)
  have d01 : Δ 0 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, d10, d12, d02, d01] at e01 e02 e12
  have k12 : k 1 2 = 0 := (hu 1 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e12)
  have k02 : k 0 2 = 0 := (hu 0 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e02)
  have k01 : k 0 1 = 0 := (hu 0 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_up' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, wt a b < 0 → k a b = 0) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    (∀ a b, wt a b < 0 → M a b = 0) ∧ ∀ a, M a a = U a a := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  have e22 := congrFun (congrFun e 2) 2
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have k10 := hk 1 0 (by decide)
  have k20 := hk 2 0 (by decide)
  have k21 := hk 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, k10, k20, k21] at e10 e20 e21 e00 e11 e22
  have m10 : M 1 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e10)
  have m20 : M 2 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e20)
  have m21 : M 2 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m20] at e21; linear_combination e21)
  have m00 : M 0 0 = U 0 0 := sub_eq_zero.1 ((hu 0).mul_left_eq_zero.1 (by linear_combination e00))
  have m11 : M 1 1 = U 1 1 := sub_eq_zero.1 ((hu 1).mul_left_eq_zero.1 (by
    rw [m10] at e11; linear_combination e11))
  have m22 : M 2 2 = U 2 2 := sub_eq_zero.1 ((hu 2).mul_left_eq_zero.1 (by
    rw [m20, m21] at e22; linear_combination e22))
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)
  · fin_cases a <;> assumption

private theorem tc_low' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, 0 < wt a b → k a b = 0) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    ∀ a b, 0 < wt a b → M a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have k01 := hk 0 1 (by decide)
  have k02 := hk 0 2 (by decide)
  have k12 := hk 1 2 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, k01, k02, k12] at e01 e02 e12
  have m12 : M 1 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e12)
  have m02 : M 0 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e02)
  have m01 : M 0 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_rel {R : Type} [CommRing R] (h h' : GL (Fin 3) R) (X : Matrix (Fin 3) (Fin 3) R) :
    (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) * (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') =
      (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') *
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h') := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (h : Matrix (Fin 3) (Fin 3) R), ← Matrix.mul_assoc (h' : Matrix (Fin 3) (Fin 3) R),
    Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.cond_iff_canon :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := R)) (x : D) (h : GL (Fin 3) R), Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Canon (r x).mat h →
      (CondT η Ψ I r ↔ TriIn η Ψ I r h) ∧ (CondD η Ψ I r ↔ DiagIn η Ψ I r h) := by
  intro O R D _ _ _ _ _ _ η Ψ I r x h hr hx hΨ hc
  have cm : ∀ (h : GL (Fin 3) R) (g : D), η g = 1 →
      (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h :=
    fun h g hg => tc_conj_mat r h g ((hr.mult g).trans hg)
  have hX : ∀ a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  have hu : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a b, a ≠ b →
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h) a a -
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h') b b) := by
    intro h' hh' a b hab
    rw [← residue_ne_zero_iff_isUnit, map_sub, tc_res_conj h hc.hat, tc_res_conj h' hh', hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit]
    exact (tc_unit (Ψ x) hΨ a b hab).map _
  have hk : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a,
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') a a) := by
    intro h' hh' a
    have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h').map (residue R) = 1 := by
      rw [Matrix.map_mul, (tc_res h hc.hat).2, (tc_res h' hh').1, Matrix.one_mul]
    have := congrFun (congrFun this a) a
    rw [Matrix.map_apply, Matrix.one_apply_eq] at this
    rw [← residue_ne_zero_iff_isUnit, this]
    exact one_ne_zero
  have hT : ∀ h' : GL (Fin 3) R, InHat h' → TriIn η Ψ I r h' → TriIn η Ψ I r h := by
    intro h' hh' ht
    have k1 := tc_up _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.tri x hx) (hu h' hh')
    have k2 := fun g (hg : η g = 1) => tc_up' _ _ _ (tc_rel h h' (r g).mat) k1
      (by rw [← cm h' g hg]; exact ht.tri g hg) (hk h' hh')
    refine ⟨fun g hg => ?_, fun s hs hg a => ?_⟩
    · rw [cm h g hg]; exact (k2 g hg).1
    · rw [cm h s hg, (k2 s hg).2, ← cm h' s hg]; exact ht.ine s hs hg a
  refine ⟨⟨fun ⟨h', hh', ht⟩ => hT h' hh' ht, fun ht => ⟨h, hc.hat, ht⟩⟩,
    ⟨fun ⟨h', hh', ht⟩ => ⟨hT h' hh' ht.toTriIn, fun g hg => ?_⟩, fun ht => ⟨h, hc.hat, ht⟩⟩⟩
  have k1 := tc_low _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.low x hx) (hu h' hh')
  rw [cm h g hg]
  exact tc_low' _ _ _ (tc_rel h h' (r g).mat) k1 (by rw [← cm h' g hg]; exact ht.low g hg) (hk h' hh')
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonMap
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem tor_conj_apply {R : Type} [CommRing R] (t : Rˣ) (Y : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    ((tor R t).val * Y * (tor R t⁻¹).val) a b =
      ((t ^ wt1 a : Rˣ) : R) * Y a b * ((t⁻¹ ^ wt1 b : Rˣ) : R) := by
  rw [tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem tor_mul_inv {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t⁻¹).val * (tor R t).val = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

private theorem tor_mul_inv' {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t).val * (tor R t⁻¹).val = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem UpperTheory.V.UnitaryThreeInertia.canon_map :
    (∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), Canon X h → Canon (X.map φ) (GeneralLinearGroup.map φ h)) ∧
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R) (t : Rˣ), Canon X h → Canon ((tor R t).val * X * (tor R t⁻¹).val) (tor R t * h * tor R t⁻¹) := by
  refine ⟨fun {R R'} _ _ _ _ φ _ X h H => ⟨fun a b => ?_, fun a => ?_, ?_⟩,
    fun {R} _ _ X h t H => ⟨fun a b => ?_, fun a => ?_, ?_⟩⟩
  · have e : ((GeneralLinearGroup.map φ h : GL (Fin 3) R').val - 1) a b = φ ((h.val - 1) a b) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]; rfl
      · rw [map_zero]; rfl
    rw [e]
    exact map_nonunit φ _ (H.hat a b)
  · show φ (h.val a a) = 1
    rw [H.one, map_one]
  · have e : ((GeneralLinearGroup.map φ h)⁻¹ : GL (Fin 3) R').val * X.map φ * (GeneralLinearGroup.map φ h).val =
        ((h⁻¹ : GL (Fin 3) R).val * X * h.val).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, ← map_inv]; rfl
    rw [e]
    exact H.diag.map (map_zero φ)
  · have e : (tor R t * h * tor R t⁻¹).val - 1 = (tor R t).val * (h.val - 1) * (tor R t⁻¹).val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, tor_mul_inv', Units.val_mul, Units.val_mul]
    rw [e, tor_conj_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (H.hat a b))
  · rw [Units.val_mul, Units.val_mul, tor_conj_apply, H.one, mul_one, ← Units.val_mul, ← mul_zpow,
      mul_inv_cancel, _root_.one_zpow, Units.val_one]
  · have e : ((tor R t * h * tor R t⁻¹)⁻¹ : GL (Fin 3) R).val * ((tor R t).val * X * (tor R t⁻¹).val) *
        (tor R t * h * tor R t⁻¹).val = (tor R t).val * ((h⁻¹ : GL (Fin 3) R).val * X * h.val) * (tor R t⁻¹).val := by
      have hc : ∀ Y : Matrix (Fin 3) (Fin 3) R, (tor R t⁻¹).val * ((tor R t).val * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, tor_mul_inv, Matrix.one_mul]
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, inv_inv]
      simp only [Units.val_mul, Matrix.mul_assoc, hc]
    rw [e]
    intro a b hab
    rw [tor_conj_apply, H.diag hab, mul_zero, zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjPushMat
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  rfl

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply,
    map_mul, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R))
    (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]; rfl

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · unfold Upper at htri ⊢
    intro g hg a b hab
    rw [conj_push_mat, htri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, hine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_push φ H1, ?_⟩
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [conj_push_mat, hlow g hg a b hab, map_zero]

variable [IsLocalRing R] [IsLocalRing R']

private theorem map_mem_max (φ : R →ₐ[O] R') [IsLocalHom φ] {x : R} (hx : x ∈ maximalIdeal R) :
    φ x ∈ maximalIdeal R' := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun hu => hx (isUnit_of_map_unit φ x hu)

private theorem inHat_push (φ : R →ₐ[O] R') [IsLocalHom φ] {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  unfold InHat CongOne EntIn at *
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  exact map_mem_max φ (H a b)

private theorem adicCont_push [TopologicalSpace D] (φ : R →ₐ[O] R') [IsLocalHom φ]
    {r : D →* GG (m := 3) (R := R)}
    (H : AdicCont (maximalIdeal R) r) : AdicCont (maximalIdeal R') (push φ r) := by
  unfold UpperTheory.V.UnitaryThreeInertia.AdicCont at *
  intro n
  have hle : ∀ x ∈ maximalIdeal R ^ n, (φ : R →+* R') x ∈ maximalIdeal R' ^ n := by
    intro x hx
    have h1 : Ideal.map (φ : R →+* R') (maximalIdeal R) ≤ maximalIdeal R' := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact map_mem_max φ hy
    have h2 : Ideal.map (φ : R →+* R') (maximalIdeal R ^ n) ≤ maximalIdeal R' ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono h1 n
    exact h2 (Ideal.mem_map_of_mem _ hx)
  let ψ : R ⧸ maximalIdeal R ^ n →+* R' ⧸ maximalIdeal R' ^ n :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : R →+* R'))
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hle x hx))
  have hfun : (fun g => ((push φ r) g).mat.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) =
      (fun M => M.map ψ) ∘ (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) := by
    funext g
    ext a b
    simp only [Function.comp_apply, Matrix.map_apply, ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rfl
  rw [hfun]
  exact (H n).comp _

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.isPt_push :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ]
      (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
      [CommRing R'] [IsLocalRing R'] [Algebra O R'] (φ : R →ₐ[O] R') [IsLocalHom φ] (g₁ : Γ)
      (r : Γ →* GG (m := 3) (R := R)), F.IsPt g₁ r → F.IsPt g₁ (push φ r) := by
  intro O _ _ G Γ ι _ _ _ F R R' _ _ _ _ _ _ φ _ g₁ r hr
  have hmat : ∀ x : GG (m := 3) (R := R), ((GG.map (φ : R →+* R')) x).mat = x.mat.map φ := fun x => rfl
  have hpm : ∀ g, ((push φ r) g).mat = (r g).mat.map φ := fun g => hmat (r g)
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, adicCont_push φ hr.cont⟩
  · have hm := hr.mult
    unfold HasMult at hm ⊢
    intro g
    exact hm g
  · intro g a b
    rw [Matrix.sub_apply, hpm, Matrix.map_apply, Matrix.map_apply, ← AlgHom.commutes φ, ← map_sub]
    apply map_mem_max φ
    have := hr.red g a b
    rwa [Matrix.sub_apply, Matrix.map_apply] at this
  · intro v
    have hv := hr.loc v
    unfold Frame.LocAt at hv ⊢
    obtain ⟨hT, hD, hU⟩ := hv
    unfold CondT CondD CondU at *
    have hcomp : (push φ r).comp (F.loc v) = push φ (r.comp (F.loc v)) := rfl
    rw [hcomp]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk, htr⟩ := hT h
      exact ⟨_, inHat_push φ hk, triIn_push φ htr⟩
    · obtain ⟨k, hk, hdi⟩ := hD h
      exact ⟨_, inHat_push φ hk, diagIn_push φ hdi⟩
    · intro s hs
      show (GG.map (φ : R →+* R')) ((r.comp (F.loc v)) s) = 1
      rw [hU h s hs, map_one]
  · obtain ⟨hatc, hz12, hz21⟩ := hr.norm
    refine ⟨?_, ?_, ?_⟩
    · rw [hpm, hatc, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · unfold zmat at hz12 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz12,
        map_zero]
    · unfold zmat at hz21 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz21,
        map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtDeformU
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.locAt_deform_u :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v ∉ F.Tb →
      ∀ (r r₂ : F.D v →* GG (m := 3) (R := R)) (z : F.D v → Gb (k := ResidueField O) j)
        (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F _ _ R _ _ _ f hf _ j v hv r r₂ z γ _ hr hz hγ hd
  have hvl : v ≠ F.vl := fun h => hv (h ▸ Set.mem_insert _ _)
  refine ⟨fun h => absurd h hvl, fun h => absurd (Set.mem_insert_of_mem _ h) hv, fun _ s hs => ?_⟩
  have h1 : r s = 1 := hr.2.2 hv s hs
  have hz0 : z s = 0 := hz.2.1 hvl s hs
  have hγ0 : γ s = 0 := by
    ext a b
    obtain ⟨o, ho, e⟩ := hγ s a b
    rw [hz0] at ho
    have ho' : o ∈ maximalIdeal O := (residue_eq_zero_iff o).1 ho
    have hm : algebraMap O R o ∈ maximalIdeal R := fun h => ho' (IsLocalHom.map_nonunit o h)
    rw [e, Algebra.smul_def]
    exact hf _ hm
  obtain ⟨e1, e2⟩ := hd s
  rw [h1] at e1
  rw [h1, hγ0, add_zero, one_mul] at e2
  exact SemidirectProduct.ext (Units.ext e2) e1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsUniqueIsPtHom
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem gg_ext {R : Type} [CommRing R] {x y : GG (m := 3) (R := R)} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

private theorem exists_weight_inv_det_left_mem_weight_piece {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG (m := 3) (R := R)) (g : Γ) : ∃ j : ℤ, (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ wpart (O := O) u j := by
  have hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹ := by
    intro R' _ k
    have hJ : GeneralLinearGroup.det (Jgl (R := R') 3) * GeneralLinearGroup.det (Jgl (R := R') 3) = 1 := by
      rw [← map_mul, Jgl_mul_Jgl, map_one]
    have hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹ := by
      rw [← map_inv]
      apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]
    show GeneralLinearGroup.det (theta k) = _
    simp only [theta, map_mul, hT]
    rw [mul_right_comm, hJ, one_mul]
  have htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2) := by
    intro R' _ t
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]
  refine ⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩
  intro R' _ _ _ f f' t h
  have hg := congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h
  simp only [push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, map_mul, GeneralLinearGroup.map_det] at hg
  simp only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg
  have key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ := by
    rw [map_inv, map_inv]
    split_ifs with hs
    · rw [hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor] at hg
      rw [hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]
    · have : sgnAct 3 R' (u g).right = thetaAut 3 R' := by simp [sgnAct, hs]
      rw [this, hth, inv_inv, htor, GeneralLinearGroup.map_det] at hg
      rw [hg]
      generalize wt1 0 + wt1 1 + wt1 2 = w
      rw [show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]
      simp only [_root_.mul_inv_rev]
      ac_rfl
  have e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R') := fun φ => rfl
  rw [e f', e f, key, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.existsUnique_isPtHom :
    ∀ {O R Γ K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] [CommRing K] [Algebra O K] (u : Γ →* GG (m := 3) (R := R)) (ξ : Sring (O := O) u →ₐ[O] K), ∃! r, IsPtHom u ξ r := by
  intro O R Γ K _ _ _ _ _ _ _ u ξ
  have hmem : ∀ g a b, (u g).mat a b ∈ Sring (O := O) u := fun g a b =>
    mem_Sring u (entry_mem u g a b)
  have hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring (O := O) u := by
    intro g a b
    obtain ⟨j, hj⟩ := exists_weight_inv_det_left_mem_weight_piece (O := O) u g
    have hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring (O := O) u :=
      mem_Sring u hj
    let M' : Matrix (Fin 3) (Fin 3) (Sring (O := O) u) := fun a b => ⟨(u g).mat a b, hmem g a b⟩
    have hM : ((Sring (O := O) u).val : Sring (O := O) u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R) := by
      ext a b; rfl
    have hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R) :=
      (GeneralLinearGroup.val_det_apply _).symm
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Sring (O := O) u).mul_mem hd (M'.adjugate a b).2
  have hinj : Function.Injective (((Sring (O := O) u).val : Sring (O := O) u →+* R).mapMatrix (m := Fin 3)) := by
    intro x y h
    ext a b
    exact congrFun (congrFun h a) b
  let large₂ : Γ → GL (Fin 3) (Sring (O := O) u) := fun g =>
    { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩
      inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩
      val_inv := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.val_inv using 2 <;> ext a b <;> rfl
      inv_val := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }
  have gmap_inj : Function.Injective (GG.map (m := 3) ((Sring (O := O) u).val : Sring (O := O) u →+* R)) := by
    intro x y h
    apply gg_ext
    · have := congrArg (fun z => z.right) h
      simpa [GG.map_right] using this
    · ext a b
      have := congrArg (fun z => z.mat a b) h
      simpa [GG.map_mat] using this
  let vf : Γ → GG (m := 3) (R := Sring (O := O) u) := fun g => SemidirectProduct.mk (large₂ g) (u g).right
  have hv : ∀ g, GG.map ((Sring (O := O) u).val : Sring (O := O) u →+* R) (vf g) = u g := by
    intro g
    apply gg_ext
    · rw [GG.map_right]
    · ext a b
      rw [GG.map_mat]
      rfl
  let v : Γ →* GG (m := 3) (R := Sring (O := O) u) :=
    { toFun := vf
      map_one' := gmap_inj (by rw [hv, map_one, map_one])
      map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }
  have h0 : IsPtHom u ξ ((GG.map (ξ : Sring (O := O) u →+* K)).comp v) := by
    intro g
    constructor
    · show (GG.map _ (vf g)).right = _
      rw [GG.map_right]
    · show (GG.map _ (vf g)).mat = _
      rw [GG.map_mat]
      ext a b
      rfl
  refine ⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩
end

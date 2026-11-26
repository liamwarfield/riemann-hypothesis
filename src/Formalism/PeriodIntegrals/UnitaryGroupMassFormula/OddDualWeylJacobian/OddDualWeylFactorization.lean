module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.TransvectionMulApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.EvalDuality
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightVectorUnique

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacobiMinorIdentity
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Jac

theorem block {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A B : Matrix (m ⊕ n) (m ⊕ n) R) (d : R)
    (h : B * A = d • (1 : Matrix (m ⊕ n) (m ⊕ n) R)) :
    B.toBlocks₂₂.det * A.det = d ^ Fintype.card n * A.toBlocks₁₁.det := by
  have hX : (fromBlocks (1 : Matrix m m R) 0 B.toBlocks₂₁ B.toBlocks₂₂) * A =
      fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ 0 (d • (1 : Matrix n n R)) := by
    ext i j
    have hij := congrFun (congrFun h i) j
    rcases i with i | i <;> rcases j with j | j <;>
      first
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]; done)
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂] at hij ⊢; exact hij)
  have hdet := congrArg Matrix.det hX
  simp only [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_smul, one_mul,
    mul_one] at hdet
  linear_combination hdet

theorem det_sub {R : Type*} [CommRing R] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eI eJ : ι ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) :
    (A.submatrix eI eJ).det = ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det := by
  have h1 : A.submatrix eI eJ = (A.submatrix eI eI).submatrix id (eJ.trans eI.symm) := by
    ext i j
    simp
  rw [h1]
  rw [det_permute', det_submatrix_equiv_self]

theorem sign_sq {R : Type*} [CommRing R] (u : ℤˣ) : ((u : ℤ) : R) * ((u : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

private theorem mapMatrix_eval_generic_eq {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : Fin k × Fin k => A p.1 p.2).mapMatrix
      (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)) = A := by
  ext i j
  simp

private theorem det_generic_int_ne_zero (k : ℕ) :
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)).det ≠ 0 := by
  intro h
  have h1 := congrArg
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ)
      fun p : Fin k × Fin k => (1 : Matrix (Fin k) (Fin k) ℤ) p.1 p.2) h
  rw [RingHom.map_det, mapMatrix_eval_generic_eq (1 : Matrix (Fin k) (Fin k) ℤ), det_one, map_zero] at h1
  exact one_ne_zero h1

private theorem det_toBlocks22_adjugate_submatrix_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {k : ℕ} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty n]
    (eI eJ : m ⊕ n ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) (hA : A.det ≠ 0) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  have hBA : (adjugate A).submatrix eJ eI * A.submatrix eI eJ =
      A.det • (1 : Matrix (m ⊕ n) (m ⊕ n) R) := by
    rw [submatrix_mul_equiv, adjugate_mul]
    ext i j
    simp [Matrix.one_apply]
  have key := block (A.submatrix eI eJ) ((adjugate A).submatrix eJ eI) A.det hBA
  rw [det_sub] at key
  have hs2 := sign_sq (R := R) (Equiv.Perm.sign (eJ.trans eI.symm))
  have hpow : A.det ^ Fintype.card n = A.det * A.det ^ (Fintype.card n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fintype.card_pos (α := n))]
  have h2 : A.det * (((adjugate A).submatrix eJ eI).toBlocks₂₂.det *
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R)) =
      A.det * (A.det ^ (Fintype.card n - 1) * (A.submatrix eI eJ).toBlocks₁₁.det) := by
    linear_combination key + (A.submatrix eI eJ).toBlocks₁₁.det * hpow
  have h3 := mul_left_cancel₀ hA h2
  linear_combination ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * h3 -
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det * hs2

theorem jacobi {R : Type*} [CommRing R] {k : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty n] (eI eJ : m ⊕ n ≃ Fin k)
    (A : Matrix (Fin k) (Fin k) R) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  obtain ⟨G, hG0, φ, hφG⟩ : ∃ G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) ℤ),
      G.det ≠ 0 ∧ ∃ φ : MvPolynomial (Fin k × Fin k) ℤ →+* R, φ.mapMatrix G = A :=
    ⟨_, det_generic_int_ne_zero k, _, mapMatrix_eval_generic_eq A⟩
  have hcore := det_toBlocks22_adjugate_submatrix_of_det_ne_zero eI eJ G hG0
  have hadj : φ.mapMatrix (adjugate G) = adjugate A := by
    rw [RingHom.map_adjugate, hφG]
  have e1 : φ.mapMatrix (((adjugate G).submatrix eJ eI).toBlocks₂₂) =
      ((adjugate A).submatrix eJ eI).toBlocks₂₂ := by
    ext i j
    exact congrFun (congrFun hadj (eJ (Sum.inr i))) (eI (Sum.inr j))
  have e2 : φ.mapMatrix ((G.submatrix eI eJ).toBlocks₁₁) = (A.submatrix eI eJ).toBlocks₁₁ := by
    ext i j
    exact congrFun (congrFun hφG (eI (Sum.inl i))) (eJ (Sum.inl j))
  have h := congrArg φ hcore
  simp only [map_mul, map_pow, map_intCast, RingHom.map_det, hφG, e1, e2] at h
  exact h

end PI.OddDualWeyl.Jac

namespace PI.OddDualWeyl.Jac

def mkE {a b k : ℕ} (f : Fin a → Fin k) (g : Fin b → Fin k) (h : a + b = k)
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ x y, f x ≠ g y) :
    Fin a ⊕ Fin b ≃ Fin k :=
  Equiv.ofBijective (Sum.elim f g) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hf.sumElim hg hfg, by simp [h]⟩)

def eR (k s : ℕ) (hs : s + 1 ≤ k) : Fin (k - 1 - s) ⊕ Fin (s + 1) ≃ Fin k :=
  mkE (a := k - 1 - s) (b := s + 1) (fun x => Fin.castLE (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)) x) (fun y => Fin.rev (Fin.castLE hs y)) (by omega)
    (Fin.castLE_injective _) (Fin.rev_injective.comp (Fin.castLE_injective _))
    (by
      intro x y h
      have h1 := congrArg Fin.val h
      have := x.isLt; have := y.isLt
      simp [Fin.val_rev] at h1; omega)

theorem dualSub_pMinor (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ)
    (hs : s ≤ k) :
    dualSub R k (pMinor R σ s hs) =
      (Matrix.of fun p q : Fin s =>
        adjugate (genM R k) (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
  rw [PI.OddDualWeyl.dualSub, PI.OddDualWeyl.pMinor, AlgHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun p q => by simp [PI.OddDualWeyl.dualM])

theorem sign_pm (R : Type*) [CommRing R] (u : ℤˣ) :
    ((u : ℤ) : R) = 1 ∨ ((u : ℤ) : R) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

end PI.OddDualWeyl.Jac

namespace PI.OddDualWeyl

open Jac in
theorem jacobiMinorReverse : JacRev := by
  unfold JacRev
  intro R _ k s hs
  refine ⟨((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R),
    PI.OddDualWeyl.Jac.sign_pm R _, ?_⟩
  calc dualSub R k (pMinor R Fin.revPerm (s + 1) hs)
      = (Matrix.of fun p q : Fin (s + 1) => adjugate (genM R k) (Fin.rev (Fin.castLE hs q))
          ((Fin.revPerm : Equiv.Perm (Fin k)) (Fin.castLE hs p))).det :=
        PI.OddDualWeyl.Jac.dualSub_pMinor R Fin.revPerm (s + 1) hs
    _ = (((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂)ᵀ.det :=
        congrArg Matrix.det (Matrix.ext fun p q => rfl)
    _ = ((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂.det :=
        det_transpose _
    _ = ((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) :
          MvPolynomial (Fin k × Fin k) R) * (genM R k).det ^ (Fintype.card (Fin (s + 1)) - 1) *
          ((genM R k).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₁₁.det :=
        PI.OddDualWeyl.Jac.jacobi (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs) (genM R k)
    _ = C (((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R)) *
          (genM R k).det ^ s * pMinor R 1 (k - 1 - s) (by omega) := by
        rw [map_intCast, Fintype.card_fin, Nat.add_sub_cancel, pMinor]
        all_goals rfl

end PI.OddDualWeyl
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.RevColOneTranspose
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

section Lin

variable {R : Type} [CommRing R] {k M : ℕ}

theorem rel_add {f g f' g' : MvPolynomial (Fin k × Fin k) R} (h1 : Rel R k M f f') (h2 : Rel R k M g g') :
    Rel R k M (f + g) (f' + g') := by
  unfold Rel at *
  rw [map_add (f := _), h1, h2, mul_add]

theorem rel_smul {f f' : MvPolynomial (Fin k × Fin k) R} (c : R) (h : Rel R k M f f') :
    Rel R k M (c • f) (c • f') := by
  unfold Rel at *
  rw [map_smul, h, mul_smul_comm]

theorem rel_zero : Rel R k M (0 : MvPolynomial (Fin k × Fin k) R) 0 := by
  unfold Rel
  simp

theorem rel_natMul {f f' : MvPolynomial (Fin k × Fin k) R} (n : ℕ) (h : Rel R k M f f') :
    Rel R k M ((n : MvPolynomial (Fin k × Fin k) R) * f) ((n : MvPolynomial (Fin k × Fin k) R) * f') := by
  unfold Rel at *
  rw [map_mul, map_natCast, h]
  ring

theorem rowDiv_add (a b : Fin k) (j : ℕ) (f g : MvPolynomial (Fin k × Fin k) R) :
    rowDiv R a b j (f + g) = rowDiv R a b j f + rowDiv R a b j g := by
  simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]

theorem rowDiv_smul (a b : Fin k) (j : ℕ) (c : R) (f : MvPolynomial (Fin k × Fin k) R) :
    rowDiv R a b j (c • f) = c • rowDiv R a b j f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

def rowDivL (a b : Fin k) (j : ℕ) : MvPolynomial (Fin k × Fin k) R →ₗ[R] MvPolynomial (Fin k × Fin k) R where
  toFun := rowDiv R a b j
  map_add' := rowDiv_add a b j
  map_smul' := rowDiv_smul a b j

theorem weyl_rowDiv {ν : Fin k → ℕ} (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R}
    (hf : f ∈ weyl R k k le_rfl ν) : rowDiv R a b j f ∈ weyl R k k le_rfl ν := by
  have key : weyl R k k le_rfl ν ≤ (weyl R k k le_rfl ν).comap (rowDivL a b j) := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩
  exact key hf

theorem applyWord_nil {ν : MvPolynomial (Fin k × Fin k) R} : applyWord R [] ν = ν := rfl

theorem applyWord_cons (x : Fin k × Fin k × ℕ) (w : List (Fin k × Fin k × ℕ)) (f : MvPolynomial (Fin k × Fin k) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl

theorem mem_of_pm {S : Submodule R (MvPolynomial (Fin k × Fin k) R)} {x : MvPolynomial (Fin k × Fin k) R}
    (u : MvPolynomial (Fin k × Fin k) R) (hu : u = 1 ∨ u = -1) (hx : x ∈ S) : u * x ∈ S := by
  rcases hu with rfl | rfl
  · rw [one_mul]; exact hx
  · rw [neg_one_mul]; exact S.neg_mem hx

end Lin

private theorem mh_applyWord_hw (hMh : MHhw) (hMd : MHdiv)
    (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (w : List (Fin k × Fin k × ℕ)) :
    MH R (applyWord R w (hw R (le_refl k) ν)) := by
  induction w with
  | nil => exact hMh R k ν
  | cons x w ih => exact hMd R k x.1 x.2.1 x.2.2 _ ih

theorem core1 (h1 : W1) (hMh : MHhw) (hMd : MHdiv) (hD : Diag) (hL : LowMem) (h4 : W4hw)
    (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ) (hl : Antitone lam) :
    ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      Rel R (m + 1) (expM lam) f f' := by
  have hCu : ∀ u : R, (u = 1 ∨ u = -1) → (C u : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) = 1 ∨
      (C u : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) = -1 := by
    intro u hu
    rcases hu with rfl | rfl
    · left; exact C_1
    · right; rw [C_neg, C_1]
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ),
      ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam)
          (applyWord R w (hw R le_rfl (nuOf lam))) f' := by
    intro w
    induction w with
    | nil =>
      obtain ⟨u, hu, hrel⟩ := h4 R m lam hl
      exact ⟨C u * low R (nuOf (lamStar lam)),
        mem_of_pm _ (hCu u hu) (hL R (m + 1) _), hrel⟩
    | cons x w ih =>
      obtain ⟨f', hf', hrel⟩ := ih
      obtain ⟨a, b, j⟩ := x
      rw [applyWord_cons]
      dsimp only
      rcases eq_or_ne a b with rfl | hab
      · obtain ⟨d, hd⟩ := mh_applyWord_hw hMh hMd R (m + 1) (nuOf lam) w a
        rw [hD R (m + 1) a j d _ hd]
        refine ⟨((d.choose j : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * f', ?_,
          (rel_natMul (h := hrel)) _⟩
        rw [← nsmul_eq_mul]
        exact nsmul_mem hf' _
      · exact ⟨(-1) ^ j * rowDiv R b a j f',
          mem_of_pm _ (neg_one_pow_eq_or _ j) (weyl_rowDiv b a j hf'),
          h1 R (m + 1) (expM lam) a b j _ f' hab hrel⟩
  intro f hf
  let S : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
    { carrier := {f | ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f'}
      add_mem' := by
        rintro f g ⟨f', hf', h⟩ ⟨g', hg', h'⟩
        exact ⟨f' + g', Submodule.add_mem _ hf' hg', (rel_add h) h'⟩
      zero_mem' := ⟨0, Submodule.zero_mem _, rel_zero⟩
      smul_mem' := by
        rintro c f ⟨f', hf', h⟩
        exact ⟨c • f', Submodule.smul_mem _ c hf', (rel_smul (h := h)) c⟩ }
  have hle : weyl R (m + 1) (m + 1) le_rfl (nuOf lam) ≤ S := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact key w
  exact hle hf

section Top

variable {K : Type} [Field K]

theorem lamStar_lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : lamStar (lamStar lam) = lam := by
  funext i
  simp [lamStar]

theorem antitone_lamStar {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (lamStar lam) := by
  intro i j hij
  simp only [lamStar]
  exact neg_le_neg (h (Fin.rev_le_rev.mpr hij))

theorem isUnit_invT {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : IsUnit ((g⁻¹)ᵀ).det := by
  rw [det_transpose]
  exact isUnit_nonsing_inv_det g hg

theorem invT_invT {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : (((g⁻¹)ᵀ)⁻¹)ᵀ = g := by
  have h1 : IsUnit (gᵀ).det := by rwa [det_transpose]
  rw [transpose_nonsing_inv g, nonsing_inv_nonsing_inv _ h1, transpose_transpose]

theorem revCol_eq {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : revCol A = A * revCol 1 := by
  ext i j
  simp [revCol, Matrix.mul_apply, Matrix.one_apply]

theorem revCol_one_mul_self {m : ℕ} : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) * revCol 1 = 1 := by
  rw [← revCol_eq]
  ext i j
  simp only [revCol, submatrix_apply]
  rw [Fin.rev_rev]
  rfl

theorem revCol_one_transpose {m : ℕ} : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))ᵀ = revCol 1 := by
  ext i j
  simp only [revCol, transpose_apply, submatrix_apply, id_eq, Matrix.one_apply]
  have h : (j = i.rev) ↔ (i = j.rev) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  by_cases hij : j = i.rev
  · rw [if_pos hij, if_pos (h.mp hij)]
  · have h' : i ≠ j.rev := fun hh => hij (h.mpr hh)
    rw [if_neg hij, if_neg h']

theorem isUnit_revInv {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    IsUnit (revCol (z⁻¹)ᵀ).det := by
  have hP : IsUnit (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det := by
    have h : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det *
        (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det = 1 := by
      rw [← det_mul, revCol_one_mul_self, det_one]
    exact ⟨⟨_, _, h, h⟩, rfl⟩
  rw [revCol_eq, det_mul]
  exact (isUnit_invT hz).mul hP

theorem revInv_revInv {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    revCol ((revCol (z⁻¹)ᵀ)⁻¹)ᵀ = z := by
  have hP : revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * revCol 1 = 1 :=
    revCol_one_mul_self
  have hPinv : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ = revCol 1 :=
    inv_eq_left_inv hP
  rw [revCol_eq ((z⁻¹)ᵀ), Matrix.mul_inv_rev, hPinv, transpose_mul, invT_invT hz,
    revCol_one_transpose, revCol_eq (z * revCol 1), mul_assoc, hP, mul_one]

theorem sgn_zpow_pm (hS : SgnPM) (m : ℕ) (n : ℤ) : sgnK K m ^ n = 1 ∨ sgnK K m ^ n = -1 := by
  rcases hS K m with h | h
  · left
    rw [h, _root_.one_zpow]
  · rw [h]
    rcases Int.even_or_odd n with he | ho
    · left
      exact he.neg_one_zpow
    · right
      exact ho.neg_one_zpow

private theorem eq_of_rel_of_isHomogeneous_of_uniq (hU : Uniq) {m M D : ℕ}
    {F F₁ F₂ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K}
    (h₁ : Rel K (m + 1) M F F₁) (h₂ : Rel K (m + 1) M F F₂)
    (d₁ : IsHomogeneous F₁ D) (d₂ : IsHomogeneous F₂ D) : F₁ = F₂ := by
  unfold Rel at h₁ h₂
  have hd : IsHomogeneous (F₁ - F₂) D := by
    rw [← mem_homogeneousSubmodule] at d₁ d₂ ⊢
    exact Submodule.sub_mem _ d₁ d₂
  have h0 : dualSub K (m + 1) (F₁ - F₂) = 0 := by
    rw [map_sub, h₁, h₂, sub_self]
  exact sub_eq_zero.mp (hU K (m + 1) D (F₁ - F₂) hd h0)

theorem dir1 (hC : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    ∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
  intro F hF
  by_cases hl : Antitone lam
  swap
  · unfold Dl0 at hF
    rw [if_neg hl, Submodule.mem_bot] at hF
    subst hF
    exact ⟨0, Submodule.zero_mem _, fun z _ => by simp⟩
  have hl' := antitone_lamStar hl
  unfold Dl0 at hF
  rw [if_pos hl] at hF
  simp only [Submodule.mem_iInf] at hF
  have hbal := hB m lam hl
  have hhom : ∀ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      IsHomogeneous f' (degW (nuOf (lamStar lam))) :=
    fun f' hf' => hH O (m + 1) _ f' hf'
  obtain ⟨F', -, hrel, hF'hom⟩ := hG O K m lam g hg hbal hhom (hC O m lam hl) F (hF g ⟨hg, rfl⟩)
  have hF'lat : F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ) := by
    unfold Dl0
    rw [if_pos hl']
    simp only [Submodule.mem_iInf]
    rintro g' ⟨hg', hspan⟩
    have hh : IsUnit ((g'⁻¹)ᵀ).det := isUnit_invT hg'
    have hspan' : colSpan O g = colSpan O (g'⁻¹)ᵀ := by
      have := hDB O K m (g⁻¹)ᵀ g' (isUnit_invT hg) hg' hspan
      rwa [invT_invT hg] at this
    obtain ⟨F'', hF''mem, hrel'', hF''hom⟩ :=
      hG O K m lam (g'⁻¹)ᵀ hh hbal hhom (hC O m lam hl) F (hF _ ⟨hh, hspan'⟩)
    rw [invT_invT hg'] at hF''mem
    rw [eq_of_rel_of_isHomogeneous_of_uniq hU hrel hrel'' hF'hom hF''hom]
    exact hF''mem
  refine ⟨C (sgnK K m ^ lamStar lam (Fin.last m)) * F', ?_,
    fun z hz => hE K m _ _ _ _ F F' hbal hrel hF'hom z hz⟩
  rcases sgn_zpow_pm (K := K) hS m (lamStar lam (Fin.last m)) with h | h
  · rw [h, C_1, one_mul]
    exact hF'lat
  · rw [h, C_neg, C_1, neg_one_mul]
    exact Submodule.neg_mem _ hF'lat

theorem oddFact_of (hC1 : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam := by
  intro g hg
  refine ⟨dir1 hC1 hH hB hE hU hDB hS hG O m lam g hg, ?_⟩
  intro F' hF'
  have hfw := dir1 hC1 hH hB hE hU hDB hS hG O m (lamStar lam) ((g⁻¹)ᵀ)
    (isUnit_invT hg)
  rw [lamStar_lamStar, invT_invT hg] at hfw
  obtain ⟨F, hF, hid⟩ := hfw F' hF'
  refine ⟨F, hF, fun z hz => ?_⟩
  have := hid (revCol (z⁻¹)ᵀ) (isUnit_revInv hz)
  rw [revInv_revInv hz] at this
  exact this.symm

theorem oddDualWeyl_of (h1 : W1) (hMh : MHhw) (hMd : MHdiv) (hD : Diag) (hL : LowMem) (h4 : W4hw)
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam := oddFact_of
    (fun R _ m lam hl => core1 h1 hMh hMd hD hL h4 R m lam hl)
    hH hB hE hU hDB hS hG O m lam

end Top

end PI.OddDualWeyl
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightMultiplicity
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace Hom

variable {R : Type} [CommRing R] {k : ℕ}

def Good (wt : Fin k × Fin k → ℤ) (δ d : ℤ) (p : Polynomial (MvPolynomial (Fin k × Fin k) R)) :
    Prop :=
  ∀ i : ℕ, IsWeightedHomogeneous wt (p.coeff i) (d + i * δ)

variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}

theorem good_congr {d e : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (h : d = e)
    (hp : Good wt δ d p) : Good wt δ e p := by
  subst h
  exact hp

theorem good_zero (d : ℤ) : Good (R := R) wt δ d 0 := by
  intro i e he
  simp at he

theorem good_add {d : ℤ} {p q : Polynomial (MvPolynomial (Fin k × Fin k) R)}
    (hp : Good wt δ d p) (hq : Good wt δ d q) : Good wt δ d (p + q) := by
  intro i
  rw [Polynomial.coeff_add]
  exact (hp i).add (hq i)

theorem good_C {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R} (hc : IsWeightedHomogeneous wt c d) :
    Good wt δ d (Polynomial.C c) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simpa using hc
  · intro e he
    simp at he

theorem good_X_mul_C {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R}
    (hc : IsWeightedHomogeneous wt c (d + δ)) : Good wt δ d (Polynomial.X * Polynomial.C c) := by
  intro i
  rw [Polynomial.X_mul_C, Polynomial.coeff_C_mul_X]
  split_ifs with h
  · subst h
    simpa using hc
  · intro e he
    simp at he

theorem good_one : Good (R := R) wt δ 0 1 := by
  simpa using good_C (δ := δ) (isWeightedHomogeneous_one (R := R) (w := wt))

theorem good_mul {d e : ℤ} {p q : Polynomial (MvPolynomial (Fin k × Fin k) R)}
    (hp : Good wt δ d p) (hq : Good wt δ e q) : Good wt δ (d + e) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [mem_weightedHomogeneousSubmodule]
  have h := (hp x.1).mul (hq x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring

theorem good_pow {d : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (hp : Good wt δ d p)
    (m : ℕ) : Good wt δ (m * d) (p ^ m) := by
  induction m with
  | zero => simpa using (good_one (R := R) (wt := wt) (δ := δ))
  | succ m ih =>
    rw [pow_succ]
    exact good_congr (by push_cast; ring) (good_mul ih hp)

theorem good_prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial (Fin k × Fin k) R))
    (d : ι → ℤ) (h : ∀ i ∈ s, Good wt δ (d i) (p i)) : Good wt δ (∑ i ∈ s, d i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on
  · simpa using (good_one (R := R) (wt := wt) (δ := δ))
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact good_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem good_rowGen_X (a b : Fin k) (hδ : ∀ s, wt (a, s) = wt (b, s) + δ) (v : Fin k × Fin k) :
    Good wt δ (wt v) (rowGen R a b (X v)) := by
  simp only [rowGen, aeval_X]
  refine good_add (good_C (isWeightedHomogeneous_X R wt v)) ?_
  split_ifs with h
  · apply good_X_mul_C
    obtain ⟨v1, v2⟩ := v
    simp only at h ⊢
    subst h
    rw [← hδ]
    exact isWeightedHomogeneous_X R wt (a, v2)
  · exact good_zero _

theorem good_rowGen (a b : Fin k) (hδ : ∀ s, wt (a, s) = wt (b, s) + δ) {d : ℤ}
    {f : MvPolynomial (Fin k × Fin k) R} (hf : IsWeightedHomogeneous wt f d) :
    Good wt δ d (rowGen R a b f) := by
  have key : ∀ m ∈ f.support, Good wt δ d (rowGen R a b (monomial m (AddMonoidAlgebra.coeff f m))) := by
    intro m hm
    have hw : Finsupp.weight wt m = d := hf (mem_support_iff.mp hm)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have h1 : Good wt δ 0 (rowGen R a b (C (AddMonoidAlgebra.coeff f m))) := by
      have hC : rowGen R a b (C (AddMonoidAlgebra.coeff f m) : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C (AddMonoidAlgebra.coeff f m) : MvPolynomial (Fin k × Fin k) R) := by
        simp [rowGen, Polynomial.algebraMap_apply]
      rw [hC]
      exact good_C (isWeightedHomogeneous_C wt _)
    have h2 := good_prod m.support (fun i => rowGen R a b (X i ^ m i)) (fun i => (m i : ℤ) * wt i)
      (fun i _ => by rw [map_pow]; exact good_pow (good_rowGen_X a b hδ i) (m i))
    refine good_congr ?_ (good_mul h1 h2)
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    simp [nsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  intro i
  rw [Polynomial.finsetSum_coeff, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact key m hm i

theorem weight_cast (w : Fin k × Fin k → ℕ) (α : Fin k × Fin k →₀ ℕ) :
    Finsupp.weight (fun v => (w v : ℤ)) α = (Finsupp.weight w α : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]

theorem toZ {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {d : ℕ}
    (h : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous (fun v => (w v : ℤ)) f (d : ℤ) := by
  intro α hα
  rw [weight_cast, h hα]

theorem ofZ {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {m : ℤ}
    (h : IsWeightedHomogeneous (fun v => (w v : ℤ)) f m) : IsWeightedHomogeneous w f m.toNat := by
  intro α hα
  have := h hα
  rw [weight_cast] at this
  omega

theorem det_isWH {M' : Type*} [AddCommMonoid M'] {w : Fin k × Fin k → M'} {s : ℕ}
    (N : Matrix (Fin s) (Fin s) (MvPolynomial (Fin k × Fin k) R)) (r : Fin s → M')
    (h : ∀ p q, IsWeightedHomogeneous w (N p q) (r p)) :
    IsWeightedHomogeneous w N.det (∑ p, r p) := by
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hprod : (∏ i, N (σ i) i) ∈ weightedHomogeneousSubmodule R w (∑ p, r p) := by
    rw [mem_weightedHomogeneousSubmodule]
    have := IsWeightedHomogeneous.prod Finset.univ (fun i => N (σ i) i) (fun i => r (σ i))
      (fun i _ => h (σ i) i)
    rwa [Equiv.sum_comp σ r] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rw [Units.neg_smul, one_smul]
    exact Submodule.neg_mem _ hprod

theorem lpMinor_row (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) (c : Fin k) :
    IsWeightedHomogeneous (rowW c) (lpMinor R s hr hn)
      (∑ p : Fin s, if Fin.castLE hr p = c then 1 else 0) := by
  unfold lpMinor
  apply det_isWH
  intro p q
  simp only [Matrix.of_apply]
  convert isWeightedHomogeneous_X R (rowW c) (Fin.castLE hr p, Fin.castLE hn q) using 1
  simp [rowW]

theorem lpMinor_tot (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) :
    IsWeightedHomogeneous (1 : Fin k × Fin k → ℕ) (lpMinor R s hr hn) s := by
  have := det_isWH (w := (1 : Fin k × Fin k → ℕ))
    (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin k × Fin k) R))
    (fun _ => 1)
    (fun p q => by simpa using isWeightedHomogeneous_X R (1 : Fin k × Fin k → ℕ) (Fin.castLE hr p, Fin.castLE hn q))
  simpa [lpMinor] using this

theorem rowDiv_tot (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (rowDiv R a b j f) n := by
  have h := good_rowGen (wt := fun v => (((1 : Fin k × Fin k → ℕ) v : ℕ) : ℤ)) (δ := 0) a b
    (fun s => by simp) (toZ (w := 1) hf) j
  have h2 := ofZ (w := 1) h
  have h3 : ((n : ℤ) + (j : ℤ) * 0).toNat = n := by simp
  rw [h3] at h2
  exact h2

theorem applyWord_tot (wd : List (Fin k × Fin k × ℕ)) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (applyWord R wd f) n := by
  induction wd with
  | nil => exact hf
  | cons x w ih => exact rowDiv_tot x.1 x.2.1 x.2.2 ih

theorem hw_tot (ν : Fin k → ℕ) : IsHomogeneous (hw R (le_refl k) ν) (degW ν) := by
  unfold hw degW
  apply IsHomogeneous.prod
  intro s _
  have h0 : IsHomogeneous (lpMinor R (s.val + 1) (by omega) (by omega) : MvPolynomial (Fin k × Fin k) R)
      (s.val + 1) := lpMinor_tot _ _ _
  convert h0.pow (ν s - nuNext ν s) using 1 <;> exact Nat.mul_comm _ _

theorem rowGen_diag_X (a : Fin k) (v : Fin k × Fin k) :
    rowGen R a a (X v) = (1 + Polynomial.X) ^ (rowW a v) * Polynomial.C (X v) := by
  simp only [rowGen, aeval_X, rowW]
  split_ifs with h
  · obtain ⟨v1, v2⟩ := v
    simp only at h ⊢
    subst h
    ring
  · simp

theorem rowGen_diag (a : Fin k) {d : ℕ} {f : MvPolynomial (Fin k × Fin k) R}
    (hf : IsWeightedHomogeneous (rowW a) f d) :
    rowGen R a a f = (1 + Polynomial.X) ^ d * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (rowW a) m = d := hf (mem_support_iff.mp hm)
  have hC : rowGen R a a (C (AddMonoidAlgebra.coeff f m) : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C (AddMonoidAlgebra.coeff f m) : MvPolynomial (Fin k × Fin k) R) := by
    simp [rowGen, Polynomial.algebraMap_apply]
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, map_mul, map_prod, hC]
  simp_rw [map_pow, rowGen_diag_X, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, mul_comm (m _) (rowW a _)]
  ring

end Hom

open Hom

theorem highest_weight_multiplicity : MHhw := by
  intro R _ k ν a
  unfold hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ (fun s _ => (lpMinor_row (R := R) (s.val + 1) _ _ a).pow _)⟩

theorem highest_weight_divisibility : MHdiv := by
  intro R _ k a b j f hf c
  obtain ⟨d, hd⟩ := hf c
  refine ⟨_, ofZ (good_rowGen (wt := fun v => ((rowW c v : ℕ) : ℤ))
    (δ := ((if a = c then 1 else 0 : ℕ) : ℤ) - ((if b = c then 1 else 0 : ℕ) : ℤ)) a b ?_ (toZ hd) j)⟩
  intro s
  simp only [rowW]
  split_ifs <;> simp

theorem hermitianDiagonalization : Diag := by
  intro R _ k a j d f hf
  unfold rowDiv
  rw [rowGen_diag a hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow]

theorem weight_homomorphism : HomW := by
  intro R _ k ν f hf
  have hle : weyl R k k (le_refl k) ν ≤ homogeneousSubmodule (Fin k × Fin k) R (degW ν) := by
    rw [weyl, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    exact applyWord_tot w (hw_tot ν)
  have := hle hf
  rwa [mem_homogeneousSubmodule] at this

end PI.OddDualWeyl
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.DegreeBalance
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace MiscB

theorem abel (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) :
    ∀ n, ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← abel f hf n, add_assoc, ← Nat.mul_add,
      Nat.sub_add_cancel (hf n)]
    ring

def ext0 {k : ℕ} (ν : Fin k → ℕ) (t : ℕ) : ℕ := if h : t < k then ν ⟨t, h⟩ else 0

theorem degW_eq {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) : degW ν = ∑ s, ν s := by
  have hf : ∀ s, ext0 ν (s + 1) ≤ ext0 ν s := by
    intro s
    unfold ext0
    split_ifs with h1 h2
    · exact hν (Fin.mk_le_mk.2 (Nat.le_succ s))
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := abel (ext0 ν) hf k
  have hk : ext0 ν k = 0 := by
    unfold ext0
    simp
  rw [hk, mul_zero, add_zero] at h
  have e1 : ∑ s : Fin k, (s.val + 1) * (ν s - nuNext ν s) =
      ∑ s ∈ Finset.range k, (s + 1) * (ext0 ν s - ext0 ν (s + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => (s + 1) * (ext0 ν s - ext0 ν (s + 1))) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
    rfl
  have e2 : ∑ s : Fin k, ν s = ∑ s ∈ Finset.range k, ext0 ν s := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => ext0 ν s) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
  unfold degW
  rw [e1, e2, h]

variable {m : ℕ} {lam : Fin (m + 1) → ℤ}

theorem nu_cast (hl : Antitone lam) (t : Fin (m + 1)) : (nuOf lam t : ℤ) = lam t - lam (Fin.last m) := by
  unfold nuOf
  exact Int.toNat_of_nonneg (sub_nonneg.2 (hl (Fin.le_last t)))

theorem nu_anti (hl : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have ha := nu_cast hl a
  have hb := nu_cast hl b
  have h := hl hab
  omega

theorem sum_nu_le (hl : Antitone lam) : ∑ t, nuOf lam t ≤ m * nuOf lam 0 := by
  rw [Fin.sum_univ_castSucc]
  have hl0 : nuOf lam (Fin.last m) = 0 := by
    unfold nuOf
    simp
  rw [hl0, add_zero]
  calc ∑ t : Fin m, nuOf lam t.castSucc ≤ ∑ _t : Fin m, nuOf lam 0 :=
        Finset.sum_le_sum fun t _ => nu_anti hl (Fin.zero_le _)
    _ = m * nuOf lam 0 := by simp

end MiscB

theorem degreeBalance : Bk := by
  intro m lam hl
  have hs : Antitone (lamStar lam) := fun i j hij => by
    unfold lamStar
    exact neg_le_neg (hl (Fin.rev_le_rev.2 hij))
  unfold expM
  rw [MiscB.degW_eq _ (MiscB.nu_anti hs), Nat.cast_sub (MiscB.sum_nu_le hl)]
  push_cast
  simp only [MiscB.nu_cast hs, MiscB.nu_cast hl]
  have hr : ∑ t : Fin (m + 1), (lamStar lam t - lamStar lam (Fin.last m)) =
      ∑ t : Fin (m + 1), (lam 0 - lam t) := by
    unfold lamStar
    rw [Fin.rev_last, ← Equiv.sum_comp Fin.revPerm (fun t => lam 0 - lam t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.revPerm_apply]
    ring
  rw [hr]
  unfold lamStar
  rw [Fin.rev_last]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end PI.OddDualWeyl
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.ExistsEqMulOfColumnSpanLe
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace Misc

theorem sgn (K : Type) [Field K] (m : ℕ) : sgnK K m = 1 ∨ sgnK K m = -1 := by
  have h : PI.OddDualWeyl.sgnK K m =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : K) := by
    unfold PI.OddDualWeyl.sgnK PI.OddDualWeyl.revCol
    have hr : (Fin.rev : Fin (m + 1) → Fin (m + 1)) = ⇑(Fin.revPerm : Equiv.Perm (Fin (m + 1))) := rfl
    rw [hr, Matrix.det_permute', Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with hs | hs <;>
    simp [h, hs]

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem exists_eq_mul_of_columnSpan_le {n : ℕ} (g g' : Matrix (Fin n) (Fin n) K) (h : colSpan O g ≤ colSpan O g') :
    ∃ v : Matrix (Fin n) (Fin n) O, g = g' * v.map (algebraMap O K) := by
  have h2 : Submodule.span O (Set.range fun c : Fin n => fun i => g i c) ≤
      Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) := h
  have hc : ∀ c : Fin n, ∃ a : Fin n → O, ∑ j, a j • (fun i => g' i j) = fun i => g i c := by
    intro c
    have hm : (fun i => g i c) ∈ Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) :=
      h2 (Submodule.subset_span ⟨c, rfl⟩)
    exact (Submodule.mem_span_range_iff_exists_fun (R := O)).1 hm
  choose a ha using hc
  refine ⟨Matrix.of fun j c => a c j, ?_⟩
  ext i c
  have hi := congrFun (ha c) i
  rw [← hi, Finset.sum_apply]
  simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem colSpan_mul_le {n : ℕ} (h' : Matrix (Fin n) (Fin n) K) (v : Matrix (Fin n) (Fin n) O) :
    colSpan O (h' * v.map (algebraMap O K)) ≤ colSpan O h' := by
  unfold PI.OddDualWeyl.colSpan
  rw [Submodule.span_le]
  rintro x ⟨c, rfl⟩
  have hv : (fun i => (h' * v.map (algebraMap O K)) i c) = ∑ j, v j c • fun i => h' i j := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  dsimp only
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem invT_eq {n : ℕ} {g g' : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) (hg' : IsUnit g'.det)
    (u : Matrix (Fin n) (Fin n) O) (hu : g' = g * u.map (algebraMap O K)) :
    (g⁻¹)ᵀ = (g'⁻¹)ᵀ * (uᵀ).map (algebraMap O K) := by
  have hU : g⁻¹ * g' = u.map (algebraMap O K) := by
    rw [hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hinv : g⁻¹ = u.map (algebraMap O K) * g'⁻¹ := by
    rw [← hU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg', Matrix.mul_one]
  rw [hinv, Matrix.transpose_mul, Matrix.transpose_map]

end Misc

theorem reverseSignUnit : SgnPM := by
  intro K _ m
  exact PI.OddDualWeyl.Misc.sgn K m

theorem columnSpanDual : DualB := by
  intro O K _ _ _ m g g' hg hg' h
  obtain ⟨v, hv⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g' g h.ge
  obtain ⟨w, hw⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g g' h.le
  apply le_antisymm
  · rw [PI.OddDualWeyl.Misc.invT_eq hg hg' v hv]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _
  · rw [PI.OddDualWeyl.Misc.invT_eq hg' hg w hw]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _

end PI.OddDualWeyl
end
end

namespace PI.OddDualWeyl

theorem odd_dual_weyl_factorization {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ)
    (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam :=
  oddDualWeyl_of rowOpIntertwining highest_weight_multiplicity highest_weight_divisibility hermitianDiagonalization lowestWeightMem (highestWeightDual_of jacobiMinorReverse) weight_homomorphism degreeBalance
    evalDuality highest_weight_vector_unique columnSpanDual reverseSignUnit twistedWeylStep O m lam

end PI.OddDualWeyl

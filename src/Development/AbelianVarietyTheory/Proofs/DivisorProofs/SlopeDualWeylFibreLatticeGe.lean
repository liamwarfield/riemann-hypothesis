module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSlopeSqLocalMatricesEqDeterminants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTvalNeZero
noncomputable section

namespace GlobalTheory.DefPt.Model

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial GlobalTheory.DefPt
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

theorem rhoMat_one (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : rhoMat la (1 : Matrix _ _ K) = 1 := by
  simp [rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]

theorem rhoMat_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la (g * h) = rhoMat la h * rhoMat la g := by
  simp [rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]

theorem rhoMat_scalar (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (t : K) :
    rhoMat la (t • (1 : Matrix _ _ K)) = t ^ size la • 1 := by
  have : rho la K (t • 1) = t ^ size la • LinearMap.id := LinearMap.ext fun f => rho_scalar t f
  simp [rhoMat, this]

end Tensor

end GlobalTheory.DefPt.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylGramDeterminantLeDimPowDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMinorLeOneAndHadamardColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMinorLeOneAndHadamardColumns
open scoped Matrix

namespace GlobalTheory.UnitaryMinor

theorem sum_norm_sq_col {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, ‖u.1 i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 u.2) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ i, ‖u.1 i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast h2

theorem norm_det_submatrix_le_one (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (I J : Fin s → Fin n) : ‖(u.1.submatrix I J).det‖ ≤ 1 := by
  by_cases hI : Function.Injective I
  · have h : ‖(u.1.submatrix I J).det‖ ^ 2 ≤ 1 := by
      refine (GlobalTheory.Hadamard.norm_det_sq_le_prod_col (u.1.submatrix I J)).trans ?_
      refine Finset.prod_le_one₀ (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
        fun j _ => ?_
      rw [← sum_norm_sq_col u (J j)]
      simp only [Matrix.submatrix_apply]
      rw [← Finset.sum_image (s := Finset.univ) (g := I) (f := fun i => ‖u.1 i (J j)‖ ^ 2)
        (fun a _ b _ h => hI h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => by positivity
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hI
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hab])]
    simp

theorem unitary_minor_and_hadamard :
    (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n),
      ‖(u.1.submatrix I J).det‖ ≤ 1) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 :=
  ⟨norm_det_submatrix_le_one, fun _ _ _ M => GlobalTheory.Hadamard.norm_det_sq_le_prod_col M⟩

end GlobalTheory.UnitaryMinor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMinorLeOneAndHadamardColumnsStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns : (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n), ‖(u.1.submatrix I J).det‖ ≤ 1) ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ), ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
  first | exact @GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | exact GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | (intros; apply GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylGramDeterminantLeDimPowDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.OnMatGram

theorem norm_evalAt_intVec_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) (g : UN n) :
    ‖evalAt g.1 (map (Int.castRingHom ℂ) (intVec la j))‖ ≤ 1 := by
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.2 j
  have hv : intVec la j = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
  rw [hv, Formalism.GradedWeylDivisibility.ldlat_map_bidet]
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [Formalism.GradedWeylDivisibility.algHom_det_of]
  have h : (Matrix.of fun p q : Fin (sz k) => evalAt g.1 (X (I k p, Fin.castLE (hsz k) q) : Pol n ℂ)) =
      g.1.submatrix (I k) (Fin.castLE (hsz k)) := by
    ext p q
    simp
  rw [h]
  exact GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.1 n (sz k) g (I k) (Fin.castLE (hsz k))

theorem normSq_basis_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    normSq la (basis la ℂ j).1 ≤ dim la := by
  refine normSq_le_dim fun g => ?_
  rw [coe_basis]
  exact norm_evalAt_intVec_le la j g

theorem sum_norm_sq_onMat {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    ∑ i, ‖onMat la i j‖ ^ 2 = normSq la (basis la ℂ j).1 := by
  rw [← norm_toSpace_sq, ← (onBasis la).repr.norm_map, EuclideanSpace.norm_sq_eq]
  rfl

theorem det_onMat_ne_zero {n : ℕ} (la : Fin n → ℕ) : (onMat la).det ≠ 0 := by
  let c : Module.Basis (Idx la) ℂ (Space la) := (basis la ℂ).map (toSpace la)
  have hc : onMat la = (onBasis la).toBasis.toMatrix c := by
    ext i j
    simp [onMat, c, Module.Basis.toMatrix_apply]
  rw [hc]
  exact (Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip c _)).ne_zero

end GlobalTheory.OnMatGram

namespace GlobalTheory.OnMatGram

theorem norm_det_onMat_sq_le : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  intro n la _
  refine ⟨det_onMat_ne_zero la, ?_⟩
  refine (GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.2 (Idx la) (onMat la)).trans ?_
  calc ∏ j, ∑ i, ‖onMat la i j‖ ^ 2 ≤ ∏ _j : Idx la, (dim la : ℝ) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun j _ => (sum_norm_sq_onMat la j).trans_le (normSq_basis_le la j)
    _ = (dim la : ℝ) ^ dim la := by rw [Finset.prod_const, Finset.card_univ, ← dim_eq_card]

end GlobalTheory.OnMatGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylGramDeterminantLeDimPowDimStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  first | exact @GlobalTheory.OnMatGram.norm_det_onMat_sq_le | exact GlobalTheory.OnMatGram.norm_det_onMat_sq_le | (intros; apply GlobalTheory.OnMatGram.norm_det_onMat_sq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatCharPowEqDetPow
noncomputable section

namespace GlobalTheory.DefPt

open Matrix

section Char

variable {K : Type} [Field K] {n : ℕ} (χ : Matrix (Fin n) (Fin n) K →* K)

theorem matChar_submatrix (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) K) :
    χ (M.submatrix σ σ) = χ M := by
  have h1 : ∀ N : Matrix (Fin n) (Fin n) K,
      σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ := by
    intro N
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    rfl
  have h2 := congrArg χ (h1 1)
  rw [submatrix_one_equiv, Matrix.mul_one, map_mul, map_one] at h2
  rw [← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]

theorem matChar_transvection [CharZero K] {i j : Fin n} (hij : i ≠ j) (c : K) :
    χ (transvection i j c) = 1 := by
  set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)
  set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have hD : χ D ≠ 0 := fun h => by
    have := congrArg χ hDD
    rw [map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hT : χ (transvection i j c) ≠ 0 := fun h => by
    have := congrArg χ (transvection_mul_transvection_same i j hij c (-c))
    rw [add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hcomm : D * transvection i j c = transvection i j (c + c) * D := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    have hdi : Function.update (1 : Fin n → K) i 2 i = 2 := by simp
    have hdj : Function.update (1 : Fin n → K) i 2 j = 1 := by simp [Ne.symm hij]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hij, hdi, hdj]
      simp only [and_self, ite_true]
      ring
    · have h' : ¬(i = a ∧ j = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg h', if_neg h']
      simp only [add_zero]
      by_cases hab : a = b
      · subst hab; ring
      · rw [Matrix.one_apply_ne hab]; ring
  have e := congrArg χ hcomm
  rw [map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)] at e
  have e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c) := by
    rw [mul_one]
    exact mul_right_cancel₀ hD e
  exact (mul_left_cancel₀ hT e2).symm

theorem matChar_mulSingle (k k' : Fin n) (a : K) :
    χ (diagonal (Pi.mulSingle k a)) = χ (diagonal (Pi.mulSingle k' a)) := by
  rw [← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]
  apply congrArg χ
  apply congrArg diagonal
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x = k
  · subst hx; simp
  · by_cases hx' : x = k'
    · subst hx'; rw [Equiv.swap_apply_right]; simp [hx, Ne.symm hx]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; simp [hx, hx']

theorem matChar_diagonal_pow (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m) (d : Fin n → K) :
    χ (diagonal d) ^ n = (diagonal d).det ^ m := by
  let ψ : (Fin n → K) →* K := χ.comp (diagonalRingHom (Fin n) K).toMonoidHom
  have hψ : ∀ v, ψ v = χ (diagonal v) := fun v => rfl
  have hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m := by
    intro k a
    calc χ (diagonal (Pi.mulSingle k a)) ^ n = ∏ k' : Fin n, ψ (Pi.mulSingle k' a) := by
          rw [Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]
  calc χ (diagonal d) ^ n = (∏ k, ψ (Pi.mulSingle k (d k))) ^ n := by
        rw [← map_prod, Finset.univ_prod_mulSingle, hψ]
    _ = ∏ k, d k ^ m := by
        rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun k _ => hone k (d k)
    _ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]

theorem matChar_pow_eq_det_pow [CharZero K] (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m)
    (g : Matrix (Fin n) (Fin n) K) : χ g ^ n = g.det ^ m := by
  refine diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g
    (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)
  · show χ t.toMatrix ^ n = t.toMatrix.det ^ m
    rw [show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij,
      det_transvection_of_ne _ _ t.hij]
    simp
  · show χ (A * B) ^ n = (A * B).det ^ m
    have hA' : χ A ^ n = A.det ^ m := hA
    have hB' : χ B ^ n = B.det ^ m := hB
    rw [map_mul, det_mul, mul_pow, mul_pow, hA', hB']

end Char

end GlobalTheory.DefPt

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine MvPolynomial
open scoped Matrix

def rhoDetHom {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : Matrix (Fin n) (Fin n) K →* K where
  toFun g := (GlobalTheory.DefPt.rhoMat la g).det
  map_one' := by rw [Model.rhoMat_one, Matrix.det_one]
  map_mul' g h := by rw [Model.rhoMat_mul, Matrix.det_mul, mul_comm]

theorem det_rhoMat_pow : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la →
    ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) := by
  intro K _ _ n la _ g
  have hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la) := by
    intro t
    show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _
    rw [Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]
  exact matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g

end GlobalTheory.DefPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGe
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibSlope

section Log

variable {K : Type} [Field K] {φ : K → ℝ} (hφ : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
include hφ

theorem log_one : φ 1 = 0 := by
  have := hφ 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at this
  linarith

theorem log_prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    φ (∏ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using log_one hφ
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, hφ _ _ (hf i) (Finset.prod_ne_zero_iff.2 fun j _ => hf j), ih]

theorem log_pow {x : K} (hx : x ≠ 0) (n : ℕ) : φ (x ^ n) = n * φ x := by
  have := log_prod hφ (Finset.range n) (fun _ => x) fun _ => hx
  simpa using this

theorem log_det_rhoMat [CharZero K] {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) {g : Matrix (Fin n) (Fin n) K}
    (hg : g.det ≠ 0) : (rhoMat la g).det ≠ 0 ∧
      φ (rhoMat la g).det = (dim la : ℝ) * ((size la : ℝ) / (n : ℝ) * φ g.det) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim g 1, GlobalTheory.DefPt.Model.rhoMat_one, Matrix.det_one, log_one hφ]
    simp
  · have h := det_rhoMat_pow K n la hla g
    have h0 : (rhoMat la g).det ≠ 0 := fun h0 => by
      rw [h0, zero_pow hn.ne'] at h
      exact pow_ne_zero _ hg h.symm
    refine ⟨h0, ?_⟩
    have h1 := congrArg φ h
    rw [log_pow hφ h0, log_pow hφ hg] at h1
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast at h1
    field_simp
    linarith

theorem log_det_kron {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (J t)] {c : K} (hc : c ≠ 0) (M : ∀ t, Matrix (J t) (J t) K) (hM : ∀ t, (M t).det ≠ 0)
    (r : T → ℝ) (hr : ∀ t, φ (M t).det = Fintype.card (J t) * r t) :
    (c • kron M).det ≠ 0 ∧ φ (c • kron M).det = Fintype.card (∀ t, J t) * (φ c + ∑ t, r t) := by
  have hk := (kronFamily_mul_one_det T J K M M).2.2
  have hp : ∀ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) ≠ 0 := fun t => pow_ne_zero _ (hM t)
  have h0 : (kron M).det ≠ 0 := hk ▸ Finset.prod_ne_zero_iff.2 fun t _ => hp t
  rw [Matrix.det_smul]
  refine ⟨mul_ne_zero (pow_ne_zero _ hc) h0, ?_⟩
  rw [hφ _ _ (pow_ne_zero _ hc) h0, log_pow hφ hc, hk, log_prod hφ _ _ hp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [log_pow hφ (hM t), hr, ← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ t),
    Fintype.card_pi]

end Log

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul_real (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (vAdd w (x * y) : ℝ) = vAdd w x + vAdd w y := by
  have h1 : w.valuation K x ≠ 0 := by simpa using hx
  have h2 : w.valuation K y ≠ 0 := by simpa using hy
  rw [← Int.cast_add, vAdd, vAdd, vAdd, map_mul, WithZero.log_mul h1 h2, neg_add]

theorem valuation_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K}
    (hM : IntAt w M) : w.valuation K M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun i _ => hM _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem finite_vAdd_det {ι : Type} [Fintype ι] [DecidableEq ι] {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K}
    (hA : IsAdelic A) : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
  refine hA.2.subset fun w hw h => hw ?_
  have h1 := valuation_det_le w h.1
  have h2 := valuation_det_le w h.2
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀] at h2
  have h0 : w.valuation K (A w).det ≠ 0 := by simpa using hA.1 w
  have h3 : w.valuation K (A w).det = 1 :=
    le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)
  simp [vAdd, h3]

end Val

theorem log_norm_mul (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) : Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {la : ∀ t, Fin (N t) → ℕ}

theorem vAdd_det_fibA {K : Type} [Field K] [NumberField K] (hla : ∀ t, Antitone (la t)) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) {B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K} (hB : ∀ t, (B t).det ≠ 0) :
    (vAdd w (fibA la a B).det : ℝ) =
      Fintype.card (TIdx la) * (vAdd w a + ∑ t, (size (la t) : ℝ) / (N t : ℝ) * vAdd w (B t).det) :=
  (log_det_kron (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) ha _
    (fun t => (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).1) _
    (fun t => by
      rw [← dim_eq_card]
      exact (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).2)).2

theorem log_det_fibY (hla : ∀ t, Antitone (la t)) {s : ℝ} (hs : 0 < s) {X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ}
    (hX : ∀ t, (X t).det ≠ 0) : (fibY la s X).det ≠ 0 ∧ Real.log ‖(fibY la s X).det‖ =
      Fintype.card (TIdx la) * (Real.log s + ∑ t, (Real.log ‖(onMat (la t)).det‖ / dim (la t) +
        (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)) := by
  have hρ := fun t => log_det_rhoMat (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (hla t) (hX t)
  have ho := fun t => (GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ (la t) (hla t)).1
  have h := log_det_kron (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (c := (s : ℂ))
    (Complex.ofReal_ne_zero.2 hs.ne') (fun t => onMat (la t) * rhoMat (la t) (X t))
    (fun t => by rw [Matrix.det_mul]; exact mul_ne_zero (ho t) (hρ t).1)
    (fun t => Real.log ‖(onMat (la t)).det‖ / dim (la t) + (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)
    (fun t => by
      have hd : (dim (la t) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (dim_pos (hla t)).ne'
      have h2 := (hρ t).2
      rw [← dim_eq_card, Matrix.det_mul, log_norm_mul _ _ (ho t) (hρ t).1, h2, mul_add, mul_div_cancel₀ _ hd])
  simp only [Complex.norm_real, Real.norm_of_nonneg hs.le] at h
  exact h

theorem log_det_onMat_le {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) :
    Real.log ‖(onMat la).det‖ / dim la ≤ Real.log (dim la) / 2 := by
  obtain ⟨h0, h⟩ := GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ la hla
  have hd : (0 : ℝ) < dim la := Nat.cast_pos.2 (dim_pos hla)
  have h1 := Real.log_le_log (pow_pos (norm_pos_iff.2 h0) 2) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_le_iff₀ hd]
  push_cast at h1
  linarith

theorem slope_fibre_ge : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  intro K _ _ _ T _ _ N la hla a B s X ha hfa hB hs hX hsc hXc
  have hY := fun σ => log_det_fibY hla (hs σ) (hX σ)
  refine ⟨fun σ => (hY σ).1, ?_⟩
  have hD : 0 < Fintype.card (TIdx la) := by
    rw [Fintype.card_pi]
    exact Finset.prod_pos fun t _ => dim_eq_card (la t) ▸ dim_pos (hla t)
  haveI : Nonempty (TIdx la) := Fintype.card_pos_iff.1 hD
  have hD' : (Fintype.card (TIdx la) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  have hK : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  rw [GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants K (TIdx la) _ _ (GlobalTheory.FibAdel.fibA_isAdelic K T N la a B ha hfa hB) (fun σ => (hY σ).1)
    (fun σ => Real.log_injOn_pos (norm_pos_iff.2 (hY _).1) (norm_pos_iff.2 (hY _).1) (by
      rw [(hY _).2, (hY _).2]; simp only [hsc, hXc]))]
  have hfa' : (Function.support fun w => (vAdd w (a w) : ℝ)).Finite := hfa.subset fun w hw h => hw (by
    simp only at h ⊢; rw [h, Int.cast_zero])
  have hfB := fun t => finite_vAdd_det (hB t)
  have hfin : ∑ᶠ w, (vAdd w (fibA la (a w) (B w)).det : ℝ) * lw K w = Fintype.card (TIdx la) *
      (∑ᶠ w, (vAdd w (a w) : ℝ) * lw K w +
        ∑ t, (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) := by
    have hsub : ∀ t, (Function.support fun w => (size (la t) : ℝ) / (N t : ℝ) *
        ((vAdd w (B w t).det : ℝ) * lw K w)).Finite := fun t =>
      (fin_mul (hfB t) (lw K)).subset (Function.support_mul_subset_right _ _)
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ _ (fun t _ => hsub t), ← finsum_add_distrib (fin_mul hfa' _), mul_finsum]
    · refine finsum_congr fun w => ?_
      rw [vAdd_det_fibA hla w (ha w) (fun t => (hB t).1 w), mul_assoc, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · exact (Set.finite_iUnion hsub).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (Finset.sum_eq_zero fun t _ => hn t)
  have hinf : ∑ σ, Real.log ‖(fibY la (s σ) (X σ)).det‖ = Fintype.card (TIdx la) *
      (∑ σ, Real.log (s σ) + ∑ t, (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖)) := by
    simp only [(hY _).2]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul,
      Finset.mul_sum]
  simp only [detDeg, lineDeg]
  rw [hfin, hinf]
  have key : ∀ u v : ℝ, 2 * (Fintype.card (TIdx la) * u - Fintype.card (TIdx la) * v / finrank ℚ K) /
      (Fintype.card (TIdx la) : ℝ) / 2 = u - v / finrank ℚ K := fun u v => by field_simp
  rw [key, add_div, Finset.sum_div (ι := T)]
  have hle : ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ((∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) -
      (∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) - Real.log (dim (la t)) / 2) ≤
      ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w -
        (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) :=
    Finset.sum_le_sum fun t _ => by
      have := log_det_onMat_le (hla t)
      rw [add_div, mul_div_cancel_left₀ _ hK.ne', mul_sub, mul_div_assoc]
      linarith
  rw [Finset.sum_sub_distrib (f := fun t => (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w)]
    at hle
  linarith

end GlobalTheory.FibSlope

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGeStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_dualWeylFibreLattice_ge : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  first | exact @GlobalTheory.FibSlope.slope_fibre_ge | exact GlobalTheory.FibSlope.slope_fibre_ge | (intros; apply GlobalTheory.FibSlope.slope_fibre_ge <;> assumption)
end

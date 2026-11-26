module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitDiscriminantMatrixQuotientIsUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTwConjMemCentMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryTwistInvolutionGLProperties
open GlobalTheory.Tw Matrix

namespace GlobalTheory.Tw.PhiConjugateTranspose

variable {n : ℕ} {R : Type} [CommRing R]

theorem phi_apply (i k : Fin n) : Phi n R i k = if k = i.rev then (-1 : R) ^ (i : ℕ) else 0 := by
  simp only [Phi, of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem phi_conj_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Phi n R * A * (Phi n R)ᵀ) i j = (-1 : R) ^ (i : ℕ) * A i.rev j.rev * (-1 : R) ^ (j : ℕ) := by
  simp [Matrix.mul_apply, phi_apply, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  have := phi_conj_apply (n := n) (R := R) 1
  ext i j
  have h := this i j
  rw [Matrix.mul_one] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [← mul_pow]
  · simp [hij]

theorem phi_transpose_mul : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp phi_mul_transpose

theorem phi_mul_phi : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i k
  simp only [Matrix.mul_apply, phi_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : k = i
  · subst h
    simp only [if_true, mul_one]
    rw [← pow_add, Fin.val_rev]
    have hk := k.isLt
    rw [show (k : ℕ) + (n - ((k : ℕ) + 1)) = n - 1 by omega]
  · simp [h, Ne.symm h]

theorem phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_left_inv phi_transpose_mul

theorem phi_transpose_inv : ((Phi n R)ᵀ)⁻¹ = Phi n R := Matrix.inv_eq_left_inv phi_mul_transpose

theorem conj_inv (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)⁻¹ = Phi n R * A⁻¹ * (Phi n R)ᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, phi_inv, phi_transpose_inv, Matrix.mul_assoc]

theorem det_conj (A : Matrix (Fin n) (Fin n) R) : (Phi n R * A * (Phi n R)ᵀ).det = A.det := by
  rw [det_mul, det_mul, mul_comm (Phi n R).det, mul_assoc, ← det_mul, phi_mul_transpose, det_one, mul_one]

variable [StarRing R]

theorem phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem phi_transpose_conjTranspose : ((Phi n R)ᵀ)ᴴ = Phi n R := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem conj_conjTranspose (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)ᴴ = Phi n R * Aᴴ * (Phi n R)ᵀ := by
  rw [conjTranspose_mul, conjTranspose_mul, phi_conjTranspose, phi_transpose_conjTranspose, Matrix.mul_assoc]

theorem theta_eq (g : Matrix (Fin n) (Fin n) R) : theta g = Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ := rfl

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta_eq, Matrix.mul_inv_rev, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), phi_transpose_mul, Matrix.one_mul]

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [theta_eq, inv_one, conjTranspose_one, Matrix.mul_one, phi_mul_transpose]

theorem det_theta (g : Matrix (Fin n) (Fin n) R) : (theta g).det = star (g⁻¹).det := by
  rw [theta_eq, det_conj, det_conjTranspose]

theorem theta_isUnit {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : IsUnit (theta g) := by
  rw [isUnit_iff_isUnit_det, det_theta]
  exact (isUnit_nonsing_inv_det _ ((isUnit_iff_isUnit_det g).mp hg)).star

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  have hd := (isUnit_iff_isUnit_det g).mp hg
  rw [theta_eq (theta g), theta_eq g, conj_inv, conj_conjTranspose, ← conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ hd, conjTranspose_conjTranspose]
  have h2 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← transpose_mul, phi_mul_phi, transpose_smul, transpose_one]
  calc Phi n R * (Phi n R * g * (Phi n R)ᵀ) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by
      rw [phi_mul_phi, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← mul_pow]
      simp

theorem theta_blockTriangular {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) (ht : g.BlockTriangular id) :
    (theta g).BlockTriangular id := by
  have : Invertible g := hg.invertible
  have hi : (g⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  intro i j hji
  rw [theta_eq, phi_conj_apply, conjTranspose_apply, hi]
  · simp
  · simpa [Fin.rev_lt_rev] using hji

end GlobalTheory.Tw.PhiConjugateTranspose

open GlobalTheory.Tw.PhiConjugateTranspose in
theorem GlobalTheory.Tw.theta_props : ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R], (Phi n R * (Phi n R)ᵀ = 1) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit (theta g) ∧ theta (theta g) = g) ∧ (∀ g h : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit h → theta (g * h) = theta g * theta h) ∧ (∀ x δ : Matrix (Fin n) (Fin n) R, IsUnit x → IsUnit δ → nrm (twConj x δ) = x⁻¹ * nrm δ * x) ∧ (∀ u δ : Matrix (Fin n) (Fin n) R, IsUnit u → IsUnit δ → nrm (δ * theta u) = nrm δ * ((theta δ)⁻¹ * theta u * theta δ) * u) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → g.BlockTriangular id → (theta g).BlockTriangular id) ∧ ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → (theta g).det * star g.det = 1 := by
  intro n R _ _
  refine ⟨phi_mul_transpose, fun g hg => ⟨theta_isUnit hg, theta_theta hg⟩, fun g h _ _ => theta_mul g h, ?_, ?_,
    fun g hg ht => theta_blockTriangular hg ht, ?_⟩
  · intro x δ hx _
    have hxd := (isUnit_iff_isUnit_det x).mp hx
    simp only [nrm, twConj, theta_mul, theta_theta hx]
    have h1 : theta x * theta x⁻¹ = 1 := by rw [← theta_mul, mul_nonsing_inv _ hxd, theta_one]
    calc x⁻¹ * δ * theta x * (theta x⁻¹ * theta δ * x)
        = x⁻¹ * δ * (theta x * theta x⁻¹) * theta δ * x := by simp only [Matrix.mul_assoc]
      _ = x⁻¹ * (δ * theta δ) * x := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  · intro u δ hu hδ
    have htd := (isUnit_iff_isUnit_det _).mp (theta_isUnit hδ)
    simp only [nrm, theta_mul, theta_theta hu]
    calc δ * theta u * (theta δ * u)
        = δ * (theta δ * (theta δ)⁻¹) * theta u * theta δ * u := by
          rw [mul_nonsing_inv _ htd, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = δ * theta δ * ((theta δ)⁻¹ * theta u * theta δ) * u := by simp only [Matrix.mul_assoc]
  · intro g hg
    have hd := (isUnit_iff_isUnit_det g).mp hg
    rw [det_theta, ← star_mul, ← det_mul, mul_nonsing_inv _ hd, det_one, star_one]
end

open GlobalTheory.Tw Matrix

namespace GlobalTheory.TwIntegral

section Basics

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

open Matrix in
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
theorem _root_.GlobalTheory.TwIntegral.intg_inv {A : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) :
    ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
  intro i j
  have hadj : ‖A.adjugate i j‖ ≤ 1 := by
    rw [adjugate_apply]
    apply _root_.GlobalTheory.norm_det_le_one_of_entries_le_one
    intro k l
    by_cases hk : k = j
    · subst hk
      rw [updateRow_self]
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    · rw [updateRow_ne hk]
      exact hA k l
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd,
    inv_one, one_mul]
  exact hadj

open Matrix in
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
theorem _root_.GlobalTheory.TwIntegral.isUnit_of_norm_det {A : Matrix (Fin n) (Fin n) E} (hd : ‖A.det‖ = 1) :
    IsUnit A := by
  rw [isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  rw [h, norm_zero] at hd
  exact zero_ne_one hd

end Basics

open Matrix in
private theorem theta_integral_of_integral_of_norm_det_one (F E : Type)
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] {n : ℕ} {g : Matrix (Fin n) (Fin n) E}
    (hg : ∀ i j, ‖g i j‖ ≤ 1) (hd : ‖g.det‖ = 1) :
    (∀ i j, ‖_root_.GlobalTheory.Tw.theta g i j‖ ≤ 1) ∧ ‖(_root_.GlobalTheory.Tw.theta g).det‖ = 1 := by
  haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)
  have hΦ : ∀ i j, ‖_root_.GlobalTheory.Tw.Phi n E i j‖ ≤ 1 := by
    intro i j
    rw [_root_.GlobalTheory.Tw.Model.Phi_apply']
    split_ifs <;> simp
  have hΦt : ∀ i j, ‖(_root_.GlobalTheory.Tw.Phi n E)ᵀ i j‖ ≤ 1 := fun i j => hΦ j i
  have hinv := _root_.GlobalTheory.TwIntegral.intg_inv hg hd
  have hH : ∀ i j, ‖(g⁻¹)ᴴ i j‖ ≤ 1 := by
    intro i j
    rw [conjTranspose_apply, _root_.GlobalTheory.JR.Unram.norm_star F]
    exact hinv j i
  unfold _root_.GlobalTheory.Tw.theta
  refine ⟨_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul hΦ hH) hΦt, ?_⟩
  have h1 : (_root_.GlobalTheory.Tw.Phi n E).det * (_root_.GlobalTheory.Tw.Phi n E)ᵀ.det = 1 := by
    rw [← det_mul, _root_.GlobalTheory.Tw.Model.Phi_mul_transpose, det_one]
  rw [det_mul, det_mul, mul_right_comm, h1, one_mul, det_conjTranspose, det_nonsing_inv,
    Ring.inverse_eq_inv', _root_.GlobalTheory.JR.Unram.norm_star F, norm_inv,
    hd, inv_one]

open Matrix in
private theorem exists_star_fixed_uniformizer (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] :
    ∃ ϖ : E, star ϖ = ϖ ∧ 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)
  haveI := _root_.GlobalTheory.JR.Unram.lcE F (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one E
  have hK : IsCompact (Metric.ball (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn ⟨y, by simpa using hy1⟩ continuous_norm.continuousOn
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.JR.Unram.unram (F := F) w
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hyw : ‖y‖ ≤ ‖w‖ := hmax (by simpa using hy1)
  refine ⟨algebraMap F E a, _root_.GlobalTheory.JR.Unram.star_fix a,
    ?_, ?_, ?_⟩ <;> rw [norm_algebraMap', ← ha]
  · exact hy0.trans_le hyw
  · exact hw1
  · intro z hz
    exact hmax (by simpa using hz)

open Matrix in
private theorem mul_inv_mul_conj_eq_one_of_norm_quotient {B : Type} [CommRing B] (τ : B → B)
    (w c Q Qi X Xi : B) (hτmul : ∀ g h, τ (g * h) = τ g * τ h) (hτone : τ 1 = 1)
    (hX : X = (w + c ^ 3) * (w * c ^ 2 + (τ c * c) ^ 2))
    (hτX : τ X = (w + τ c ^ 3) * (w * τ c ^ 2 + (c * τ c) ^ 2))
    (hτP : τ ((w * c ^ 3 + (τ c * c) ^ 3) * (w + c ^ 2)) =
      (w * τ c ^ 3 + (c * τ c) ^ 3) * (w + τ c ^ 2))
    (e1 : Q * Qi = 1) (e2 : Q * X = (w * c ^ 3 + (τ c * c) ^ 3) * (w + c ^ 2))
    (e3 : X * Xi = 1) :
    c * Qi * τ (c * Qi) = 1 := by
  have e1' : τ Q * τ Qi = 1 := by rw [← hτmul, e1, hτone]
  have e3' : τ X * τ Xi = 1 := by rw [← hτmul, e3, hτone]
  have e2' : τ Q * τ X = (w * τ c ^ 3 + (c * τ c) ^ 3) * (w + τ c ^ 2) := by
    rw [← hτmul, e2, hτP]
  have hmain : Q * τ Q = τ c * c := by
    calc Q * τ Q = Q * τ Q * (X * Xi) * (τ X * τ Xi) := by rw [e3, e3', mul_one, mul_one]
      _ = (Q * X) * (τ Q * τ X) * Xi * τ Xi := by ring
      _ = τ c * c * (X * Xi) * (τ X * τ Xi) := by
          rw [e2, e2', hτX, hX]
          ring
      _ = τ c * c := by rw [e3, e3', mul_one, mul_one]
  calc c * Qi * τ (c * Qi) = (Q * τ Q) * Qi * τ Qi := by rw [hmain, hτmul]; ring
    _ = (Q * Qi) * (τ Q * τ Qi) := by ring
    _ = 1 := by rw [e1, e1', one_mul]

open Matrix in
private theorem mul_inv_quotient_mem_twistedCentralizerGL_lemma_3 {E : Type} [Field E] [StarRing E]
    {n : ℕ} (δ c : Matrix (Fin n) (Fin n) E) (ϖ : E) (hδ : IsUnit δ) (hϖ : star ϖ = ϖ)
    (hsep : (_root_.GlobalTheory.Tw.nrm δ).charpoly.Separable) (hc : IsUnit c)
    (hcN : c * _root_.GlobalTheory.Tw.nrm δ = _root_.GlobalTheory.Tw.nrm δ * c)
    (hP3 : IsUnit (ϖ • 1 + c ^ 3))
    (hP4 : IsUnit (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))
    (hQ : IsUnit ((ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) *
      ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹)) :
    c * ((ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) *
      ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹)⁻¹ ∈
      _root_.GlobalTheory.Tw.cent δ := by
  set N := _root_.GlobalTheory.Tw.nrm δ
  set A := Algebra.adjoin E {N}
  letI : CommRing A := { (inferInstance : Ring A) with mul_comm := mul_comm' }
  have hmem : ∀ g, g * N = N * g → g ∈ A := fun g hg =>
    _root_.GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N g hsep hg
  have hNA : N ∈ A := Algebra.self_mem_adjoin_singleton E N
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hinvA : ∀ g ∈ A, IsUnit g → g⁻¹ ∈ A := by
    intro g hg hu
    have hd : IsUnit g.det := (isUnit_iff_isUnit_det g).mp hu
    apply hmem
    calc g⁻¹ * N = g⁻¹ * N * (g * g⁻¹) := by rw [mul_nonsing_inv _ hd, mul_one]
      _ = g⁻¹ * (N * g) * g⁻¹ := by simp only [mul_assoc]
      _ = g⁻¹ * (g * N) * g⁻¹ := by rw [hcomm N hNA g hg]
      _ = N * g⁻¹ := by rw [← mul_assoc, nonsing_inv_mul _ hd, one_mul]
  have hτA : ∀ g ∈ A, _root_.GlobalTheory.Tw.adj δ g ∈ A ∧
      _root_.GlobalTheory.Tw.adj δ (_root_.GlobalTheory.Tw.adj δ g) = g :=
    _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hδ
  let τA : A → A := fun g => ⟨_root_.GlobalTheory.Tw.adj δ g.1, (hτA g.1 g.2).1⟩
  have hτmul : ∀ g h : A, τA (g * h) = τA g * τA h := by
    intro g h
    apply Subtype.ext
    show _root_.GlobalTheory.Tw.adj δ (g.1 * h.1) =
      _root_.GlobalTheory.Tw.adj δ g.1 * _root_.GlobalTheory.Tw.adj δ h.1
    rw [_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hδ]
    exact hcomm _ (hτA h.1 h.2).1 _ (hτA g.1 g.2).1
  have hτ0 : _root_.GlobalTheory.Tw.adj δ 0 = 0 := by
    have h := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ 1 0 0
    simpa using h
  have hτadd : ∀ g h : A, τA (g + h) = τA g + τA h := by
    intro g h
    apply Subtype.ext
    show _root_.GlobalTheory.Tw.adj δ (g.1 + h.1) =
      _root_.GlobalTheory.Tw.adj δ g.1 + _root_.GlobalTheory.Tw.adj δ h.1
    have e := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ 1 g.1 h.1
    simpa using e
  have hτsmul : ∀ (r : E) (g : A), τA (r • g) = star r • τA g := by
    intro r g
    apply Subtype.ext
    show _root_.GlobalTheory.Tw.adj δ (r • g.1) = star r • _root_.GlobalTheory.Tw.adj δ g.1
    have e := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ r g.1 0
    simpa [hτ0] using e
  have hτone : τA 1 = 1 := Subtype.ext (_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_one' hδ)
  have hτpow : ∀ (g : A) (k : ℕ), τA (g ^ k) = τA g ^ k := by
    intro g k
    induction k with
    | zero => simpa using hτone
    | succ k ih => rw [pow_succ, hτmul, ih, pow_succ]
  have hττ : ∀ g : A, τA (τA g) = g := fun g => Subtype.ext (hτA g.1 g.2).2
  have hcA : c ∈ A := hmem c hcN
  have hsub : ∀ g : A, IsUnit g.1 → (g.1)⁻¹ ∈ A := fun g hg => hinvA g.1 g.2 hg
  let cA : A := ⟨c, hcA⟩
  let w : A := algebraMap E A ϖ
  have hw : (w : Matrix (Fin n) (Fin n) E) = ϖ • 1 := Algebra.algebraMap_eq_smul_one ϖ
  have hτw : τA w = w := by
    show τA (algebraMap E A ϖ) = algebraMap E A ϖ
    rw [Algebra.algebraMap_eq_smul_one, hτsmul, hτone, hϖ]
  let X : A := (w + cA ^ 3) * (w * cA ^ 2 + (τA cA * cA) ^ 2)
  let P : A := (w * cA ^ 3 + (τA cA * cA) ^ 3) * (w + cA ^ 2)
  have hXm : X.1 =
      (ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2) := by
    show ((w : Matrix (Fin n) (Fin n) E) + c ^ 3) *
      ((w : Matrix (Fin n) (Fin n) E) * c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2) = _
    rw [hw, smul_mul_assoc, one_mul]
  have hPm : P.1 =
      (ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) := by
    show ((w : Matrix (Fin n) (Fin n) E) * c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) *
      ((w : Matrix (Fin n) (Fin n) E) + c ^ 2) = _
    rw [hw, smul_mul_assoc, one_mul]
  have hXu : IsUnit X.1 := hXm ▸ hP3.mul hP4
  have hXd : IsUnit (X.1).det := (isUnit_iff_isUnit_det _).mp hXu
  let Xi : A := ⟨(X.1)⁻¹, hsub X hXu⟩
  let QA : A := P * Xi
  have hQm : QA.1 =
      (ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) *
      ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹ := by
    show P.1 * (X.1)⁻¹ = _
    rw [hPm, hXm]
  have hQu : IsUnit QA.1 := hQm ▸ hQ
  have hQd : IsUnit (QA.1).det := (isUnit_iff_isUnit_det _).mp hQu
  let Qi : A := ⟨(QA.1)⁻¹, hsub QA hQu⟩
  have e1 : QA * Qi = 1 := Subtype.ext (mul_nonsing_inv _ hQd)
  have e2 : QA * X = P := Subtype.ext (nonsing_inv_mul_cancel_right _ _ hXd)
  have e3 : X * Xi = 1 := Subtype.ext (mul_nonsing_inv _ hXd)
  have hτX : τA X = (w + τA cA ^ 3) * (w * τA cA ^ 2 + (cA * τA cA) ^ 2) := by
    simp only [X, hτmul, hτadd, hτpow, hττ, hτw]
  have hτP : τA P = (w * τA cA ^ 3 + (cA * τA cA) ^ 3) * (w + τA cA ^ 2) := by
    simp only [P, hτmul, hτadd, hτpow, hττ, hτw]
  have htt : cA * Qi * τA (cA * Qi) = 1 :=
    mul_inv_mul_conj_eq_one_of_norm_quotient τA w cA QA Qi X Xi hτmul hτone rfl hτX hτP
      e1 e2 e3
  rw [← hQm]
  have ht : IsUnit (c * (QA.1)⁻¹) := hc.mul ((isUnit_nonsing_inv_iff).mpr hQu)
  have htt' : c * (QA.1)⁻¹ * _root_.GlobalTheory.Tw.adj δ (c * (QA.1)⁻¹) = 1 :=
    congrArg Subtype.val htt
  rw [_root_.GlobalTheory.Tw.Model.adj_eq hδ ht] at htt'
  have hθ := ((_root_.GlobalTheory.Tw.theta_props n E).2.1 _ ht).1
  have hM : IsUnit (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹) :=
    (hδ.mul hθ).mul ((isUnit_nonsing_inv_iff).mpr hδ)
  have hMd := (isUnit_iff_isUnit_det _).mp hM
  have hδd := (isUnit_iff_isUnit_det _).mp hδ
  have heq : c * (QA.1)⁻¹ = δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹ := by
    calc c * (QA.1)⁻¹ = c * (QA.1)⁻¹ * (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹)⁻¹ *
          (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹) :=
          (nonsing_inv_mul_cancel_right _ _ hMd).symm
      _ = _ := by rw [htt', one_mul]
  refine ⟨ht, ?_⟩
  show c * (QA.1)⁻¹ * δ = δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹)
  rw [heq, nonsing_inv_mul_cancel_right _ _ hδd, ← heq]

open Matrix in
theorem _root_.GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] (n : ℕ) (δ x : Matrix (Fin n) (Fin n) E),
    (∀ i j, ‖δ i j‖ ≤ 1) → ‖δ.det‖ = 1 →
    (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * (_root_.GlobalTheory.Tw.nrm δ).charpoly +
        v * Polynomial.derivative (_root_.GlobalTheory.Tw.nrm δ).charpoly = 1) →
    IsUnit x → (∀ i j, ‖_root_.GlobalTheory.Tw.twConj x δ i j‖ ≤ 1) →
    ‖(_root_.GlobalTheory.Tw.twConj x δ).det‖ = 1 →
    ∃ t ∈ _root_.GlobalTheory.Tw.cent δ, ∃ k : Matrix (Fin n) (Fin n) E, (∀ i j, ‖k i j‖ ≤ 1) ∧
      ‖k.det‖ = 1 ∧ x = t * k := by
  intro F E _ _ _ _ _ n δ x hδ hδd ⟨u, v, hu, hv, huv⟩ hx hx' hx'd
  haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)
  have hδu := _root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hδd
  have hδdu := (isUnit_iff_isUnit_det δ).mp hδu
  obtain ⟨hθδ, -⟩ := theta_integral_of_integral_of_norm_det_one F E hδ hδd
  have hN : _root_.GlobalTheory.Tw.nrm δ = δ * _root_.GlobalTheory.Tw.theta δ := rfl
  have hNi : ∀ i j, ‖_root_.GlobalTheory.Tw.nrm δ i j‖ ≤ 1 := by
    rw [hN]; exact _root_.GlobalTheory.UnitDiscAlg.integ_mul hδ hθδ
  have hsep : (_root_.GlobalTheory.Tw.nrm δ).charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨hθx', -⟩ := theta_integral_of_integral_of_norm_det_one F E hx' hx'd
  have hconj : x⁻¹ * _root_.GlobalTheory.Tw.nrm δ * x =
      _root_.GlobalTheory.Tw.twConj x δ * _root_.GlobalTheory.Tw.theta (_root_.GlobalTheory.Tw.twConj x δ) := by
    unfold _root_.GlobalTheory.Tw.twConj
    rw [hN, _root_.GlobalTheory.Tw.Model.theta_mul, _root_.GlobalTheory.Tw.Model.theta_mul,
      _root_.GlobalTheory.Tw.Model.theta_theta hx]
    simp only [mul_assoc]
    rw [← mul_assoc (_root_.GlobalTheory.Tw.theta x), _root_.GlobalTheory.Tw.Model.theta_mul_theta_inv hx, one_mul]
  have hxN : ∀ i j, ‖(x⁻¹ * _root_.GlobalTheory.Tw.nrm δ * x) i j‖ ≤ 1 := by
    rw [hconj]; exact _root_.GlobalTheory.UnitDiscAlg.integ_mul hx' hθx'
  obtain ⟨c, hc, hcN, hk, hkd⟩ :=
    _root_.GlobalTheory.IntConj.exists_commuting_mul_integral E n _ x hNi ⟨u, v, hu, hv, huv⟩ hx hxN
  have hcd := (isUnit_iff_isUnit_det c).mp hc
  obtain ⟨k, rfl⟩ : ∃ k, x = c * k := ⟨c⁻¹ * x, (mul_nonsing_inv_cancel_left c x hcd).symm⟩
  rw [nonsing_inv_mul_cancel_left _ _ hcd] at hk hkd
  have hkdu := (isUnit_iff_isUnit_det k).mp (_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hkd)
  obtain ⟨hθk, hθkd⟩ := theta_integral_of_integral_of_norm_det_one F E hk hkd
  have hθkdu := (isUnit_iff_isUnit_det _).mp (_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hθkd)
  have hcA : c ∈ Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ} :=
    _root_.GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ c hsep hcN
  obtain ⟨haA, -⟩ := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hδu c hcA
  have hcommN : ∀ g ∈ Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ},
      g * _root_.GlobalTheory.Tw.nrm δ = _root_.GlobalTheory.Tw.nrm δ * g := fun g hg =>
    congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ})
      ⟨_, Algebra.self_mem_adjoin_singleton E _⟩)
  have hsN := hcommN _ (Subalgebra.mul_mem _ haA hcA)
  have hs : _root_.GlobalTheory.Tw.adj δ c * c =
      δ * _root_.GlobalTheory.Tw.theta k * (_root_.GlobalTheory.Tw.twConj (c * k) δ)⁻¹ * k⁻¹ := by
    rw [_root_.GlobalTheory.Tw.Model.adj_eq hδu hc]
    unfold _root_.GlobalTheory.Tw.twConj
    rw [_root_.GlobalTheory.Tw.Model.theta_mul]
    have hck : IsUnit (c * k).det := by rw [det_mul]; exact hcd.mul hkdu
    simp only [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hδdu, nonsing_inv_nonsing_inv _ hck,
      nonsing_inv_nonsing_inv _ hcd, nonsing_inv_nonsing_inv _ hkdu, mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hθkdu, mul_nonsing_inv _ hkdu, mul_one]
  have hsi : ∀ i j, ‖(_root_.GlobalTheory.Tw.adj δ c * c) i j‖ ≤ 1 := by
    rw [hs]
    exact _root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul
      (_root_.GlobalTheory.UnitDiscAlg.integ_mul hδ hθk) (_root_.GlobalTheory.TwIntegral.intg_inv hx' hx'd))
      (_root_.GlobalTheory.TwIntegral.intg_inv hk hkd)
  have hsd : ‖(_root_.GlobalTheory.Tw.adj δ c * c).det‖ = 1 := by
    rw [hs]
    simp [det_mul, det_nonsing_inv, Ring.inverse_eq_inv', hδd, hθkd, hx'd, hkd]
  obtain ⟨ϖ, hϖs, hϖ0, hϖ1, hϖmax⟩ := exists_star_fixed_uniformizer F E
  haveI := _root_.GlobalTheory.JR.Unram.lcE F (E := E)
  obtain ⟨-, hP3, hP4, -, hQi, hQd⟩ := _root_.GlobalTheory.UnitDiscAlg.units_quotient E n _ c _ ϖ hNi
    ⟨u, v, hu, hv, huv⟩ hϖ0 hϖ1 hϖmax hc hcN hsN hsi hsd
  have hQ := _root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hQd
  refine ⟨_, mul_inv_quotient_mem_twistedCentralizerGL_lemma_3 δ c ϖ hδu hϖs hsep hc hcN hP3 hP4 hQ,
    _ * k, _root_.GlobalTheory.UnitDiscAlg.integ_mul hQi hk, ?_, ?_⟩
  · rw [det_mul, norm_mul, hQd, hkd, one_mul]
  · rw [mul_assoc, nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).mp hQ)]

end GlobalTheory.TwIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertUniq

section Fixed
variable {L : Type} [Field L]

abbrev fixF (σ : L →+* L) : Subfield L := σ.eqLocusField (RingHom.id L)

abbrev starOfInv (σ : L →+* L) (h : ∀ x, σ (σ x) = x) : StarRing L where
  star := σ
  star_involutive := h
  star_mul x y := by rw [map_mul]; exact mul_comm _ _
  star_add := map_add σ

theorem finrank_fixF (σ : L →+* L) (h : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Module.finrank (fixF σ) L = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx₀)
  have hli : LinearIndependent (fixF σ) ![(1 : L), x₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : σ (s : L) = s := s.2
    have ht : σ (t : L) = t := t.2
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    change (s : L) + (t : L) * x₀ = 0 at hst
    have h2 : (s : L) + (t : L) * σ x₀ = 0 := by
      have := congrArg σ hst
      rwa [map_add, map_mul, hs, ht, map_zero] at this
    have ht0 : (t : L) = 0 := by
      have : (t : L) * (x₀ - σ x₀) = 0 := by linear_combination hst - h2
      exact (mul_eq_zero.1 this).resolve_right hd
    refine ⟨Subtype.ext ?_, Subtype.ext ht0⟩
    simpa [ht0] using hst
  have hsp : ⊤ ≤ Submodule.span (fixF σ) (Set.range ![(1 : L), x₀]) := by
    intro y _
    set b := (y - σ y) / (x₀ - σ x₀) with hbdef
    have hb : σ b = b := by
      rw [hbdef, map_div₀, map_sub, map_sub, h, h, ← neg_sub y (σ y), ← neg_sub x₀ (σ x₀), neg_div_neg_eq]
    set a := y - b * x₀ with hadef
    have hbm : b * (x₀ - σ x₀) = y - σ y := div_mul_cancel₀ _ hd
    have ha : σ a = a := by
      rw [hadef, map_sub, map_mul, hb]
      linear_combination hbm
    have hy : y = (⟨a, ha⟩ : fixF σ) • (1 : L) + (⟨b, hb⟩ : fixF σ) • x₀ := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change y = a * 1 + b * x₀
      rw [hadef]; ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
  simp

end Fixed

theorem eq_twCent_mul_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  intro E _ _ _ hU n w hs y g hy hbez hyg
  obtain ⟨hc, hinv, hval, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hϖ, -⟩, -⟩ := hns hs
  obtain ⟨-, -, hϖf, hϖv, ⟨x₀, -, hx₀⟩, -⟩ := hϖ
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  letI : StarRing (w.adicCompletion E) := starOfInv (cj w) hinv
  have hle1 : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  have hneq : ∀ x y : w.adicCompletion E, Valued.v x = Valued.v y → ‖x‖ = ‖y‖ := fun x y h =>
    le_antisymm (Valued.toNormedField.norm_le_iff.2 h.le) (Valued.toNormedField.norm_le_iff.2 h.ge)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖi : cj w ϖ⁻¹ = ϖ⁻¹ := by rw [map_inv₀, hϖf]
  have hϖn : 1 < ‖ϖ⁻¹‖ := by
    rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀, hϖv]
    exact one_lt_inv₀ (by simp) |>.2 (by rw [← WithZero.coe_one, WithZero.coe_lt_coe]; decide)
  letI nF : NontriviallyNormedField (fixF (cj w)) :=
    { (inferInstance : NormedField (fixF (cj w))) with non_trivial := ⟨⟨ϖ⁻¹, hϖi⟩, hϖn⟩ }
  letI : NormedAlgebra (fixF (cj w)) (w.adicCompletion E) :=
    { (inferInstance : Algebra (fixF (cj w)) (w.adicCompletion E)) with
      norm_smul_le := fun r x => by rw [Algebra.smul_def, norm_mul]; exact le_of_eq rfl }
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI hUn : GlobalTheory.JR.Unram (fixF (cj w)) (w.adicCompletion E) :=
    { charZero := ⟨fun a b h => Nat.cast_injective (R := w.adicCompletion E) (by simpa using congrArg (algebraMap (fixF (cj w)) (w.adicCompletion E)) h)⟩
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := (isClosed_eq hc continuous_id).isClosedEmbedding_subtypeVal.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixF (cj w) hinv ⟨x₀, fun h => by rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      star_fix := fun x => x.2
      star_ne := ⟨x₀, fun h => by change cj w x₀ = x₀ at h; rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      norm_star := fun x => hneq _ _ (hval x)
      unram := by
        intro x
        by_cases hx : x = 0
        · exact ⟨0, by rw [hx]; rfl⟩
        · have hv0 : Valued.v x ≠ 0 := by simpa using hx
          refine ⟨⟨ϖ ^ (-WithZero.log (Valued.v x)), by
            change cj w (ϖ ^ (-WithZero.log (Valued.v x))) = ϖ ^ (-WithZero.log (Valued.v x)); rw [map_zpow₀, hϖf]⟩, ?_⟩
          change ‖x‖ = ‖ϖ ^ (-WithZero.log (Valued.v x))‖
          apply hneq
          rw [map_zpow₀, hϖv, show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) from rfl,
            ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hv0] }
  have hcs : cj w = starRingEnd (w.adicCompletion E) := RingHom.ext fun _ => rfl
  have hth : ∀ h : GLw n w, (thL n w h).val = GlobalTheory.Tw.theta h.val := by
    intro h
    rw [thL, if_neg hs, hcs, thetaGL_val]
  have hnr : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
    rw [nrmL, if_neg hs, Units.val_mul, hcs, thetaGL_val]; rfl

  have hmem (O : Subring (w.adicCompletion E)) (h : GLw n w) :
      h ∈ GLint (Fin n) O ↔
        (∀ i j, h.val i j ∈ O) ∧ ∀ i j, (h⁻¹).val i j ∈ O := by
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
      · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h.mul_inv
      · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h.inv_mul
  have hint : ∀ h : GLw n w, h ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ i j, ‖h.val i j‖ ≤ 1) ∧ ‖h.val.det‖ = 1 := by
    intro h hh
    obtain ⟨h1, h2⟩ := (hmem (Ov E w) h).1 hh
    have hdet : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ i j, M i j ∈ Ov E w) → M.det ∈ Ov E w := by
      intro M hM
      let M₀ : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨M i j, hM i j⟩
      have hM₀ : M = (Ov E w).subtype.mapMatrix M₀ := by ext i j; rfl
      rw [hM₀, ← RingHom.map_det]
      exact (M₀.det).2
    have d1 : ‖h.val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h1)
    have d2 : ‖(h⁻¹).val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h2)
    have hprod : ‖h.val.det‖ * ‖(h⁻¹).val.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
    refine ⟨fun i j => (hle1 _).2 (h1 i j), ?_⟩
    nlinarith [norm_nonneg h.val.det, norm_nonneg (h⁻¹).val.det]
  have hintR : ∀ h : GLw n w, (∀ i j, ‖h.val i j‖ ≤ 1) → ‖h.val.det‖ = 1 → h ∈ GlobalTheory.LFun.KGL w (n := n) := by
    intro h h1 h2
    refine (hmem (Ov E w) h).2 ⟨fun i j => (hle1 _).1 (h1 i j), fun i j => ?_⟩
    rw [Matrix.coe_units_inv]
    exact (hle1 _).1 (GlobalTheory.TwIntegral.intg_inv h1 h2 i j)
  obtain ⟨hy1, hy2⟩ := hint y hy
  obtain ⟨hg1, hg2⟩ := hint _ hyg
  have htw : GlobalTheory.Tw.twConj g.val y.val = (g⁻¹ * y * thL n w g).val := by
    rw [Units.val_mul, Units.val_mul, hth, Matrix.coe_units_inv]; rfl
  obtain ⟨u, v, hu, hv, huv⟩ := hbez
  rw [hnr] at huv
  obtain ⟨t, ⟨htu, htc⟩, k, hk1, hk2, hx⟩ := GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul (fixF (cj w)) (w.adicCompletion E) n
    y.val g.val hy1 hy2 ⟨u, v, fun i => (hle1 _).2 (hu i), fun i => (hle1 _).2 (hv i), huv⟩ g.isUnit
    (by rw [htw]; exact hg1) (by rw [htw]; exact hg2)
  have hku : IsUnit k := GlobalTheory.TwIntegral.isUnit_of_norm_det hk2
  refine ⟨htu.unit, ?_, hku.unit, hintR _ (by simpa using hk1) (by simpa using hk2), Units.ext ?_⟩
  · show htu.unit * y = y * thL n w htu.unit
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hth, IsUnit.unit_spec]
    exact htc
  · rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    exact hx

end GlobalTheory.InertUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizerStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.InertUniq.eq_twCent_mul_KGL | exact GlobalTheory.InertUniq.eq_twCent_mul_KGL | (intros; apply GlobalTheory.InertUniq.eq_twCent_mul_KGL <;> assumption)
end

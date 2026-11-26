module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqrtNsqLeOfAbsLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOrthSucc
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.PairingTensor

open TensorProduct

variable {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

noncomputable def contrR (l : B →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A l

noncomputable def contrL (l : A →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B l

@[simp] theorem contrR_tmul (l : B →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrR l (a ⊗ₜ[ℂ] b) = l b • a := by
  simp [contrR]

@[simp] theorem contrL_tmul (l : A →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrL l (a ⊗ₜ[ℂ] b) = l a • b := by
  simp [contrL]

theorem apply_contrR (l : A →ₗ[ℂ] ℂ) (m : B →ₗ[ℂ] ℂ) (z : TensorProduct ℂ A B) :
    l (contrR m z) = m (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem contrR_map (m : B →ₗ[ℂ] ℂ) (a : Module.End ℂ A) (z : TensorProduct ℂ A B) :
    contrR m (TensorProduct.map a LinearMap.id z) = a (contrR m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem contrL_map (l : A →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : TensorProduct ℂ A B) :
    contrL l (TensorProduct.map LinearMap.id b z) = b (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem eq_zero_of_contrR {ι : Type} (m : ι → B →ₗ[ℂ] ℂ) (hm : ∀ b, (∀ y, m y b = 0) → b = 0)
    (z : TensorProduct ℂ A B) (hz : ∀ y, contrR (m y) z = 0) : z = 0 := by
  classical
  let bA := Module.Basis.ofVectorSpace ℂ A
  have key : ∀ (w : TensorProduct ℂ A B) i,
      TensorProduct.equivFinsuppOfBasisLeft bA w i = contrL (bA.coord i) w := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft bA).injective
  ext i
  rw [key, map_zero, Finsupp.zero_apply]
  apply hm
  intro y
  rw [← apply_contrR, hz, map_zero]

theorem inner_separates {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (i : A →ₗ[ℂ] H) (hi : Function.Injective i) (a : A) (h : ∀ x, inner ℂ x (i a) = 0) :
    a = 0 := by
  apply hi
  rw [map_zero]
  exact inner_self_eq_zero.mp (h (i a))

theorem exists_linearMap_tensor :
    ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  intro V A B H₁ H₂ _ _ _ _ _ _ _ _ _ _ i₁ i₂ h₁ h₂ φ ψ hφψ hE
  let m : H₂ → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ y) ∘ₗ i₂
  let l : H₁ → A →ₗ[ℂ] ℂ := fun x => (innerₛₗ ℂ x) ∘ₗ i₁
  have hm : ∀ y b, m y b = inner ℂ y (i₂ b) := fun _ _ => rfl
  have hl : ∀ x a, l x a = inner ℂ x (i₁ a) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => inner_separates i₂ h₂ b h
  have sepl : ∀ a, (∀ x, l x a = 0) → a = 0 := fun a h => inner_separates i₁ h₁ a h
  have sepR : ∀ z w : TensorProduct ℂ A B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  have sepL : ∀ z w : TensorProduct ℂ A B, (∀ x, contrL (l x) z = contrL (l x) w) → z = w := by
    intro z w h
    apply sepR
    intro y
    rw [← sub_eq_zero]
    apply sepl
    intro x
    rw [map_sub, apply_contrR, apply_contrR, h, sub_self]
  have ex : ∀ P, ∃ z : TensorProduct ℂ A B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ (e j) P, fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, ha, hm, ← hφψ]
  choose g hg using ex
  let f : V →ₗ[ℂ] TensorProduct ℂ A B :=
    { toFun := g
      map_add' := fun P Q => sepR _ _ fun y => by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]
      map_smul' := fun s P => sepR _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }
  have hf : ∀ P y, contrR (m y) (f P) = φ y P := hg
  have hf' : ∀ P x, contrL (l x) (f P) = ψ x P := by
    intro P x
    rw [← sub_eq_zero]
    apply sepm
    intro y
    rw [map_sub, ← apply_contrR, hf, hl, hm, hφψ, sub_self]
  refine ⟨f, fun P hP y => by rw [← hf, hP, map_zero], fun c a h => ?_, fun c b h => ?_⟩
  · ext P
    refine sepR _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, h]
  · ext P
    refine sepL _ _ fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrL_map, hf', hf', h]

end GlobalTheory.PairingTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairingStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_tensor_of_pairing : ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  first | exact @GlobalTheory.PairingTensor.exists_linearMap_tensor | exact GlobalTheory.PairingTensor.exists_linearMap_tensor | (intros; apply GlobalTheory.PairingTensor.exists_linearMap_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegree
noncomputable section
namespace GlobalTheory.FockDegree
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem inner_eq_zero_of_deriv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → H →L[ℂ] H) (hn : ∀ t x, ‖U t x‖ = ‖x‖) (hinv : ∀ t x, U t (U (-t) x) = x)
    (K : H →L[ℂ] H) (hK : ∀ t x, K (U t x) = U t (K x)) (x v : H) (a b : ℝ) (hab : a ≠ b)
    (hx : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) 0)
    (hv : HasDerivAt (fun t : ℝ => U t v) ((Complex.I * b) • v) 0) :
    inner ℂ x (K v) = 0 := by
  have hU : ∀ t y z, inner ℂ (U t y) (U t z) = inner ℂ y z := fun t y z =>
    LinearIsometry.inner_map_map (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H) y z
  have h1 : HasDerivAt (fun t : ℝ => K (U t v)) (K ((Complex.I * b) • v)) 0 :=
    (K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) x) h1
  have h3 : HasDerivAt (fun t : ℝ => U (-t) x) ((-1 : ℝ) • ((Complex.I * a) • x)) 0 := by
    have hx' : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) (-0) := by
      rw [neg_zero]; exact hx
    exact hx'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h4 := HasDerivAt.inner ℂ h3 (hasDerivAt_const (0 : ℝ) (K v))
  have heq : (fun t : ℝ => inner ℂ x (K (U t v))) = fun t : ℝ => inner ℂ (U (-t) x) (K v) := by
    funext t
    rw [hK, ← hU t (U (-t) x) (K v), hinv]
  rw [heq] at h2
  have h5 := h2.unique h4
  simp only [map_smul, inner_smul_right, inner_zero_left, inner_zero_right, add_zero, zero_add,
    neg_smul, one_smul, inner_neg_left, inner_smul_left, map_mul, Complex.conj_I,
    Complex.conj_ofReal] at h5
  have h6 : (Complex.I * ((b : ℂ) - a)) * inner ℂ x (K v) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.1 h6 with h | h
  · exfalso
    rcases mul_eq_zero.1 h with h | h
    · exact Complex.I_ne_zero h
    · exact hab (by exact_mod_cast (sub_eq_zero.1 h).symm)
  · exact h

theorem Jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (fun a => if a.isLeft then (1 : ℂ) else -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem smul_I_Jm_mem (p q : ℕ) (t : ℝ) : t • (Complex.I • Jm p q) ∈ upq p q := by
  have h : (Jm p q).conjTranspose = Jm p q := by
    rw [Jm_eq_diagonal, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases ha : a.isLeft <;> simp [ha]
  simp [upq, Matrix.conjTranspose_smul, h]

theorem I_Jm_mem (p q : ℕ) : Complex.I • Jm p q ∈ upq p q := by
  simpa using smul_I_Jm_mem p q 1

theorem commute_Jm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) : Commute X (Jm p q) := by
  rw [Jm_eq_diagonal]
  show X * _ = _ * X
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · rw [hX _ _ (by simp [sameBlock])]; simp
  · rw [hX _ _ (by simp [sameBlock])]; simp
  · simp

theorem commute_expt {p q : ℕ} (T : GrpData p q) (k : T.G) (hk : k ∈ T.Kset) (t : ℝ) :
    k * T.expt (t • (Complex.I • Jm p q)) = T.expt (t • (Complex.I • Jm p q)) * k := by
  apply T.emb.injective
  simp only [map_mul, Prod.mk.injEq]
  refine ⟨?_, mul_comm _ _⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, T.expt_cov _ (smul_I_Jm_mem p q t)]
  exact (((commute_Jm_of_isKC _ hk).smul_right Complex.I).smul_right t).exp_right.eq

theorem omAct_I_Jm_monomial (p q r s : ℕ) (α : Ln p q r s →₀ ℕ) :
    omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) (MvPolynomial.monomial α 1) =
    (Complex.I * ((α.degree : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2 : ℝ)) •
      MvPolynomial.monomial α 1 := by
  rw [omAct_apply, LinearMap.sum_apply]
  have : ∀ l : Ln p q r s, (∑ l', (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) l l' • omE l l') (MvPolynomial.monomial α 1) =
      (Complex.I * (((α l : ℕ) : ℂ) + 1 / 2)) • (MvPolynomial.monomial α 1 : Pol p q r s) := by
    intro l
    rw [Finset.sum_eq_single l]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Jm_eq_diagonal,
        Matrix.smul_apply, Matrix.diagonal_apply_eq, lineEquiv_isLeft, LinearMap.smul_apply]
      cases hl : linePos l
      · rw [omE_neg l hl, smul_smul]; congr 1; simp; ring
      · rw [omE_pos l hl, smul_smul]; congr 1; simp
    · intro l' _ hl'
      have : lineEquiv p q r s l ≠ lineEquiv p q r s l' :=
        fun h => hl' ((lineEquiv p q r s).injective h).symm
      simp [Jm_eq_diagonal, Matrix.diagonal_apply_ne _ this]
    · simp
  rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.sum_smul, ← Finset.mul_sum]
  congr 2
  rw [Finsupp.degree_eq_sum, Finset.sum_add_distrib]
  simp
  ring

theorem omAct_I_Jm_homog (p q r s d : ℕ) (P : Pol p q r s) (hP : P ∈ homog (Ix p q × Ix r s) d) :
    omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) P =
    (Complex.I * ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2 : ℝ)) • P := by
  have hP' : P.IsHomogeneous d := hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : α.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP' (MvPolynomial.mem_support_iff.1 hα)
  have : (MvPolynomial.monomial α (P.coeff α) : Pol p q r s) =
      P.coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial]; simp
  rw [this, map_smul, omAct_I_Jm_monomial, hd, smul_comm]

theorem inner_Om_eq_zero {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) (k : T0.G) (hk : k ∈ T0.Kset)
    {d d' : ℕ} (hd : d' ≠ d) (R : Pol p q r s) (hR : R ∈ homog (Ix p q × Ix r s) d')
    (P : Pol p q r s) (hP : P ∈ homog (Ix p q × Ix r s) d) :
    inner ℂ (F.ι R) (F.Om k (F.ι P)) = 0 := by
  refine inner_eq_zero_of_deriv (fun t => F.Om (T0.expt (t • (Complex.I • Jm _ _))))
    (fun t x => F.isom _ x) ?_ (F.Om k) ?_ _ _
    ((d' : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2)
    ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2) ?_ ?_ ?_
  · intro t x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T0.expt_add _ (I_Jm_mem _ _),
      add_neg_cancel, zero_smul, T0.expt_zero, map_one]
    rfl
  · intro t x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, commute_expt T0 k hk, map_mul]
    rfl
  · intro h
    exact hd (by exact_mod_cast add_right_cancel h)
  · have := F.der _ (I_Jm_mem _ _) R
    rwa [omAct_I_Jm_homog p q r s d' R hR, map_smul] at this
  · have := F.der _ (I_Jm_mem _ _) P
    rwa [omAct_I_Jm_homog p q r s d P hP, map_smul] at this

theorem one_mem_Kset {p q : ℕ} (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  rw [map_one, Units.val_one, Matrix.one_apply_ne]
  rintro rfl
  rcases a with a | a <;> simp [sameBlock] at hab

instance finiteDimensional_homog (σ : Type) [Finite σ] (d : ℕ) :
    FiniteDimensional ℂ (homog σ d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg σ ℂ d)

theorem Om_Kset_homog : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q := by
  intro p q r s T0 T1 T2 F k hk d P hP
  let E : Submodule ℂ F.H := (homog (Ix p q × Ix r s) d).map F.ι
  haveI : FiniteDimensional ℂ E := inferInstance
  obtain ⟨e, he, w', hw', hw⟩ := E.exists_add_mem_mem_orthogonal (F.Om k (F.ι P))
  obtain ⟨Q, hQ, rfl⟩ := he
  refine ⟨Q, hQ, ?_⟩
  have h0 : ∀ R, inner ℂ (F.ι R) w' = 0 := by
    intro R
    induction R using MvPolynomial.induction_on' with
    | add R S hR hS => rw [map_add (f := _), inner_add_left, hR, hS, add_zero]
    | monomial α c =>
      have hm : MvPolynomial.monomial α c ∈ homog (Ix p q × Ix r s) α.degree :=
        MvPolynomial.isHomogeneous_monomial c rfl
      by_cases h : α.degree = d
      · exact hw' _ ⟨_, h ▸ hm, rfl⟩
      · have h1 := inner_Om_eq_zero F k hk h _ hm P hP
        have h2 := inner_Om_eq_zero F 1 (one_mem_Kset T0) h _ hm Q hQ
        rw [map_one, ContinuousLinearMap.one_apply] at h2
        rwa [hw, inner_add_right, h2, zero_add] at h1
  have : w' = 0 := by
    have hc : IsClosed {x : F.H | inner ℂ x w' = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    have hsub : Set.range F.ι ⊆ {x : F.H | inner ℂ x w' = 0} := by
      rintro _ ⟨R, rfl⟩; exact h0 R
    have := hc.closure_subset_iff.2 hsub (F.dense w')
    exact inner_self_eq_zero.1 this
  rw [hw, this, add_zero]

end GlobalTheory.FockDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegreeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_Kset_preserves_homogeneous_degree : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q := by
  first | exact @GlobalTheory.FockDegree.Om_Kset_homog | exact GlobalTheory.FockDegree.Om_Kset_homog | (intros; apply GlobalTheory.FockDegree.Om_Kset_homog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimir
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimir
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowGen

variable {p q : ℕ}

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (x : V) : x ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x) ∧ ∀ a b, posC a b → act (Eab a b) x = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem genSub_stable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) (Z : Mat p q) : ∀ y ∈ genSub act S, act Z y ∈ genSub act S := by
  intro y hy
  rw [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem mem_genSub_self {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (u : V) : u ∈ genSub act {u} := by
  rw [genSub, Submodule.mem_sInf]
  exact fun N hN => hN.1 rfl

theorem genSub_le {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {u : V} {N : Submodule ℂ V} (hu : u ∈ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act {u} ≤ N :=
  sInf_le ⟨Set.singleton_subset_iff.2 hu, hN⟩

theorem gen_irred_adm {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hlie : IsLieAct act) (ip : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ x y, star (ip x y) = ip y x) (pos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (hadj : ∀ Z x y, ip (act Z x) y = ip x (act (adjZ Z) y))
    {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (u : V)
    (hfin : ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ u ∈ W ∧ KStable act W)
    (hu : u ∈ hwSub act (blattner lam))
    (hc : casimir act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u) :
    (∀ Q : Submodule ℂ V, Q ≤ genSub act {u} → (∀ Z, ∀ y ∈ Q, act Z y ∈ Q) → u ∉ Q → Q = ⊥) ∧
    ∀ μ, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ x ∈ genSub act {u}, x ∈ hwSub act μ → x ∈ S := by
  first
  | exact @_root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | (apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main ..)

def prodAct {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') :
    Mat p q →ₗ[ℂ] Module.End ℂ (V × V') where
  toFun Z := (a Z).prodMap (a' Z)
  map_add' Y Z := by ext <;> simp
  map_smul' c Z := by ext <;> simp

@[simp] theorem prodAct_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') (Z : Mat p q) (x : V × V') :
    prodAct a a' Z x = (a Z x.1, a' Z x.2) := rfl

def prodForm {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) : (V × V') →ₗ⋆[ℂ] (V × V') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => b x.1 y.1 + b' x.2 y.2)
    (fun x y z => by simp; ring) (fun c x y => by simp; ring) (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

theorem prodForm_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) (x y : V × V') :
    prodForm b b' x y = b x.1 y.1 + b' x.2 y.2 := rfl

theorem ip_nonneg (M : UGKMod p q) (x : M.M.V) : 0 ≤ (M.ip x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (M.pos x hx).le

theorem diag_irred {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V)
    (hu : u ∈ hwSub M.M.act (blattner lam)) (hu' : u' ∈ hwSub M'.M.act (blattner lam))
    (hc : casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u)
    (hc' : casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u') :
    ∀ Q : Submodule ℂ (M.M.V × M'.M.V), Q ≤ genSub (prodAct M.M.act M'.M.act) {(u, u')} →
      (∀ Z, ∀ y ∈ Q, prodAct M.M.act M'.M.act Z y ∈ Q) → (u, u') ∉ Q → Q = ⊥ := by
  refine (gen_irred_adm (prodAct M.M.act M'.M.act) ?_ (prodForm M.ip M'.ip) ?_ ?_ ?_ hl hg1 hg2 (u, u')
    ?_ ?_ ?_).1
  · intro X Y
    refine LinearMap.ext fun x => ?_
    simp only [prodAct_apply, M.M.lie X Y, M'.M.lie X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rfl
  · intro x y
    rw [prodForm_apply, prodForm_apply, star_add, M.herm, M'.herm]
  · intro x hx
    rw [prodForm_apply, Complex.add_re]
    have h1 := ip_nonneg M x.1
    have h2 := ip_nonneg M' x.2
    by_cases h : x.1 = 0
    · have := M'.pos x.2 fun h' => hx (Prod.ext h h')
      linarith
    · have := M.pos x.1 h
      linarith
  · intro Z x y
    simp only [prodForm_apply, prodAct_apply, M.adj, M'.adj]
  · obtain ⟨W, hW, huW, hst⟩ := M.M.kfin u
    obtain ⟨W', hW', huW', hst'⟩ := M'.M.kfin u'
    exact ⟨W.prod W', Module.Finite.of_fg (Submodule.FG.prod (Submodule.FG.of_finite) (Submodule.FG.of_finite)), ⟨huW, huW'⟩,
      fun X hX w hw => ⟨hst X hX _ hw.1, hst' X hX _ hw.2⟩⟩
  · rw [mem_hwSub] at hu hu' ⊢
    exact ⟨fun a => Prod.ext (hu.1 a) (hu'.1 a), fun a b h => Prod.ext (hu.2 a b h) (hu'.2 a b h)⟩
  · refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, ← hc]
      simp [casimir, Prod.fst_sum]
    · rw [Prod.smul_snd, ← hc']
      simp [casimir, Prod.snd_sum]

theorem gen_iso_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  intro _ _ p q lam hl hg1 hg2 M M' u u' hu hu' hc hc' hirr
  constructor
  · set N := genSub (prodAct M.M.act M'.M.act) {(u, u')} with hN
    have hNs := genSub_stable (prodAct M.M.act M'.M.act) {(u, u')}
    have hw : (u, u') ∈ N := mem_genSub_self _ _
    let π : N →ₗ[ℂ] M'.M.V := LinearMap.snd ℂ _ _ ∘ₗ N.subtype
    have hinj : Function.Injective π := by
      have h := diag_irred hl hg1 hg2 M M' u u' hu.2 hu'.2 hc hc' (N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _))
        inf_le_left (fun Z y hy => ⟨hNs Z y hy.1, by
          have h2 : y.2 = 0 := hy.2
          change M'.M.act Z y.2 = 0
          rw [h2, map_zero]⟩) (fun h => hu'.1 h.2)
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : M.M.V × M'.M.V) ∈ N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _) := ⟨x.2, hx⟩
      rw [h] at this
      exact Subtype.ext this
    have hsurj : Function.Surjective π := by
      rcases hirr.2 (LinearMap.range π) (by
        rintro Z _ ⟨x, rfl⟩
        exact ⟨⟨_, hNs Z x x.2⟩, rfl⟩) with h | h
      · have : u' ∈ LinearMap.range π := ⟨⟨_, hw⟩, rfl⟩
        rw [h] at this
        exact absurd this hu'.1
      · exact LinearMap.range_eq_top.1 h
    let φ := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
    let e : M'.M.V →ₗ[ℂ] M.M.V := (LinearMap.fst ℂ _ _ ∘ₗ N.subtype) ∘ₗ φ.symm.toLinearMap
    have he : ∀ x : N, e (x : M.M.V × M'.M.V).2 = (x : M.M.V × M'.M.V).1 := fun x =>
      congrArg (fun y : N => (y : M.M.V × M'.M.V).1) (φ.symm_apply_apply x)
    have heZ : ∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x) := by
      intro Z x
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 := he ⟨_, hNs Z y y.2⟩
      have h2 := he y
      exact h1.trans (congrArg (M.M.act Z) h2.symm)
    have heu : e u' = u := he ⟨_, hw⟩
    refine ⟨e, ?_, heZ, heu, le_antisymm ?_ (genSub_le ⟨u', heu⟩ ?_)⟩
    · rcases hirr.2 (LinearMap.ker e) (fun Z y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        rw [heZ, hy, map_zero]) with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · have : u' ∈ LinearMap.ker e := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, heu] at this
        exact absurd this hu.1
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 : N ≤ (genSub M.M.act {u}).comap (LinearMap.fst ℂ _ _) :=
        genSub_le (mem_genSub_self _ u) fun Z z hz => genSub_stable _ _ Z _ hz
      exact (he y).symm ▸ h1 y.2
    · rintro Z _ ⟨x, rfl⟩
      exact ⟨_, heZ Z x⟩
  · intro μ
    obtain ⟨S, hS, hS'⟩ := (gen_irred_adm M'.M.act M'.M.lie M'.ip M'.herm M'.pos M'.adj hl hg1 hg2 u'
      (M'.M.kfin u') hu'.2 hc').2 μ
    have htop : genSub M'.M.act {u'} = ⊤ := by
      rcases hirr.2 _ (genSub_stable M'.M.act {u'}) with h | h
      · have := mem_genSub_self M'.M.act u'
        rw [h] at this
        exact absurd this hu'.1
      · exact h
    exact Submodule.finiteDimensional_of_le (S₂ := S) fun x hx => hS' x (htop ▸ Submodule.mem_top) hx

end GlobalTheory.LowGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimirStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_iso_of_equal_casimir : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  first | exact @GlobalTheory.LowGen.gen_iso_of_lowest_type | exact GlobalTheory.LowGen.gen_iso_of_lowest_type | (intros; apply GlobalTheory.LowGen.gen_iso_of_lowest_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestType
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.LowestType

theorem two_le_of_not_sameBlock {p q : ℕ} {a b : Ix p q} (h : ¬ sameBlock a b) : 2 ≤ p + q := by
  unfold sameBlock at h
  rcases a with i | i <;> rcases b with j | j
  · exact (h trivial).elim
  · have hi := i.pos
    have hj := j.pos
    omega
  · have hi := i.pos
    have hj := j.pos
    omega
  · exact (h trivial).elim

theorem gapGt_of_cube {p q : ℕ} {lam : Ix p q → ℚ} (hg : GapGt lam (((p + q : ℕ) : ℝ) ^ 3))
    {h : ℝ} (hh : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) → h ≤ ((p + q : ℕ) : ℝ) ^ 3) : GapGt lam h := by
  unfold GapGt at hg ⊢
  intro a b hab
  have h2 : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast two_le_of_not_sameBlock hab
  exact lt_of_le_of_lt (hh h2) (hg a b hab)

private lemma cube_div_add_one_le_cube_and_sub_one_le {n : ℝ} (h2 : 2 ≤ n) : n ^ 3 / 24 + 1 ≤ n ^ 3 ∧ n - 1 ≤ n ^ 3 := by

  have hp : 0 ≤ n * (n - 1) * (n + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have e : n * (n - 1) * (n + 1) = n ^ 3 - n := by ring
  constructor <;> linarith

theorem embeds_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3) → ∀ (A B : UGKMod p q) (u : A.M.V) (v : B.M.V), IsHW A.M.act (blattner lam) u → IsHW B.M.act (blattner lam) v → casimir A.M.act u = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • u → casimir B.M.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v → IrrGK B.M → ∃ e : B.M.V →ₗ[ℂ] A.M.V, Function.Injective e ∧ e v = u ∧ ∀ Z x, e (B.M.act Z x) = A.M.act Z (e x) := by
  intro hQ7 hQ8 p q lam hlam hgap A B u v hu hv hcu hcv hirr

  have g1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).1)
  have g2 : GapGt lam (((p + q : ℕ) : ℝ) - 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).2)
  obtain ⟨⟨e, he, hcomm, heu, -⟩, -⟩ :=
    GlobalTheory.T.highest_weight_iso_of_equal_casimir hQ7 hQ8 p q lam hlam g1 g2 A B u v hu hv hcu hcv hirr
  exact ⟨e, he, heu, hcomm⟩

end GlobalTheory.LowestType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestTypeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_intertwiner_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3) → ∀ (A B : UGKMod p q) (u : A.M.V) (v : B.M.V), IsHW A.M.act (blattner lam) u → IsHW B.M.act (blattner lam) v → casimir A.M.act u = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • u → casimir B.M.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v → IrrGK B.M → ∃ e : B.M.V →ₗ[ℂ] A.M.V, Function.Injective e ∧ e v = u ∧ ∀ Z x, e (B.M.act Z x) = A.M.act Z (e x) := by
  first | exact @GlobalTheory.LowestType.embeds_of_lowest_type | exact GlobalTheory.LowestType.embeds_of_lowest_type | (intros; apply GlobalTheory.LowestType.embeds_of_lowest_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator
namespace GlobalTheory.CommonDenominatorLemma

open NumberField

theorem exists_common_denominator {E : Type} [inst : Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : Submodule.FG L) :
    ∃ (b : NumberField.RingOfIntegers E), b ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ x ∈ L, ∀ (i : Fin N), ∃ (u : NumberField.RingOfIntegers E), (↑u : E) = (↑b : E) * x i := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin N → E) × Fin N =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let b : NumberField.RingOfIntegers E :=
    ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ((z p).2 : NumberField.RingOfIntegers E)
  refine ⟨b, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, i) ∈ s ×ˢ (Finset.univ : Finset (Fin N)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ i⟩)
    refine ⟨e * (z (g, i)).1, ?_⟩
    have h := hz (g, i)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show b = ((z (g, i)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro i
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    obtain ⟨c2, h2⟩ := hy i
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SelfDualIdDecomp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_range (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  have h : IsIntegral ℤ (star (a : E)) := by
    exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨star (a : E), h⟩, rfl⟩

theorem exists_den {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∀ x ∈ L, ∀ i, ∃ u : 𝓞 E, (u : E) = (b : E) * x i := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator ..)

theorem exists_extension {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L)
    (φ : L →ₗ[𝓞 E] 𝓞 E) : ∃ u ∈ L, ∀ x (hx : x ∈ L), stdH E N u x = (φ ⟨x, hx⟩ : E) := by
  classical
  obtain ⟨hfg, -, hdual⟩ := hL
  obtain ⟨b, hb0, hb⟩ := exists_den L hfg
  obtain ⟨c', hc'⟩ := star_mem_range b
  have hbE : (b : E) ≠ 0 := by
    intro h; apply hb0; exact RingOfIntegers.coe_injective (by simpa using h)
  have hc0 : star (b : E) ≠ 0 := star_ne_zero.2 hbE
  have hce : ∀ i, (Pi.single i (star (b : E)) : Fin N → E) ∈ L := by
    intro i
    rw [hdual]
    intro x hx
    obtain ⟨u, hu⟩ := hb x hx i
    have h1 : stdH E N x (Pi.single i (star (b : E))) = star (u : E) := by
      rw [hu, star_mul]
      simp [stdH, Pi.single_apply]
    rw [h1]; exact star_mem_range u
  let w : Fin N → E := fun i => (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) / star (b : E)
  have hw : ∀ x (hx : x ∈ L), (φ ⟨x, hx⟩ : E) = ∑ i, w i * x i := by
    intro x hx
    choose ub hub using hb x hx
    have h1 : (b * c') • (⟨x, hx⟩ : L) = ∑ i, ub i • (⟨Pi.single i (star (b : E)), hce i⟩ : L) := by
      apply Subtype.ext; funext j
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := hub j
      simp only [map_mul, hc']
      rw [show (algebraMap (𝓞 E) E) (ub j) = (b : E) * x j from this]
      ring
    have h2 := congrArg (fun z => ((φ z : 𝓞 E) : E)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, smul_eq_mul] at h2
    push_cast at h2
    apply mul_left_cancel₀ (mul_ne_zero hbE hc0)
    have h3 : (b : E) * star (b : E) * (φ ⟨x, hx⟩ : E) =
        ∑ i, ((ub i : 𝓞 E) : E) * (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) := by
      rw [← h2, ← hc']
    rw [h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hub i]
    simp only [w]
    first | (field_simp; ring) | field_simp
  refine ⟨fun i => star (w i), ?_, ?_⟩
  · rw [hdual]
    intro y hy
    have : stdH E N y (fun i => star (w i)) = star (φ ⟨y, hy⟩ : E) := by
      rw [hw y hy, star_sum]
      simp [stdH, star_mul, mul_comm]
    rw [this]; exact star_mem_range _
  · intro x hx
    rw [hw x hx]
    simp [stdH]

theorem exists_decomp {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L) :
    ∃ (r : ℕ) (s u : Fin r → Fin N → E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  classical
  have hspan := hL.2.1
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  choose u hu hux using fun k : Fin m => exists_extension L hL ((LinearMap.proj k) ∘ₗ g)
  refine ⟨m, fun k => (f (Pi.single k 1) : Fin N → E), u, fun k => (f _).2, hu, ?_⟩
  have hrec : ∀ y : L, (y : Fin N → E) = ∑ k, ((g y k : 𝓞 E) : E) • (f (Pi.single k 1) : Fin N → E) := by
    intro y
    have h1 : f (g y) = y := LinearMap.congr_fun hfg y
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← h1, pi_eq_sum_univ' (g y), map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hspan
  rintro x hx
  rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
  funext i
  have e1 : x i = ∑ k, ((g ⟨x, hx⟩ k : 𝓞 E) : E) * (f (Pi.single k 1) : Fin N → E) i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : L) : Fin N → E) from rfl, hrec ⟨x, hx⟩]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun k _ => Algebra.smul_def _ _
  rw [e1]
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, vecMulVec_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hux k x hx
  simp only [stdH, LinearMap.comp_apply, LinearMap.proj_apply] at this
  rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply]
  ring

theorem iddecomp : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  intro D N L hL
  exact exists_decomp L hL

end GlobalTheory.SelfDualIdDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_resolution_of_identity : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧ ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  first | exact @GlobalTheory.SelfDualIdDecomp.iddecomp | exact GlobalTheory.SelfDualIdDecomp.iddecomp | (intros; apply GlobalTheory.SelfDualIdDecomp.iddecomp <;> assumption)
end
end

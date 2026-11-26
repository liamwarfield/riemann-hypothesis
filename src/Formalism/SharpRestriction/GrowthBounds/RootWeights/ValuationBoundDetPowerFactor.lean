module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IdentityEvaluationGenericMatrix
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem mapRingHom_laurent_C' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  first
  | simp [LaurentPolynomial.C_apply, AddMonoidAlgebra.mapRingHom_single]
  | simp [LaurentPolynomial.C_apply, Finsupp.mapRange_single]
  | (ext k; simp [LaurentPolynomial.C_apply, Finsupp.single_apply]; split_ifs <;> simp)
  | (ext k; simp [LaurentPolynomial.C_apply, AddMonoidAlgebra.coeff_single]; split_ifs <;> simp)
  | rfl

private theorem mapRingHom_laurent_T {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (k : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T k : LaurentPolynomial A) = LaurentPolynomial.T k := by
  first
  | (simp [LaurentPolynomial.T, -LaurentPolynomial.single_eq_C_mul_T]; done)
  | (ext j
     simp [LaurentPolynomial.T, -LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]
     split_ifs <;> simp; done)
  | (ext j
     simp [LaurentPolynomial.T, -LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_apply]
     split_ifs <;> simp; done)
  | (ext j
     simp [LaurentPolynomial.T_apply]
     split_ifs <;> simp; done)
  | (ext j
     simp [LaurentPolynomial.coeff_T]
     split_ifs <;> simp; done)

theorem mul_Psi_support {σ A R' : Type*} [CommRing A] [CommRing R'] (φ0 : A →+* R') (x : σ → R')
    (P : MvPolynomial σ (LaurentPolynomial A)) :
    ((eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ φ0) (fun v => LaurentPolynomial.C (x v))) P).coeff.support ⊆
      mul_degs P := by
  have key : (eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ φ0) (fun v => LaurentPolynomial.C (x v)) :
      MvPolynomial σ (LaurentPolynomial A) →+* LaurentPolynomial R') =
      (AddMonoidAlgebra.mapRingHom ℤ (eval₂Hom φ0 x)).comp (mul_Phi σ A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      ext k
      simp [mul_Phi]
    · intro i
      simp [mul_Phi, mapRingHom_laurent_C']
  rw [key, mul_degs_eq]
  intro k hk
  rw [Finsupp.mem_support_iff] at hk ⊢
  intro h
  apply hk
  simp [h]

def identityEvaluation (R : Type*) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R →+* R :=
  MvPolynomial.eval (fun ab => if ab.1 = ab.2 then (1 : R) else 0)

theorem identity_evaluation_generic_matrix (R : Type*) [CommRing R] (n : ℕ) : (identityEvaluation R n).mapMatrix (genMat R n) = 1 := by
  ext a b
  simp [identityEvaluation, genMat, Matrix.one_apply]

theorem identity_evaluation_generic_det (R : Type*) [CommRing R] (n : ℕ) : identityEvaluation R n (genMat R n).det = 1 := by
  rw [RingHom.map_det, identity_evaluation_generic_matrix, Matrix.det_one]

def mul_ev (R : Type*) [CommRing R] (n : ℕ) : GLCoord R n →+* R :=
  IsLocalization.Away.lift (genMat R n).det (g := identityEvaluation R n) (by rw [identity_evaluation_generic_det]; exact isUnit_one)

theorem mul_ev_alg (R : Type*) [CommRing R] (n : ℕ) (a : MvPolynomial (Fin n × Fin n) R) :
    mul_ev R n (algebraMap _ (GLCoord R n) a) = identityEvaluation R n a := by
  first
  | simp [mul_ev]
  | exact IsLocalization.Away.lift_eq _ _ a
  | (unfold mul_ev; exact IsLocalization.lift_eq _ a)

theorem mul_ev_inv (R : Type*) [CommRing R] (n : ℕ) :
    mul_ev R n (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) = 1 := by
  have h := congrArg (mul_ev R n)
    (IsLocalization.Away.mul_invSelf (S := GLCoord R n) (genMat R n).det)
  rw [map_mul, map_one, mul_ev_alg, identity_evaluation_generic_det, one_mul] at h
  exact h

def mul_ph (R : Type*) [CommRing R] (n : ℕ) : GLLaurent R n →+* LaurentPolynomial R :=
  AddMonoidAlgebra.mapRingHom ℤ (mul_ev R n)

theorem mul_ph_C (R : Type*) [CommRing R] (n : ℕ) (a : GLCoord R n) :
    mul_ph R n (LaurentPolynomial.C a) = LaurentPolynomial.C (mul_ev R n a) := by
  simp only [mul_ph]
  exact mapRingHom_laurent_C' _ _

theorem mul_ph_T (R : Type*) [CommRing R] (n : ℕ) (k : ℤ) :
    mul_ph R n (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  simp only [mul_ph]
  exact mapRingHom_laurent_T _ _

theorem mul_ph_gL (R : Type*) [CommRing R] (n : ℕ) : (mul_ph R n).mapMatrix (gL R n) = 1 := by
  ext a b
  simp only [gL, RingHom.mapMatrix_apply, Matrix.map_apply, genMat, Matrix.of_apply, mul_ph_C,
    mul_ev_alg, identityEvaluation, MvPolynomial.eval_X, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_ph_gLinv (R : Type*) [CommRing R] (n : ℕ) : (mul_ph R n).mapMatrix (gLinv R n) = 1 := by
  have hadj : (identityEvaluation R n).mapMatrix (genMat R n).adjugate = 1 := by
    rw [RingHom.map_adjugate, identity_evaluation_generic_matrix, Matrix.adjugate_one]
  ext a b
  have hab := congrFun (congrFun hadj a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hab
  simp only [gLinv, RingHom.mapMatrix_apply, Matrix.map_apply, mul_ph_C, map_mul, mul_ev_inv,
    mul_ev_alg, one_mul, hab, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_ph_twist (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    (mul_ph R n).mapMatrix (twistMat R n j k) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T k else 1) := by
  rw [twistMat, map_mul, map_mul, mul_ph_gL, mul_ph_gLinv, one_mul, mul_one]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [mul_ph_T]

open Classical in
theorem mul_valS_detA_le {R : Type} [Field R] {ι : Type} (LL : Letters ι) {r : ℕ} [NeZero r]
    (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, LL.vec (A l) = true) (S' : Set ι) :
    valS LL S' (detA (R := R) A) ≤ ((1 : ℤ) : WithTop ℤ) := by
  set Ψ : MvPolynomial (ι × Fin r) (GLLaurent R r) →+* LaurentPolynomial R :=
    eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ (mul_ev R r))
      (fun v => LaurentPolynomial.C (if v.1 = A v.2 then (1 : R) else 0)) with hΨ
  have hC : ∀ b, Ψ (C b) = mul_ph R r b := fun b => by rw [hΨ, coe_eval₂Hom, eval₂_C]; rfl
  have hX : ∀ i b, Ψ (X (A i, b)) = if i = b then 1 else 0 := by
    intro i b
    rw [hΨ, coe_eval₂Hom, eval₂_X]
    by_cases h : i = b
    · simp [h]
    · have : A i ≠ A b := fun h' => h (hA h')
      simp [h, this]
  have key : Ψ (twistSub LL S' (lastIdx r) (detA (R := R) A)) =
      (Matrix.diagonal (fun i : Fin r =>
        if A i ∈ S' ∧ i = lastIdx r then (LaurentPolynomial.T 1 : LaurentPolynomial R) else 1)).det := by
    rw [detA, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    have ht := fun b => congrFun (congrFun (mul_ph_twist R r (lastIdx r) 1) b) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at ht
    by_cases hS : A i ∈ S'
    · have : twistSub LL S' (lastIdx r) (X (A i, j) : MvPolynomial (ι × Fin r) R) =
          ∑ b : Fin r, C (twistMat R r (lastIdx r) 1 b j) * X (A i, b) := by
        simp [twistSub, hS, hv]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      simp only [map_mul, hC, hX, ht]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases hij : i = j
      · subst hij; simp [hS]
      · simp [hij]
    · have : twistSub LL S' (lastIdx r) (X (A i, j) : MvPolynomial (ι × Fin r) R) = X (A i, j) := by
        simp [twistSub, hS]
      rw [this, hX]
      by_cases hij : i = j
      · subst hij; simp [hS]
      · simp [hij]
  rw [Matrix.det_diagonal, Finset.prod_eq_single (lastIdx r) (fun b _ hb => by simp [hb]) (by simp)] at key
  have hsub := mul_Psi_support (mul_ev R r) (fun v : ι × Fin r => if v.1 = A v.2 then (1 : R) else 0)
    (twistSub LL S' (lastIdx r) (detA (R := R) A))
  by_cases hS : A (lastIdx r) ∈ S'
  · have hm : (1 : ℤ) ∈ sDegs LL S' (lastIdx r) (detA (R := R) A) := by
      apply hsub
      rw [← hΨ, key]
      simp [hS]
    exact Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hm
  · have hm : (0 : ℤ) ∈ sDegs LL S' (lastIdx r) (detA (R := R) A) := by
      apply hsub
      rw [← hΨ, key]
      simp [hS]
    refine (Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hm).trans ?_
    exact_mod_cast (zero_le_one : (0 : ℤ) ≤ 1)

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem sDegs_eq_support_mul_Phi_twistSub {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (j : Fin n) (H : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j H = (mul_Phi _ _ (twistSub LL S j H)).coeff.support := by
  ext k
  simp only [sDegs, Finset.mem_biUnion, Finsupp.mem_support_iff, MvPolynomial.mem_support_iff]
  constructor
  · rintro ⟨m, -, hk⟩ h0
    apply hk
    rw [← mul_Phi_coeff, h0, MvPolynomial.coeff_zero]
    rfl
  · intro hk
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
    rw [mul_Phi_coeff] at hm
    refine ⟨m, fun h => hm ?_, hm⟩
    rw [h]
    rfl

theorem mul_valS_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
  rw [valS, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_lam1S_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
  rw [lam1S, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  rw [mul_valS_eq LL S F, mul_valS_eq LL S G, mul_valS_eq LL S (F + G), map_add (f := _), map_add (f := _)]
  refine le_trans ?_ (Finset.inf_mono Finsupp.support_add)
  rw [Finset.inf_union]
  exact le_rfl

theorem mul_lam1S_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  rw [mul_lam1S_eq LL S F, mul_lam1S_eq LL S G, mul_lam1S_eq LL S (F + G), map_add (f := _), map_add (f := _)]
  refine le_trans (Finset.sup_mono Finsupp.support_add) ?_
  rw [Finset.sup_union]
  exact le_rfl

theorem valuation_bound_det_power_factor (R : Type) [Field R] (ι : Type) (LL : Letters ι) (r : ℕ) [NeZero r]
    (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, LL.vec (A l) = true)
    (G H : MvPolynomial (ι × Fin r) R) (m : ℕ) (hG : G = (detA (R := R) A) ^ m * H) (S' : Set ι) :
    valS LL S' G ≤ valS LL S' H + ((m : ℤ) : WithTop ℤ) := by
  have hd := mul_valS_detA_le (R := R) LL A hA hv S'
  have hpow : ∀ k : ℕ, valS LL S' ((detA (R := R) A) ^ (k + 1)) ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [pow_succ, mul_valS_mul]
      calc valS LL S' ((detA (R := R) A) ^ (k + 1)) + valS LL S' (detA (R := R) A)
          ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) := add_le_add ih hd
        _ = (((k + 1 + 1 : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
  subst hG
  rcases m with _ | k
  · simp
  · rw [mul_valS_mul, add_comm (valS LL S' _) (valS LL S' H)]
    exact add_le_add (le_refl _) (hpow k)

def GlOperatorsFormRepresentation : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

theorem prvE_of_gl_operators_form_representation (D : Formalism.BasicNotions.D7) (h : GlOperatorsFormRepresentation) : ConclusionE D := by
  intro R _ ι _ LL r _ S A hA hAS
  exact ⟨h R ι LL r S A hA hAS,
    fun G H m hG S' => valuation_bound_det_power_factor R ι LL r A hA (fun l => (hAS l).2) G H m hG S'⟩

def GeneratedModuleWeightDescription : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι),
    (∀ (G : MvPolynomial (ι × Fin n) R) (th : ℤ), ((th : WithTop ℤ) ≤ valS LL S G ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), th ≤ mu (lastIdx n))) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (M : ℤ), (lam1S LL S G ≤ (M : WithBot ℤ) ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), mu 0 ≤ M))

theorem valuations_additive_of_generated_weight_description (D : Formalism.BasicNotions.D7) (h : GeneratedModuleWeightDescription) : ValuationsAdditive D := by
  intro R _ ι _ LL n _ S
  exact ⟨mul_valS_mul LL S, mul_valS_add LL S, mul_lam1S_mul LL S, mul_lam1S_add LL S,
    (h R ι LL n S).1, (h R ι LL n S).2⟩

end Formalism.MainNotions.G.GLWeightTheory

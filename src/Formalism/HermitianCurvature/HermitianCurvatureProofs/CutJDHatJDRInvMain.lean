module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvCov
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_right (X S x : Mat k r) (f : Mat k r → E) (h1 : S * S⁻¹ = 1) (h2 : S⁻¹ * S = 1) :
    RdV X (fun y => f (y * S)) x = RdV (S⁻¹ * X * S) f (x * S) := by
  unfold RdV
  congr 1
  funext t
  have e1 : ((t : ℂ) • (S⁻¹ * X * S)) = S⁻¹ * ((t : ℂ) • X) * S := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, Formalism.QuantumDeterminants.ioh_exp_conj S⁻¹ S _ h1 h2]
  show f (x * NormedSpace.exp ((t : ℂ) • X) * S) = f (x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S))
  congr 1
  calc x * NormedSpace.exp ((t : ℂ) • X) * S
      = x * (S * S⁻¹) * NormedSpace.exp ((t : ℂ) • X) * S := by rw [h1, Matrix.mul_one]
    _ = x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S) := by simp only [Matrix.mul_assoc]

theorem rdV_left (X A x : Mat k r) (f : Mat k r → E) :
    RdV X (fun y => f (A * y)) x = RdV X f (A * x) := by
  unfold RdV
  simp only [Matrix.mul_assoc]

theorem EZ_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) (a b : Fin (2 * r + k + 1)) (x : Mat k r) :
    EZ (Msg k r a b) (fun y => f (y * S)) x = EZ (Mc S a b) f (x * S) := by
  have h := congrFun (congrFun (congrFun (congrFun (EHc_eq_LT (E := E) S hS) a) b) f) (x * S)
  refine Eq.trans ?_ h
  obtain ⟨h1, h2⟩ := gv_inv hS
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x +
      Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x = _
  rw [rdV_right _ _ _ _ h1 h2, rdV_right _ _ _ _ h1 h2]
  rfl

theorem EZ_left (A : Mat k r) (Z : Mat k r) (f : Mat k r → E) (x : Mat k r) :
    EZ Z (fun y => f (A * y)) x = EZ Z f (A * x) := by
  unfold EZ
  rw [rdV_left, rdV_left]

theorem fold_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold (Msg k r) ts (fun y => f (y * S)) = fun x => fold (Mc S) ts f (x * S)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_right S hS f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_right S hS (fold (Mc S) ts f) t.2.1 t.2.2 x

theorem fold_left (A : Mat k r) (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold M ts (fun y => f (A * y)) = fun x => fold M ts f (A * x)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_left A M f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_left A (M t.2.1 t.2.2) (fold M ts f) x

theorem qminor_left {t : ℕ} (A : Mat k r) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (x : Mat k r) :
    qminorOp (Q.EH k r) a b u (fun y => f (A * y)) x = qminorOp (Q.EH k r) a b u f (A * x) := by
  rw [qm_eq, qm_eq]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [PP]
  rw [fold_left]

theorem qminor_right_all (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
        ((∏ j, (S⁻¹) (c j) (a j)) * ∏ j, S (b j) (d j)) • qminorOp (Q.EH k r) c d u f (x * S) := by
  set P := S⁻¹
  set A : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun c => ∏ j, P (c j) (a j) with hA
  set B : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun d => ∏ j, S (b j) (d j) with hB
  have step : ∀ σ : Equiv.Perm (Fin t),
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S) =
        ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) := by
    intro σ
    rw [expandM S hS t _ f (x * S) hx hloc]
    refine (Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun c => ?_)).symm
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    congr 1
    · simp only [Function.comp_apply, hA, hB]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact (Equiv.prod_comp σ (fun j => P (c j) (a j))).symm
  rw [qm_eq]
  simp only [PP]
  simp_rw [fold_right S hS f]
  rw [show (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S)) =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) from
    Finset.sum_congr rfl (fun σ _ => by rw [step σ])]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [qm_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open Classical in
theorem sum_sortM {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ} (F : (Fin t → Fin N) → M)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)), F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
      (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C := by
  rw [Formalism.FourierDecayAlt.P.CutMP.CapInv.groupingM (fun i : Fin N => (i : ℕ)) Fin.val_injective F hF hF0 W,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  by_cases h : StrictMono C
  · rw [if_pos h, if_pos (show StrictMono fun l => ((C l : Fin N) : ℕ) from h)]
  · rw [if_neg h, if_neg (show ¬ StrictMono fun l => ((C l : Fin N) : ℕ) from h)]


open Classical in
theorem collapse2 {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ}
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (A B : (Fin t → Fin N) → ℂ)
    (hr : ∀ c d (τ : Equiv.Perm (Fin t)), D (c ∘ τ) d = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hr0 : ∀ c d, ¬ Function.Injective c → D c d = 0)
    (hc : ∀ c d (τ : Equiv.Perm (Fin t)), D c (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hc0 : ∀ c d, ¬ Function.Injective d → D c d = 0) :
    ∑ c, ∑ d, (A c * B d) • D c d =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
          ((∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * A (c ∘ σ)) *
            (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ))) • D c d := by
  set S := Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C)
  set Y : (Fin t → Fin N) → M := fun c =>
    ∑ d ∈ S, (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ)) • D c d with hY
  have inner : ∀ c, ∑ d, (A c * B d) • D c d = A c • Y c := by
    intro c
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_sortM (D c) (hc c) (hc0 c) B]
  simp_rw [inner]
  rw [sum_sortM Y (fun c τ => by simp only [hY, hr, smul_comm _ (((Equiv.Perm.sign τ : ℤ) : ℂ)), Finset.smul_sum])
    (fun c hcn => by simp [hY, hr0 c _ hcn]) A]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [hY, Finset.smul_sum, smul_smul]

theorem det_rows {t N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (c a : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P ((c ∘ σ) j) (a j) = (P.submatrix c a).det := by
  rw [Matrix.det_apply']
  rfl

theorem det_cols {t N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (b d : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, S (b j) ((d ∘ σ) j) = (S.submatrix b d).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


open Classical in
theorem qminor_right (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
          ((S⁻¹.submatrix c a).det * (S.submatrix b d).det) • qminorOp (Q.EH k r) c d u f (x * S) := by
  rw [qminor_right_all S hS a b u f x hx hloc]
  rw [collapse2 (fun c d => qminorOp (Q.EH k r) c d u f (x * S)) (fun c => ∏ j, (S⁻¹) (c j) (a j))
    (fun d => ∏ j, S (b j) (d j))
    (fun c d τ => skewRow c d u f (x * S) τ) (fun c d hc => row_zero c d u f (x * S) hc)
    (fun c d τ => skewCol c u f (x * S) hx hloc d τ) (fun c d hd => col_zero c d u f (x * S) hx hloc hd)]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  rw [det_rows, det_cols]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov
end
end

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

theorem assembleP {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι] {t N : ℕ}
    (T : Finset (Fin t → Fin N)) (al : ι → ℂ) (R : ι → Fin t → Fin N) (be be' : (Fin t → Fin N) → ℂ)
    (pc : (Fin t → Fin N) → ι → ℂ) (qd : (Fin t → Fin N) → (Fin t → Fin N) → ℂ)
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (lam mu : ℂ) (hlm : lam * mu = 1)
    (hA : ∀ X : (Fin t → Fin N) → M, ∑ c ∈ T, (∑ i, al i * pc c i) • X c = lam • ∑ i, al i • X (R i))
    (hB : ∀ d, ∑ J ∈ T, be J * qd J d = mu * be' d) :
    ∑ i, ∑ J ∈ T, (al i * be J) • ∑ c ∈ T, ∑ d ∈ T, (pc c i * qd J d) • D c d =
      ∑ i, ∑ J ∈ T, (al i * be' J) • D (R i) J := by
  have e1 : ∑ i, ∑ J ∈ T, (al i * be J) • ∑ c ∈ T, ∑ d ∈ T, (pc c i * qd J d) • D c d =
      ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * pc c i * (be J * qd J d)) • D c d := by
    simp only [Finset.smul_sum, smul_smul]
    calc ∑ i, ∑ J ∈ T, ∑ c ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d
        = ∑ i, ∑ c ∈ T, ∑ J ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ c ∈ T, ∑ i, ∑ J ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d := Finset.sum_comm
      _ = ∑ c ∈ T, ∑ i, ∑ d ∈ T, ∑ J ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
      _ = ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))))
          congr 1
          ring
  have e2 : ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * pc c i * (be J * qd J d)) • D c d =
      ∑ c ∈ T, (∑ i, al i * pc c i) • ∑ d ∈ T, (∑ J ∈ T, be J * qd J d) • D c d := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [smul_smul, Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp_rw [hB]
  rw [hA (fun c => ∑ d ∈ T, (mu * be' d) • D c d)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))
  congr 1
  linear_combination (al i * be' J) * hlm

theorem assembleM {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι] {t N : ℕ}
    (T : Finset (Fin t → Fin N)) (bb : ι → ℂ) (C : ι → Fin t → Fin N) (al al' : (Fin t → Fin N) → ℂ)
    (pc : (Fin t → Fin N) → (Fin t → Fin N) → ℂ) (qd : ι → (Fin t → Fin N) → ℂ)
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (lam mu : ℂ) (hlm : lam * mu = 1)
    (hA : ∀ c, ∑ J ∈ T, al J * pc c J = lam * al' c)
    (hB : ∀ X : (Fin t → Fin N) → M, ∑ d ∈ T, (∑ i, bb i * qd i d) • X d = mu • ∑ i, bb i • X (C i)) :
    ∑ i, ∑ J ∈ T, (bb i * al J) • ∑ c ∈ T, ∑ d ∈ T, (pc c J * qd i d) • D c d =
      ∑ i, ∑ J ∈ T, (bb i * al' J) • D J (C i) := by
  have e1 : ∑ i, ∑ J ∈ T, (bb i * al J) • ∑ c ∈ T, ∑ d ∈ T, (pc c J * qd i d) • D c d =
      ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * qd i d * (al J * pc c J)) • D c d := by
    simp only [Finset.smul_sum, smul_smul]
    calc ∑ i, ∑ J ∈ T, ∑ c ∈ T, ∑ d ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d
        = ∑ i, ∑ c ∈ T, ∑ J ∈ T, ∑ d ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ i, ∑ c ∈ T, ∑ d ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
      _ = ∑ i, ∑ d ∈ T, ∑ c ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ d ∈ T, ∑ i, ∑ c ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d := Finset.sum_comm
      _ = ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))))
          congr 1
          ring
  have e2 : ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * qd i d * (al J * pc c J)) • D c d =
      ∑ d ∈ T, (∑ i, bb i * qd i d) • ∑ c ∈ T, (∑ J ∈ T, al J * pc c J) • D c d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [smul_smul, Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp_rw [hA]
  rw [hB (fun d => ∑ c ∈ T, (lam * al' c) • D c d)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))
  congr 1
  linear_combination (bb i * al' J) * hlm

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem one_GV : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem left_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r := by
  have := WeylGroupFacts.uh_inv (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)
  rwa [Matrix.mul_inv_rev] at this

theorem rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (G : Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D p G = fun x => Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (G ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
  rw [Formalism.FourierDecayAlt.P.JFxB.rho_eq_trn']
  funext x
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.trn, Matrix.mul_assoc]

open Classical in
theorem jset_eq : (Finset.univ.filter fun C : Fin (r + k) → Fin (2 * r + k + 1) => StrictMono C) = jSetR k r := rfl

theorem qminor_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ((r + k : ℕ) : ℕ∞) (GV k r) F) {g : Mat k r} (hg : g ∈ GV k r)
    (a b : Fin (r + k) → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (∑ c ∈ jSetR k r, ∑ d ∈ jSetR k r,
        (((Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹.submatrix c a).det *
          ((Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r).submatrix b d).det) •
        qminorOp (Q.EH k r) c d u F
          ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hAG := left_GV D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ GV k r := WeylGroupFacts.uh_mul hg hSG
  have hG' : CkOn ((r + k : ℕ) : ℕ∞) (GV k r) (fun x =>
      F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
    have := Formalism.FourierDecayAlt.P.B5.ckOn_translate hF hAG hSG
    have e : (fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) =
        fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
      funext x; simp only [Matrix.mul_assoc]
    rwa [e] at this
  have hFa : Loc ((r + k : ℕ) : ℕ∞) (fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y))
      (g * (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
    have := Formalism.FourierDecayAlt.P.B5.ckOn_translate hF hAG (one_GV (k := k) (r := r))
    have e : (fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * 1)) =
        fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y) := by
      funext x; simp only [Matrix.mul_one]
    rw [e] at this
    exact this _ hgS
  rw [rho_eq D p F]
  have h1 : qminorOp (Q.EH k r) a b u (fun x => Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1))))) g =
      Formalism.FourierDecayAlt.P.JFxB.Lq D p (qminorOp (Q.EH k r) a b u (fun x =>
        F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) g) :=
    Formalism.FourierDecayAlt.P.CutMP.CapInv.post_qm (Formalism.FourierDecayAlt.P.JFxB.Lq D p) _ hG' a b u hg
  rw [h1]
  congr 1
  have h2 := qminor_right (Matrix.of p.2.2 * Matrix.of p.2.1) hSG a b u
    (fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y)) g hgS hFa
  rw [jset_eq] at h2
  refine h2.trans (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_)))
  rw [qminor_left]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B RInvCov

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jDRInvFn_of (hA : RInvAlphaP) (hB : RInvBetaP) (hBL : RInvBetaLeftP) : JDRInvFn := by
  intro k r Wp Wq _ _ _ _ D Y p hp F hF g hg
  have hgG : g ∈ B.GV k r := hg.1
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r) ∈ B.GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ B.GV k r := WeylGroupFacts.uh_mul hgG hSG
  rw [rho_eq D p (rhatOp k r D.z D.z' Y F)]
  show rhatOp k r D.z D.z' Y (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p (rhatOp k r D.z D.z' Y F
    ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
  simp only [rhatOp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => by
    rw [qminor_rho D hp hF hgG]))) ?_
  have key := assembleP (M := Wq →L[ℂ] Wp) (jSetR k r) (alP k r D.z') (rowsR k r)
    (fun J => beJ k r D.z g J)
    (fun J => beJ k r D.z ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))) J)
    (fun c i => (((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).submatrix c (rowsR k r i)).det)
    (fun J d => ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).submatrix J d).det)
    (fun c d => qminorOp (Q.EH k r) c d (Q.uC k r 0 Y) F
      ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
    ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).det (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).det
    (by rw [← Matrix.det_mul, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hSG).2, Matrix.det_one])
    (fun X => hA k r D.z' (Matrix.of p.2.1) (Matrix.of p.2.2) D.z'_mem hp.2.2.1 hp.2.2.2 (Wq →L[ℂ] Wp) X)
    (fun d => by
      rw [hB k r D.z g _ hgG hSG d, hBL k r D.z _ _ _ D.z_mem hp.1 hp.2.1 hgS d])
  have key2 := congrArg (Formalism.FourierDecayAlt.P.JFxB.Lq D p) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at key2 ⊢
  refine Eq.trans ?_ (key2.trans ?_)
  · rfl
  · rfl

theorem jDRInvFnM_of (hA : RInvAlphaM) (hAL : RInvAlphaLeftM) (hB : RInvBetaM) : JDRInvFnM := by
  intro k r Wp Wq _ _ _ _ D Y p hp F hF g hg
  have hgG : g ∈ B.GV k r := hg.1
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r) ∈ B.GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ B.GV k r := WeylGroupFacts.uh_mul hgG hSG
  rw [rho_eq D p (rvhatOp k r D.z D.z' Y F)]
  show rvhatOp k r D.z D.z' Y (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p (rvhatOp k r D.z D.z' Y F
    ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
  simp only [rvhatOp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => by
    rw [qminor_rho D hp hF hgG]))) ?_
  have key := assembleM (M := Wq →L[ℂ] Wp) (jSetR k r) (beM k r D.z') (colsV k r)
    (fun J => alJ k r D.z g J)
    (fun J => alJ k r D.z ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))) J)
    (fun c J => (((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).submatrix c J).det)
    (fun t d => ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).submatrix (colsV k r t) d).det)
    (fun c d => qminorOp (Q.EH k r) c d (Q.uC k r (Fin.last r) Y - 1) F
      ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
    ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).det (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).det
    (by rw [← Matrix.det_mul, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hSG).2, Matrix.det_one])
    (fun c => by
      rw [hA k r D.z g _ hgG hSG c, hAL k r D.z _ _ _ D.z_mem hp.1 hp.2.1 hgS c])
    (fun X => hB k r D.z' (Matrix.of p.2.1) (Matrix.of p.2.2) D.z'_mem hp.2.2.1 hp.2.2.2 (Wq →L[ℂ] Wp) X)
  have key2 := congrArg (Formalism.FourierDecayAlt.P.JFxB.Lq D p) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at key2 ⊢
  refine Eq.trans ?_ (key2.trans ?_)
  · rfl
  · rfl

end Formalism.FourierDecayAlt.P.CutMP

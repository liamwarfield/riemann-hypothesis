module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeEqualityFromTestFunctions
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

section MatSub

variable {A : Type} [Ring A] [Algebra ℂ A]

def matSub (C : Subalgebra ℂ A) (n : Type) [Fintype n] [DecidableEq n] : Subalgebra ℂ (Matrix n n A) where
  carrier := {M | ∀ i j, M i j ∈ C}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)
  add_mem' := by
    intro M N hM hN i j
    exact Subalgebra.add_mem _ (hM i j) (hN i j)
  algebraMap_mem' := by
    intro c i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact C.algebraMap_mem c
    · exact C.zero_mem

theorem mem_matSub {C : Subalgebra ℂ A} {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n A} :
    M ∈ matSub C n ↔ ∀ i j, M i j ∈ C := by
  exact Iff.rfl

variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)

theorem eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro x y
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact C.one_mem
  · exact C.zero_mem

theorem io_mem {x : A} (hx : x ∈ C) : (io x : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact C.zero_mem

theorem lift_mem_matrix_algebra {M : M2 A} (hM : ∀ i j, M i j ∈ C) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  rw [mem_matSub]
  intro i j
  simp only [lift0, Matrix.map_apply]
  exact io_mem C (hM i j)

theorem ins_mem (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : M ∈ matSub (matSub C (Ix S)) (Fin 2)) :
    ins a M ∈ matSub C (Ix S) := by
  unfold ins
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (eU_mem C a i j) ?_
  exact mem_matSub.1 hM i j

theorem transpose_mem {n : Type} [Fintype n] [DecidableEq n] {C' : Subalgebra ℂ A} {M : Matrix n n A}
    (hM : M ∈ matSub C' n) : Mᵀ ∈ matSub C' n := by
  exact mem_matSub.2 fun i j => mem_matSub.1 hM j i

theorem Rh0_mem (a : S) (D : ℂ) : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hP : (P0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a j i
  unfold Rh0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hP) _

theorem Rht0_mem (a : S) (D : ℂ) : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hQ : (Q0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a i j
  unfold Rht0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hQ) _

theorem TTw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) (Y : ℂ) :
    TTw QQ w Y ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  induction w generalizing Y with
  | nil =>
    simp only [TTw]
    exact lift_mem_matrix_algebra C (hQ Y)
  | cons l w ih =>
    simp only [TTw]
    split_ifs
    · exact Subalgebra.mul_mem _ (ih Y) (Rh0_mem C _ _)
    · exact Subalgebra.mul_mem _ (Rht0_mem C _ _) (ih Y)

theorem RRw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) :
    RRw QQ w ∈ matSub C (Ix S) := by
  induction w with
  | nil =>
    simp only [RRw]
    exact Subalgebra.one_mem _
  | cons l w ih =>
    simp only [RRw]
    refine Subalgebra.mul_mem _ ih (ins_mem C _ ?_)
    split_ifs
    · exact TTw_mem C hQ w _
    · exact transpose_mem (TTw_mem C hQ w _)

theorem commute_io {f : A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ matSub (Subalgebra.centralizer ℂ {f}) (Ix S)) :
    Commute (io f : SlopeTestRemainingChoices S A) M := by
  have h : ∀ i j, f * M i j = M i j * f := by
    intro i j
    have hm := mem_matSub.1 hM i j
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm f (Set.mem_singleton f)
  show (io f : SlopeTestRemainingChoices S A) * M = M * io f
  ext i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact h i j

end MatSub

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem pr_fst_sum {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (s : Finset ι) (g : ι → Pr V) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  first
    | exact Prod.fst_sum (s := s) (f := g)
    | (classical
       induction s using Finset.induction_on with
       | empty => simp only [Finset.sum_empty]; rfl
       | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl)

theorem pr_fst_mul {V : Type} [AddCommGroup V] [Module ℂ V] (m n : Pr V) : (m * n).1 = m.1 * n.1 := rfl

theorem pr_fst_zero {V : Type} [AddCommGroup V] [Module ℂ V] : (0 : Pr V).1 = 0 := rfl

theorem act_mul (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Ix S → RadSp k r z z' π π') :
    act (M * N) x = act M (act N x) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [act, Matrix.mul_apply, pr_fst_sum, pr_fst_mul, LinearMap.sum_apply, Module.End.mul_apply,
    map_sum]
  exact Finset.sum_comm

theorem act_io (f : Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (io f) x a = f.1 (x a) := by
  simp only [act, io, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), pr_fst_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Act

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem hsInner_smul_left (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner (a • U) V = a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • U) = a • Formalism.FourierDecayAlt.B.hsVec U := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    first
      | rfl
      | (congr 1; funext i; simp)
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_right]

theorem pairAt_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (Wv Φ) Ψ c = fsv s (c l) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp_rw [hW Φ c, hsInner_smul_left]
  exact MeasureTheory.integral_const_mul _ _

theorem glue_succ_update (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  simp only [glue]
  rw [dite_eq_right (by rw [Fin.val_succ]; omega)]
  simp

theorem form_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ (act (io (mkP Wv Wv')) u) y (Function.update c l t) =
      fsv s t * form μ l.succ u y (Function.update c l t) := by
  unfold form
  have h : ∀ (c' : Cf r l.succ) (a : Ix S), pairAt μ (act (io (mkP Wv Wv')) u a) (y a) (glue l.succ (Function.update c l t) c') =
      fsv s t * pairAt μ (u a) (y a) (glue l.succ (Function.update c l t) c') := by
    intro c' a
    rw [act_io]
    have e : (mkP Wv Wv' : Pr (RadSp k r z z' π π')).1 = Wv := rfl
    rw [e, pairAt_mulOp μ l s Wv hW, glue_succ_update]
  simp_rw [h, ← Finset.mul_sum, mul_left_comm _ (fsv s t)]
  exact MeasureTheory.integral_const_mul _ _

end Wave

section StepParts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

theorem stepTwistFromParts : StepTwistFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hPW hWS hWC hWK w hw l s Wv Wv' hW hW' x y hx hy c _
  refine ⟨hWK w hw l s Wv Wv' hW hW' x hx, fun t _ => ?_⟩
  obtain ⟨hwave, hc1, hc2, hp⟩ := hWS hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    hPW ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hw.1.1
  have hQ : ∀ Y i j, QQi L st l.succ Y i j ∈ Subalgebra.centralizer ℂ {mkP Wv Wv'} := by
    intro Y i j
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (hWC l s Wv Wv' hW hW' Y i j).eq
  have hcomm : io (mkP Wv Wv') * RRi L st l.succ w = RRi L st l.succ w * io (mkP Wv Wv') :=
    (commute_io (RRw_mem _ hQ w)).eq
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) x, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) x,
    ← act_mul (RRi L st l.succ w) (io (mkP Wv Wv')), ← hcomm, act_mul (io (mkP Wv Wv')), form_mulOp μ l s Wv Wv' hW]
  ring

end StepParts

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

lemma mul_mem (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x)
    (Φ : RadSp k r z z' π π') :
    (fun c g => m (c, g) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈ RadSp k r z z' π π' := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, he⟩ := hΦm
  refine (show _ ∧ _ ∧ _ from ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩)
  · show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
    rw [h0 x hx, smul_zero]
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
    refine ⟨U, fun x => m x • F x, hU, hxU, hm.contDiffOn.smul hF, fun x hx hg => ?_⟩
    show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = m x • F x
    rw [hΦ x hx hg]
  · show m (x.1, h * x.2 * h') • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [hinv x hx h hh h' hh', he x hx h hh h' hh']
    ext v
    simp

def mulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    Module.End ℂ (RadSp k r z z' π π') where
  toFun Φ := ⟨_, mul_mem m hm hinv Φ⟩
  map_add' Φ Ψ := by
    ext c g v
    simp [smul_add]
  map_smul' a Φ := by
    ext c g v
    simp [smul_smul, mul_comm]

lemma mulOp_isMulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    multiplicationOperator (mulOp (π := π) (π' := π') m hm hinv) (fun c g => m (c, g)) := by
  intro _ _ _
  rfl

lemma contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

lemma contDiff_fsv_coord (l : Fin r) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fsv s (x.1 l)) :=
  (contDiff_fsv s).comp (by fun_prop : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l))

def hermLin (H : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun g := herm H (g *ᵥ v) w
  map_add' g g' := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a g := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]

lemma contDiff_zeta : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zeta k r z z' x.2) := by
  unfold zeta zetaL
  let Lc : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (hermLin (Hpk k r) (fvec k r z' (Fin.last r)) (fvec k r z (Fin.last r)))
  have h1 : ContDiff ℝ ∞ (fun g : Mx k r => Lc g) := (Lc.restrictScalars ℝ).contDiff
  exact h1.comp contDiff_snd

lemma herm_mulVec_mulVec (H h : Mx k r) (hh : hᴴ * H * h = H) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H (h *ᵥ v) (h *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh]

lemma zeta_inv (g : Mx k r) (h h' : Mx k r) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    zeta k r z z' (h * g * h') = zeta k r z z' g := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh'
  obtain ⟨hU, hb, hz⟩ := hh
  obtain ⟨hU', hb', hz'⟩ := hh'
  simp only [UH, Set.mem_setOf_eq] at hU
  have hf' : h' *ᵥ fvec k r z' (Fin.last r) = fvec k r z' (Fin.last r) := by
    unfold fvec
    rw [dite_eq_right (by simp)]
    exact hz'
  have hf : h *ᵥ fvec k r z (Fin.last r) = fvec k r z (Fin.last r) := by
    unfold fvec
    rw [dite_eq_right (by simp)]
    exact hz
  unfold zeta zetaL
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf']
  conv_lhs => rw [← hf]
  exact herm_mulVec_mulVec _ _ hU _ _

end Wave

theorem waveCExists : WaveCExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' l s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (x.1 l)) (contDiff_fsv_coord l s)
    (fun _ _ _ _ _ _ => rfl), mulOp_isMulOp _ _ _⟩

theorem waveZExists : WaveZExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (zeta k r z z' x.2))
    ((contDiff_fsv s).comp (contDiff_zeta (k := k) (r := r) (z := z) (z' := z')))
    (fun x _ h hh h' hh' => by
      show fsv s (zeta k r z z' (h * x.2 * h')) = fsv s (zeta k r z z' x.2)
      rw [zeta_inv _ _ _ hh hh']), mulOp_isMulOp _ _ _⟩

section Zero

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

end Zero

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordKeyIdentity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list_smul' {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => a i • φ i p).sum) μ ∧
      ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hadd := integral_add (hi.smul (a i)) hl1
    simp only [Pi.smul_apply] at hadd
    simp only [List.map_cons, List.sum_cons]
    refine ⟨(hi.smul (a i)).add hl1, ?_⟩
    rw [hadd, integral_smul, hl2]

theorem int_list_smul {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum :=
  (int_list_smul' μ l a φ h).2

theorem smul_list_smul {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (a : ι → ℂ)
    (x : ι → E) : c • (l.map fun i => a i • x i).sum = (l.map fun i => a i • (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [smul_add, ih, smul_comm c (a i)]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

theorem word_key (hW : JWords) (hR : RwRho) (D : RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : InCC A m F) {g : Mat k r} (hg : g ∈ Om k r D.z D.z')
    (w : List (Mat k r)) (hw : ∀ X ∈ w, unitLie k r X) (hl : w.length ≤ m) :
    Integrable (fun p => xiP D p • Rw w (rho D p F) g) D.μSS ∧
      Rw w (JF D F) g = ∫ p, xiP D p • Rw w (rho D p F) g ∂D.μSS := by
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] w (by simp) hw (by simpa using hl) g hg
  simp only [List.map_nil] at hI hE
  have hae : (fun p => xiP D p • rho D p (dLR [] (w.map (AdR p)) F) g) =ᵐ[D.μSS]
      fun p => xiP D p • Rw w (rho D p F) g := by
    filter_upwards [B5.ae_inSS D] with p hp
    have := hR k r Wp Wq D m F p hp hCk [] w (by simp) (fun X hX => (hw X hX).1) (by simpa using hl) g hg.1
    simp only [List.map_nil] at this
    rw [← this]
    rfl
  exact ⟨hI.congr hae, by rw [← integral_congr_ae hae]; exact hE⟩

end Formalism.FourierDecayAlt.P.WordKeyIdentity

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem capelli_under_integral_of_parts : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by
  intro hW hWS hR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hT hF g hg
  obtain ⟨L, hLw, hLeq⟩ := hWS k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ ⟨WordKeyIdentity.glev0 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun x hx hxG => he x hx (WordKeyIdentity.glev0 hxG)⟩
  rw [hLeq _ _ _ hJck g hg hg.1]
  have key : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := fun cw hcw =>
    WordKeyIdentity.word_key hW hR D hT hF hg cw.2 (hLw cw hcw).1 ((hLw cw hcw).2.trans hnm)
  have hRHS : (∫ p, xiP D p • Q.CV k r Y (rho D p F) g ∂D.μSS) =
      ∫ p, (L.map fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g)).sum ∂D.μSS := by
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hLeq _ _ _ (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, WordKeyIdentity.smul_list_smul]
  rw [hRHS, WordKeyIdentity.int_list_smul D.μSS L (fun cw => cw.1) (fun cw p => xiP D p • Rw cw.2 (rho D p F) g)
    fun cw hcw => (key cw hcw).1]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [(key cw hcw).2]

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaBOfComponents
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.B

theorem lemma_B_of_components : Formalism.FourierDecayAlt.B.LemmaB :=
  bessel_lemma_from_reductions bilinear_form_continuity ae_equality_from_test_functions fatou_lemma_in_parameter matrix_coefficient_linear dilation_matrix_coefficient
    bessel_function_trivial_index regularized_beta_bound_continuity_sesquilinear regularised_average_identity unfolding_identity_of_integration_formula orbital_integral_ae_convergence_continuity
    dilation_identity_of_jacobian phase_function_adjoint regularised_pairing_via_phase assemble_equality_identity adjointness_of_bessel_transform

theorem b_lemmaBClosed_of : Formalism.FourierDecayAlt.B.XiExists → Formalism.FourierDecayAlt.B.LemmaBClosed := fun hX =>
  bessel_lemma_closed_form hX lemma_B_of_components clause_of_regularized_limit adjointness_polynomially_bounded

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

theorem sgn_step (s : ℕ) : s * (s - 1) / 2 + (s + 1) * (s + 1 - 1) / 2 = s * s := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 1) * (s + 1 - 1) / 2 * 2 = (s + 1) * (s + 1 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd
  have h3 : s * (s - 1) + (s + 1) * (s + 1 - 1) = 2 * (s * s) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 1) * (s + 1 - 1) = B at *
  generalize s * s = C at *
  omega

theorem sgn_step2 (s : ℕ) : s * (s - 1) / 2 + (s + 2) * (s + 2 - 1) / 2 = s * (s + 1) + 1 := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 2) * (s + 2 - 1) / 2 * 2 = (s + 2) * (s + 2 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 2)).two_dvd
  have h3 : s * (s - 1) + (s + 2) * (s + 2 - 1) = 2 * (s * (s + 1) + 1) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel, show n + 1 + 2 - 1 = n + 2 by omega]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 2) * (s + 2 - 1) = B at *
  generalize s * (s + 1) = C at *
  omega

theorem neg_one_pow_sq (s : ℕ) : (-1 : ℂ) ^ (s * s) = (-1) ^ s := by
  rcases Nat.even_or_odd s with h | h
  · rw [Even.neg_one_pow h, Even.neg_one_pow (h.mul_left s)]
  · rw [Odd.neg_one_pow h, Odd.neg_one_pow (h.mul h)]

theorem sign_permutation_identity : SignE := by
  intro s
  refine ⟨?_, ?_⟩
  · unfold sgnW; rw [← pow_add, sgn_step, neg_one_pow_sq]
  · unfold sgnW; rw [← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]; ring

theorem sgnW_succ (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by
  have h := (sign_permutation_identity m).1
  have hsq : sgnW m * sgnW m = 1 := by
    unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp
  calc sgnW (m + 1) = (sgnW m * sgnW m) * sgnW (m + 1) := by rw [hsq, one_mul]
    _ = sgnW m * (sgnW m * sgnW (m + 1)) := by ring
    _ = (-1) ^ m * sgnW m := by rw [h]; ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMaj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeas : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

theorem jDom_of_parts : JDomMeas → JDomBound → Formalism.FourierDecayAlt.JF.JDom := fun hM hB k r Wp Wq _ _ _ _ _ _ D A m F hT hC =>
  ⟨hM k r Wp Wq D A m F hT hC, hB k r Wp Wq D A m F hT hC⟩

variable {k r : ℕ}

private theorem gv_mul_lemma (a b : Mat k r) (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma sL_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sL p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨⟨h11, -⟩, ⟨h12, -⟩, -, -⟩ := hp
  unfold sL
  exact gv_mul_lemma _ _ h12 h11

lemma sR_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sR p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨-, -, ⟨h21, -⟩, ⟨h22, -⟩⟩ := hp
  unfold sR
  exact gv_mul_lemma _ _ h22 h21

lemma pn_lr (p : SS k r) (u v : List (Mat k r)) :
    B4.pn (B4.lr (u.map (AdL p)) (v.map (AdR p))) =
      (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod := by
  simp [B4.pn, B4.lr, List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem inLie_inv_mul_mul_of_mem_gv {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) : inLie k r (y⁻¹ * X * y) := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [hinv]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
      hHH, mul_one]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    rw [hinv]
    simp only [mul_assoc, hHH']
  show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

lemma allLie_ad {p : SS k r} (hL : sL p ∈ GV k r) (hR : sR p ∈ GV k r) {u v : List (Mat k r)}
    (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    B4.AllLie (B4.lr (u.map (AdL p)) (v.map (AdR p))) := by
  unfold B4.AllLie B4.lr AdL AdR
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, ⟨X, hX, rfl⟩, rfl⟩ | ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  · exact inLie_inv_mul_mul_of_mem_gv hL (hu X hX).1
  · exact inLie_inv_mul_mul_of_mem_gv hR (hv X hX).1

theorem jDomBound_of_nnMaj : NNMaj → JDomBound := by
  intro hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub
  obtain ⟨c, hc⟩ := hCC
  obtain ⟨b, hbI, hb⟩ := hNN k r Wp Wq D A m hThr K hK hKsub
  refine ⟨fun p => c * b p, hbI.const_mul c, ?_⟩
  intro u v hu hv hl g hg
  filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin
  have hgG : g ∈ GV k r := (hKsub hg).1
  have hsG : sgs p g ∈ GV k r := B7.sgs_mem D hin hgG
  have hN : 0 < gN (sgs p g) := B6.gN_pos hsG
  have hgA : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hN A
  have hc0 : 0 ≤ c := by
    have h0 := hc.2 [] [] (by simp) (by simp) (by simp) g hgG
    exact le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0
  have hall := allLie_ad (sL_mem hin) (sR_mem hin) hu hv
  have hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m := by
    rw [B4.length_lr, List.length_map, List.length_map]; exact hl
  have hbd := B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG
  rw [← B4.dLR_eq, pn_lr] at hbd
  refine (B7.norm_rho_le D hin _ g).trans ?_
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A := by
    rw [le_div_iff₀ hgA]
    linarith [hbd]
  refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))
  rw [Real.rpow_neg hN.le]
  field_simp

end Formalism.FourierDecayAlt.P.JFxDs2
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RhoAntitoneOfInterlacing
open Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P

theorem lambda_side_inequality : C7.LamSide := by
  unfold C7.LamSide C7.LamInterlaces
  rintro k r u u' lam l Y hl hlk ⟨hA, hL⟩ ⟨-, hL'⟩ - i
  constructor
  · intro hli
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 1 := ⟨⟨l - 1, by omega⟩, rfl⟩
    have hji : j ≤ i := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam i ≤ lam j := hA.antitone hji
    have h1 := (hL j).1 (by omega)
    have h2 := (hL' j).1 (by omega)
    rw [show (j : ℕ) + 1 = l by omega] at h1 h2
    exact lt_min (lt_of_le_of_lt hi1 h1) (lt_of_le_of_lt hi1 h2)
  · intro hil
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 2 := ⟨⟨l - 2, by omega⟩, rfl⟩
    have hij : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam j ≤ lam i := hA.antitone hij
    have h1 := (hL j).2 (by omega)
    have h2 := (hL' j).2 (by omega)
    rw [show (j : ℕ) + 2 = l by omega] at h1 h2
    exact max_lt (lt_of_lt_of_le h1 hi1) (lt_of_lt_of_le h2 hi1)

theorem rho_antitone_of_interlacing {k : ℕ} {u u' ρ : ℕ → ℝ} (h : I.Interlaces k u u' ρ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k - 1 → ρ j ≤ ρ i := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
    have h1 := h n (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := h (n + 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h3 := ih (by omega)
    linarith [h1.2.2.1, h2.1]

theorem rho_side_inequality : C7.RhoSide := by
  unfold C7.RhoSide C7.Between
  intro k u u' ρ l Y hl hlk hI hB i hi
  have hi' : 1 ≤ i ∧ i ≤ k - 1 := by simpa using hi
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro hli
    have h1 := hI l (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI l i hl hli hi'.2
    have h3 : ρ l + 1 / 2 ≤ min (u l) (u' l) := le_min h1.1 h1.2.1
    linarith
  · intro hil
    have h1 := hI (l - 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI i (l - 1) hi'.1 (by omega) (by omega)
    rw [show l - 1 + 1 = l by omega] at h1
    have h3 : max (u l) (u' l) + 1 / 2 ≤ ρ (l - 1) := by
      rcases le_total (u l) (u' l) with h | h
      · rw [max_eq_right h]; exact h1.2.2.2
      · rw [max_eq_left h]; exact h1.2.2.1
    linarith

theorem sign_prod_of_split_at_index (s : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) (hpos : ∀ j ∈ s, j < m → 0 < g j)
    (hneg : ∀ j ∈ s, m ≤ j → g j < 0) : 0 < (-1 : ℝ) ^ (s.filter (m ≤ ·)).card * ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
      (fun j hj => hneg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert ha, Finset.filter_insert]
    by_cases hma : m ≤ a
    · rw [if_pos hma, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1), pow_succ]
      have := hneg a (Finset.mem_insert_self a s) hma
      nlinarith
    · rw [if_neg hma]
      have := hpos a (Finset.mem_insert_self a s) (by omega)
      nlinarith

theorem polynomial_sign : C7.PSign := by
  unfold C7.PSign
  intro k r u u' ρ lam l Y hl hlk hL hL' hI hB
  have hside := lambda_side_inequality k r u u' lam l Y hl hlk hL hL' hB
  have hrho := rho_side_inequality k u u' ρ l Y hl hlk hI hB
  have hB' := hB
  unfold C7.Between at hB'
  have hA : 0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) := by
    have hprod : ∏ s, (Y + lam s) = ∏ j ∈ Finset.range (k + 2 * r + 1),
        (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) j := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [dif_pos s.isLt, Fin.eta]
    have key := sign_prod_of_split_at_index (Finset.range (k + 2 * r + 1))
      (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) (l - 1)
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).2 (show j + 1 < l by omega)
        linarith [hB'.2])
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).1 (show l ≤ j + 1 by omega)
        linarith [hB'.1])
    have hcard : ((Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·)).card = (k - l) + 2 * (r + 1) := by
      rw [(show (Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·) = Finset.Ico (l - 1) (k + 2 * r + 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega), Nat.card_Ico]
      omega
    rw [hcard, pow_add, pow_mul, neg_one_sq, one_pow, mul_one] at key
    rw [hprod]
    exact key
  have hB2 : 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y := by
    unfold I.xpoly
    have key := sign_prod_of_split_at_index (Finset.Icc 1 (k - 1)) (fun i => Y + ρ i) l
      (fun i hi hil => show 0 < Y + ρ i by linarith [(hrho i hi).2 hil])
      (fun i hi hli => show Y + ρ i < 0 by linarith [(hrho i hi).1 hli])
    have hcard : ((Finset.Icc 1 (k - 1)).filter (l ≤ ·)).card = k - l := by
      rw [(show (Finset.Icc 1 (k - 1)).filter (l ≤ ·) = Finset.Icc l (k - 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega), Nat.card_Icc]
      omega
    rw [hcard] at key
    exact key
  refine ⟨hA, hB2, ?_⟩
  have h := abs_of_pos hA
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
  exact h

theorem roots_outside_jointly : C7.RootsOutJoint := by
  unfold C7.RootsOutJoint LE.Sys.RootsOut
  intro S u u' l hl hlk hI hI' hB s hs
  have hb := hB _ hs
  have key := lambda_side_inequality S.k S.r u u' S.lam l (-S.lam s) hl hlk hI hI' hb s
  unfold C7.Between at hb
  rw [neg_neg] at hb
  by_cases h : l ≤ s.val + 1
  · have := key.1 h
    linarith [hb.1]
  · have := key.2 (by omega)
    linarith [hb.2]

end Formalism.FourierDecayAlt.P
end

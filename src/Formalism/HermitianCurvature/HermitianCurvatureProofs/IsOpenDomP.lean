module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

abbrev XH (h : C.LPt) : Type := U.LW (D.ptPerm h) → ℂ

def ellH (h : C.LPt) (v : XH h) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)

def zxH (h : C.LPt) (j : ℕ) (hh : D.ptSize h = j) (v : XH h) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.reindex (finCongr hh) (finCongr hh) (LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h))

def pbT (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    Q.Mx P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) F g

def domP (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) :=
  {g | (∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0) ∧ 0 < Gf k r z z' g}

theorem isOpen_domP (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (domP k r j z z') := by
  have h1 : IsOpen {g : Q.Mx k r | ∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} := by
    have : {g : Q.Mx k r | ∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} =
        ⋂ l : Fin (r + 2), {g | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} := by
      ext g; simp
    rw [this]
    refine isOpen_iInter_of_finite fun l => ?_
    by_cases hl : j ≤ l.val ∧ l.val ≤ r
    · have : {g : Q.Mx k r | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
        ext g; simp [hl.1, hl.2]
      rw [this]
      exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l).continuous continuous_const
    · have : {g : Q.Mx k r | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
        ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro a b; exact absurd ⟨a, b⟩ hl
      rw [this]; exact isOpen_univ
  exact h1.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').continuous)

theorem minorDomain_subset (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    domP k r j z z' ⊆ LevelPointCoordinates.domJ k r j hj z z' := fun g hg =>
  ⟨hg.1 ⟨j, by omega⟩ (show j ≤ j from le_rfl) (show j ≤ r by omega),
    hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ r by omega), hg.2⟩

end Formalism.FourierDecayAlt.P.PBQ
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section zfull

variable {j : ℕ}

theorem zfull_apply (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (i l : Fin (j + 1)) :
    zfull Z τ i l = if h : i.val < j ∧ l.val < j then Z ⟨i.val, h.1⟩ ⟨l.val, h.2⟩
      else if i.val = j ∧ l.val = j then τ else 0 := by
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨l', rfl⟩ := finSumFinEquiv.surjective l
  unfold zfull U.blk2
  rcases i' with a | a <;> rcases l' with b | b <;>
    simp [Matrix.reindex_apply] <;> omega

theorem zfull_det (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  rw [Matrix.det_unique]
  rfl

end zfull

section point

variable {k r j : ℕ}

theorem x0_GV (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  have hZf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  have hM := (Formalism.FourierDecayAlt.P.slice_membership k (j + 1) (r - (j + 1))).1 _ γ hZf hγ
  exact Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM

theorem upper_minor_of_level_point (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < j + 1) :
    PBG.xi0 (x0 k r j hj Z τ γ) a' q =
      if hq : q.val < j + 1 then zfull Z τ ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0 := by
  unfold PBG.xi0
  rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
  unfold x0
  rw [LeftFubiniLemmas.castM_apply']
  have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j + 1 - 1 - a'.val, by omega⟩) := by
    ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
  rw [hi, LeftFubiniLemmas.embedding_map_apply_last_block]
  by_cases hq : q.val < j + 1
  · rw [dite_eq_left (by simpa using hq), dite_eq_left hq]
    congr 1; ext; simp [Fin.val_rev]; omega
  · rw [dite_eq_right (by simpa using hq), dite_eq_right hq]

theorem lower_minor_of_level_point (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1)))
    (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < j + 1) :
    PBG.y0 (x0 k r j hj Z τ γ) a' q =
      if hq : r + k < q.val ∧ 2 * r + k - q.val < j + 1 then
        star (zfull Z τ ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0 := by
  have hZf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  unfold PBG.y0
  rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
  have hgu : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hγ
  unfold x0
  rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZf) hgu,
    LeftFubiniLemmas.castM_apply']
  have hjj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
    ext; rw [Ux3.block_index_first_val]; simp [eI]
  rw [hjj, LeftFubiniLemmas.embedding_map_apply_first_block]
  by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < j + 1
  · rw [dite_eq_left (by simp; omega), dite_eq_left hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
    congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
  · rw [dite_eq_right (by simp; omega), dite_eq_right hq]

end point

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def qU : ℝ := ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) : NNReal) : ℝ)

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lam1 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ s : ℝ) : ℂ) * Complex.I ^ (s - 2)

def lam2 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ (s - 1) : ℝ) : ℂ) * Complex.I ^ (s - 1)

def omN (S : C.HidaSetting E Wp Wq) (N : ℕ) (P : C.LPt) : ℝ :=
  √(PBL.nnS S P) / PBL.bS S P * √(Top.wPt (S.T * S.T') S.G.r (PBL.stdS S P) ^ N)

end pts

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeib
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wl (A B : ℂ) : ℂ →L[ℝ] ℂ := A • ContinuousLinearMap.id ℝ ℂ + B • Complex.conjCLE.toContinuousLinearMap

theorem wl_apply (A B h : ℂ) : wl A B h = A * h + B * conj h := rfl

section Slice

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wOp (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) : Module.End ℂ (RadSp k r z z' π π') :=
  (js.map (X.op l)).prod

def dT (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 2 * X.op l 0

def dTb (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 5 * X.op l 3

def SlDom (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (Φ : RadSp k r z z' π π') : Prop :=
  ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧
    ∀ t ∈ Metric.ball t0 ε, ∀ c' : Cf r l.succ,
      ‖wtI l.succ c' * pairAt μ Φ Φ (glue l.succ (Function.update c l t) c')‖ ≤ F c'

def SliceGood (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)
    (Φ : RadSp k r z z' π π') : Prop :=
  Φ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') ∧
    ∀ js : List (Fin 6), SlDom μ l c (wOp X l js Φ)

end Slice

def PairAtDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (Φ Ψ : RadSp k r z z' π π'),
    Φ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') →
    Ψ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') →
    ∀ c ∈ OmX r, ∀ (c' : Cf r l.succ) (t : ℂ), t ≠ 0 →
      HasFDerivAt (fun s => pairAt μ Φ Ψ (glue l.succ (Function.update c l s) c'))
        (wl (pairAt μ (dT X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dTb X l Ψ) (glue l.succ (Function.update c l t) c'))
            (pairAt μ (dTb X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dT X l Ψ) (glue l.succ (Function.update c l t) c'))) t

def OuterLeib : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (S : Type) [Fintype S] [DecidableEq S] (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ), c ∈ OmX r →
    (∀ b, SliceGood X μ l c (u b)) → (∀ b, SliceGood X μ l c (v b)) → ∀ t : ℂ, t ≠ 0 →
      HasFDerivAt (fun s => form μ l.succ u v (Function.update c l s))
        (wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
            (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t))) t

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

abbrev MJ (j : ℕ) : Type := Matrix (Fin j) (Fin j) ℂ

def levi (k r j : ℕ) (x : MJ j) : Q.Mx k r := Matrix.of fun p q =>
  if hp : p.val < j then (if hq : q.val < j then x ⟨p.val, hp⟩ ⟨q.val, hq⟩ else 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      -conj (x ⟨2 * r + k - q.val, by omega⟩ ⟨2 * r + k - p.val, by omega⟩) else 0)
  else 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def EZ {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) h Z

def EZs {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ)) h Z

def ParamCommF {j : ℕ} (T : (MJ j → E) → (MJ j → E)) : Prop :=
  ∀ (U : Set (ℂ × (Fin j → Fin j → ℂ))) (κ : ℂ → MJ j → E), IsOpen U →
    U ⊆ {q | (Matrix.of q.2).det ≠ 0} →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => T (κ q.1) (Matrix.of q.2)) U ∧
    ∀ q ∈ U, PBP.dz (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dz (fun τ => κ τ Z) q.1) (Matrix.of q.2) ∧
      PBP.dzb (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) (Matrix.of q.2)

structure ZOp {j : ℕ} (T : (MJ j → E) → MJ j → E) : Prop where
  loc : ∀ (h₁ h₂ : MJ j → E) (Z : MJ j), h₁ =ᶠ[𝓝 Z] h₂ → T h₁ Z = T h₂ Z
  add : ∀ (V : Set (MJ j)) (h₁ h₂ : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h₁ V →
    ContDiffOn ℝ ∞ h₂ V → ∀ Z ∈ V, T (h₁ + h₂) Z = T h₁ Z + T h₂ Z
  smul : ∀ (V : Set (MJ j)) (c : ℂ) (h : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h V →
    ∀ Z ∈ V, T (c • h) Z = c • T h Z
  par : ParamCommF T

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

def CurveLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (x : MJ j) (t : ℝ),
    x0 k r j hj Z τ γ * NormedSpace.exp ((t : ℂ) • levi k r j x) =
      x0 k r j hj (Z * NormedSpace.exp ((t : ℂ) • x)) τ γ

def HpartLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j ≤ r) (a b : Fin j),
    hpart1 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) ∧
      hpart1 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ))

def XiCoef : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (a : Fin j)
    (p : Fin (2 * r + k + 1)),
    herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec p) (bvec (eI k r (Fin.castLE (by omega) a))) =
      if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def XiCoefV : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → ∀ (a : Fin j) (p : Fin (2 * r + k + 1)),
    ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE (by omega) a))) p =
      if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0

def XiMem : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Q.Glev k r 0

def XiSmooth : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ) {Z | Z.det ≠ 0}

def ZOpRd : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (x : MJ j), ZOp (E := E) (fun h => RdV x h)

def DzSlice : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (ℂ × (Fin j → Fin j → ℂ)))
    (κ : ℂ → MJ j → E), IsOpen U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U → ∀ τ₀ : ℂ,
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dz (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} ∧
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dzb (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U}

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HpkMulSingleEsI
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

variable {k r : ℕ}

theorem single_conjT {n : ℕ} (p q : Fin n) (c : ℂ) : (Matrix.single p q c)ᴴ = Matrix.single q p (star c) := by
  ext x y
  simp only [conjTranspose_apply, single_apply]
  by_cases h1 : p = y <;> by_cases h2 : q = x <;> simp [h1, h2]

theorem hpk_col_eI (i : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_col_esI (i : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_single_eI (c : Fin r) (q : Fin (2 * r + k + 1)) (x : ℂ) :
    Hpk k r * Matrix.single (eI k r c) q x = Matrix.single (esI k r c) q x := by
  ext i l
  by_cases hl : l = q
  · subst hl
    rw [mul_single_apply_same, hpk_col_eI, single_apply]
    by_cases h : i = esI k r c <;> simp [h, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]

theorem hpk_mul_single_esI (c : Fin r) (q : Fin (2 * r + k + 1)) (x : ℂ) :
    Hpk k r * Matrix.single (esI k r c) q x = Matrix.single (eI k r c) q x := by
  ext i l
  by_cases hl : l = q
  · subst hl
    rw [mul_single_apply_same, hpk_col_esI, single_apply]
    by_cases h : i = eI k r c <;> simp [h, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]

theorem eI_ne_esI (b c : Fin r) : eI k r b ≠ esI k r c := by
  have := b.isLt; have := c.isLt
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem eI_inj {b c : Fin r} (h : eI k r b = eI k r c) : b = c := by
  simp only [eI, Fin.ext_iff] at h; exact Fin.ext h

theorem esI_inj {b c : Fin r} (h : esI k r b = esI k r c) : b = c := by
  have := b.isLt; have := c.isLt
  simp only [esI, Fin.ext_iff] at h; exact Fin.ext (by omega)

section nl

variable (j : ℕ) (hj : j + 1 ≤ r) (a : Fin j → ℂ)

def Xn : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  ∑ b : Fin j, (a b • Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ))

theorem nL_eq : LevelPointCoordinates.nL k r j hj a = 1 + Xn j hj a := rfl

theorem hX : Hpk k r * Xn j hj a = ∑ b : Fin j, (a b • Matrix.single (eI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (esI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ)) := by
  unfold Xn
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hpk_mul_single_esI, hpk_mul_single_eI]

theorem hXh : (Xn (k := k) j hj a)ᴴ = ∑ b : Fin j, (conj (a b) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) -
    a b • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) := by
  unfold Xn
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]
  simp

theorem hXhH : (Xn (k := k) j hj a)ᴴ * Hpk k r = -(Hpk k r * Xn j hj a) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e : (Xn (k := k) j hj a)ᴴ * Hpk k r = (Hpk k r * Xn j hj a)ᴴ := by
    rw [Matrix.conjTranspose_mul, hH]
  rw [e, hX, Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]
  simp only [star_one, RCLike.star_def, Complex.conj_conj]
  abel

theorem hXHX : (Xn (k := k) j hj a)ᴴ * Hpk k r * Xn j hj a = 0 := by
  rw [Matrix.mul_assoc, hX, hXh, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  have n1 : esI k r ⟨j, by omega⟩ ≠ eI k r ⟨j, by omega⟩ := (eI_ne_esI _ _).symm
  have n2 : esI k r ⟨j, by omega⟩ ≠ esI k r ⟨b', by omega⟩ := fun h => by
    have := congrArg Fin.val (esI_inj h); simp at this; omega
  have n3 : eI k r ⟨b, by omega⟩ ≠ eI k r ⟨j, by omega⟩ := fun h => by
    have := congrArg Fin.val (eI_inj h); simp at this; omega
  have n4 : eI k r ⟨b, by omega⟩ ≠ esI k r ⟨b', by omega⟩ := eI_ne_esI _ _
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    single_mul_single_of_ne _ _ _ _ n1, single_mul_single_of_ne _ _ _ _ n2, single_mul_single_of_ne _ _ _ _ n3,
    single_mul_single_of_ne _ _ _ _ n4, smul_zero, sub_zero]

theorem nL_uh : LevelPointCoordinates.nL k r j hj a ∈ UH (Hpk k r) := by
  show (LevelPointCoordinates.nL k r j hj a)ᴴ * Hpk k r * LevelPointCoordinates.nL k r j hj a = Hpk k r
  rw [nL_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have h1 := hXhH (k := k) j hj a
  have h2 := hXHX (k := k) j hj a
  calc (1 + (Xn j hj a)ᴴ) * Hpk k r * (1 + Xn j hj a)
      = Hpk k r + ((Xn (k := k) j hj a)ᴴ * Hpk k r + Hpk k r * Xn j hj a) +
          (Xn (k := k) j hj a)ᴴ * Hpk k r * Xn j hj a := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]; abel
    _ = Hpk k r := by rw [h2, h1]; abel

theorem nL_apply (p q : Fin (2 * r + k + 1)) :
    LevelPointCoordinates.nL k r j hj a p q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) p q +
      ∑ b : Fin j, (a b * Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) p q -
        conj (a b) * Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ) p q) := by
  rw [nL_eq, Matrix.add_apply, Xn, Matrix.sum_apply]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

theorem nL_mem : LevelPointCoordinates.nL k r j hj a ∈ Nset k r := by
  refine ⟨nL_uh j hj a, ?_, ?_⟩
  · intro c i hci
    rw [nL_apply, Finset.sum_eq_zero, add_zero]
    · by_cases h : i = eI k r c <;> simp [h, Matrix.one_apply]
    · intro b _
      have hc := c.isLt
      rw [single_apply_of_col_ne _ _ (fun h => eI_ne_esI c ⟨b, by omega⟩ h.symm), mul_zero, zero_sub]
      rw [single_apply, if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      have := b.isLt
      omega
  · intro i q hq1 hq2 hi
    rw [nL_apply, Finset.sum_eq_zero, add_zero]
    · by_cases h : i = q <;> simp [h, Matrix.one_apply]
    · intro b _
      have hb := b.isLt
      rw [single_apply, if_neg, single_apply, if_neg, mul_zero, mul_zero, sub_zero]
      · rintro ⟨_, h2⟩
        have e2 := congrArg Fin.val h2; simp only [eI] at e2; omega
      · rintro ⟨_, h2⟩
        have e2 := congrArg Fin.val h2; simp only [esI] at e2; omega

end nl

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleOfEq
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

def RuleOfEq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (Φ : Q.Mx k r → E) (g : Q.Mx k r), inWb k r z' →
    (∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g) →
    ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g

def AdjoinNL : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r) (z : Fin (2 * r + k + 1) → ℂ)
    (Dm : Set (Q.Mx k r)) (hD : IsOpen Dm),
    (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, nL k r j hj a * g ∈ Dm) →
    ∀ x ∈ Algebra.adjoin ℂ (Set.range fun pq : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) =>
        (PBG.E0 (E := E) hD pq.1 pq.2 : Module.End ℂ (Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E))),
    ∀ v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E,
      (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        (v : Q.Mx k r → E) (nL k r j hj a * g) = psi k r z cStd (nL k r j hj a) • (v : Q.Mx k r → E) g) →
      ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) (nL k r j hj a * g) =
          psi k r z cStd (nL k r j hj a) • ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) g

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveOperatorLeL2Subspace
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem opClos_le {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (X : ActualOps k r z z' π π') (l : Fin r)
    {B V : Submodule ℂ (RadSp k r z z' π π')} (hB : B ≤ V) (hV : ∀ (j : Fin 6), ∀ Φ ∈ V, X.op l j Φ ∈ V) :
    OpClos X l B ≤ V := by
  rw [OpClos, Submodule.span_le]
  rintro Φ ⟨js, Ψ, hΨ, rfl⟩
  show (js.map (X.op l)).prod Ψ ∈ V
  induction js with
  | nil => simpa using hB hΨ
  | cons j js ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hV j _ ih

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem wave_operator_le_l2_subspace (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq)
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) :
    waveJ P z z' π π' D l ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Ψ hΨ => ?_
  obtain ⟨s, ε, G, Φ, Wv, -, hN, hlc, hΦ, hWv, rfl⟩ := unwave P z z' π π' D l Ψ hΨ
  refine unimodular_multiplier_preserves_L2 μ hμ hWv (fun _ _ => norm_fsv _ _) Φ ⟨hlc, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => G) (fun _ => G) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hN.2.1) (fun _ => hN.2.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  letI : Unique (Ix Empty) := { default := Empty.elim, uniq := fun _ => funext fun x => x.elim }
  simpa [wt0] using h

end Wave

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentRotationHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.TwoByOneBlock

section cWLemmas

variable {k r : ℕ}

theorem cW_mul (θ θ' : ℝ) : cW k r θ * cW k r θ' = cW k r (θ + θ') := by
  unfold cW
  rw [← emb_mul, smul_mul_smul_comm, mul_one, ← Complex.exp_add]
  congr 3
  push_cast
  ring

theorem cW_zero : cW k r 0 = 1 := by
  unfold cW
  simp [emb_one]

theorem cW_inv (θ : ℝ) : (cW k r θ)⁻¹ = cW k r (-θ) := by
  apply Matrix.inv_eq_right_inv
  rw [cW_mul, add_neg_cancel, cW_zero]

theorem cW_mulVec (θ : ℝ) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    cW k r θ *ᵥ v = Complex.exp ((θ : ℂ) * Complex.I) • v := by
  unfold cW
  rw [DC.emb_mulVec_of _ hv, Matrix.smul_mulVec, Matrix.one_mulVec, DC.jV_smul, jV_wbPart hv]

theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  unfold fvec
  rw [dite_eq_right (by simp)]

end cWLemmas

theorem lower_unipotent_rotation_holds : LowerUnipotentRotation := by
  intro k r z z' hz E _ _ θ Y f g _
  have hy : ∀ j, Q.yv k r z (Fin.last r) (cW k r θ * g) j =
      Complex.exp (-((θ : ℂ) * Complex.I)) * Q.yv k r z (Fin.last r) g j := by
    intro j
    unfold Q.yv
    rw [fvec_last, Matrix.mul_inv_rev, cW_inv, ← Matrix.mulVec_mulVec, cW_mulVec _ hz, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul]
    congr 2
    push_cast
    ring
  have hq : ∀ (t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ),
      qminorOp (Q.EH k r) a b u (fun x => f (cW k r θ * x)) g = qminorOp (Q.EH k r) a b u f (cW k r θ * g) :=
    fun t a b u => congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E _ t (Hpk k r) f a b u (cW k r θ)) g
  change (-(Q.chatL (Q.EH k r) (Q.posL k r (Fin.last r)) (Q.uC k r (Fin.last r) Y) (Q.yv k r z (Fin.last r))
      (fun _ => Q.xbv k r z' (Fin.last r)) f)) (cW k r θ * g) =
    Complex.exp (-((θ : ℂ) * Complex.I)) • (-(Q.chatL (Q.EH k r) (Q.posL k r (Fin.last r)) (Q.uC k r (Fin.last r) Y)
      (Q.yv k r z (Fin.last r)) (fun _ => Q.xbv k r z' (Fin.last r)) (fun x => f (cW k r θ * x)))) g
  simp only [Pi.neg_apply, Q.chatL, smul_neg, Finset.smul_sum, neg_inj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hy, hq, smul_smul]
  congr 1
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERD
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Wave

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def wvG (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => fsv s (Dmin k r z z' g ⟨1, by omega⟩) • F g

variable [FiniteDimensional ℂ Wq]

def NiceAll (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ JC.NiceCoef D ε F

end Wave

def RDWave : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (hr : 0 < r) (ε : ℝ) (s : ℂ) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
    (JC.NiceCoef D ε G → JC.NiceCoef D ε (wvG D.z D.z' s G)) ∧
    ∀ y ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 =
      fsv s (y.1 ⟨0, hr⟩) • resG k r (Fin.last r) (B.JF D G) y.1 y.2

def RDBeta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ : Measure (Mt k r)), B.IsHaarOn (Glev k r (Fin.last r)) μ →
    ∃ C1 : ℂ, C1 ≠ 0 ∧ ∀ (F H : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Ψ : RadSp k r D.z D.z' D.π D.π'),
      (∀ (A : ℝ) (m : ℕ), B.InCC A m F) → (∀ (A : ℝ) (m : ℕ), B.InCC A m H) →
      (∀ y ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ DomR k r D.z D.z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D H) y.1 y.2) →
      ∀ c : Fin r → ℂ, LocFacts₂ μ 0 Φ Ψ c = C1 * B.beta D F H

def RDBdd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F H : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ (A : ℝ) (m : ℕ), B.InCC A m F) → (∀ (A : ℝ) (m : ℕ), B.InCC A m H) →
    ∃ K : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) H‖ ≤ K

def RDHyp (Q : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], B.RealPlaceData k r Wp Wq → Prop) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    Q P.k P.r Wp Wq D

def RDIdent : Prop :=
  RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∃ Θ : Fin 4 → (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp),
      (∀ j F, NiceAll D F → NiceAll D (Θ j F)) ∧
      ∀ (s : ℂ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
        s * B.beta D (wvG D.z D.z' s F) F' =
          B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') - B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')

section Second

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RDOpsProp (D : B.RealPlaceData k r Wp Wq) (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ j, B.SmoothCoef (B.GPos D) (Θ j) ∧ B.Commutes D (B.GPos D) (Θ j) ∧
    (∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 ≤ d ∧ B.PolyCoef D ε d (B.opOrder (Θ j) + 5) (Θ j)) ∧
    ∀ F, NiceAll D F → NiceAll D (B.opApply (Θ j) F) ∧ NiceAll D (B.opAdj (Θ j) F)

end Second

end Formalism.FourierDecayAlt.P.CutSE
end
end

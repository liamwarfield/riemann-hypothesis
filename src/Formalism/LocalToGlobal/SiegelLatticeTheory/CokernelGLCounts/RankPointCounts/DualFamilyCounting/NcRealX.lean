module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXSig
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXGauge
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXUni
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

def sq2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem sq2_mul_sq2_eq_half : sq2 * sq2 = 1 / 2 := by
  unfold sq2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem star_sq2_eq_self : star sq2 = sq2 := by
  unfold sq2; rw [Complex.star_def, Complex.conj_ofReal]

def u1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then -sq2 else 1

def u2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then sq2 else 0

def Pu (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then u1 k r i else 0) + (if i = sig k r j then u2 k r i else 0)

theorem Pu_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pu k r i j) = Pu k r i j := by
  unfold Pu u1 u2
  split_ifs <;> simp [star_sq2_eq_self]

theorem PuJPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r) i j = Hpk k r i j := by
  have hJ : Formalism.REAL.Jm (epsK k r) = diagonal (dK k r) := rfl
  rw [hJ, Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2', if_neg h3, if_neg hjs]
      norm_num

theorem PuPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Pu k r) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      simp [h1, hjs, h2', h3]

theorem PuJPu (k r : ℕ) : (Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r = Hpk k r := by
  ext i j; exact PuJPu_apply k r i j

theorem PuPu (k r : ℕ) : (Pu k r)ᴴ * Pu k r = 1 := by
  ext i j; exact PuPu_apply k r i j

theorem exists_unitary {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r ∧ Pᴴ * P = 1 := by
  obtain ⟨σ, hσ⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF.exists_perm ε hs
  refine ⟨Matrix.of fun i j => Pu k r (σ.symm i) j, ?_, ?_⟩
  · rw [← PuJPu k r]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply, hσ m]
  · rw [← PuPu k r]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.MainNotions.S

section Coords

variable {m : ℕ}

def realifyE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

theorem realifyE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    (realifyE X).ofLp p = realifyFun X p := rfl

theorem unrealify_realifyE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realifyE X) = X := by
  funext i j
  apply Complex.ext
  · first | rfl | simp [unrealify, realifyE, realifyFun]
  · first | rfl | simp [unrealify, realifyE, realifyFun]

theorem realifyE_unrealify (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realifyE (unrealify x) = x := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b
  · first | rfl | simp [unrealify, realifyE, realifyFun]
  · first | rfl | simp [unrealify, realifyE, realifyFun]

theorem realifyE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realifyE (X + Y) = realifyE X + realifyE Y := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [realifyE, realifyFun]

theorem realifyE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realifyE (c • X) = c • realifyE X := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [realifyE, realifyFun]

theorem unrealify_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  rw [← realifyE_unrealify x, ← realifyE_unrealify y, ← realifyE_add, unrealify_realifyE, unrealify_realifyE,
    unrealify_realifyE]

theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = c • unrealify x := by
  rw [← realifyE_unrealify x, ← realifyE_smul, unrealify_realifyE, unrealify_realifyE]

def adE (A B : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realifyE (A * unrealify x * B)
  map_add' x y := by simp only [unrealify_add, Matrix.mul_add, Matrix.add_mul, realifyE_add]
  map_smul' c x := by
    simp only [unrealify_smul, Matrix.mul_smul, Matrix.smul_mul, realifyE_smul, RingHom.id_apply]

theorem unrealify_adE (A B : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (adE A B x) = A * unrealify x * B := unrealify_realifyE _

theorem norm_sq_realifyE (Y : Matrix (Fin m) (Fin m) ℂ) : ‖realifyE Y‖ ^ 2 = (trace (Yᴴ * Y)).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [realifyE_apply, realifyFun, if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_adE {P : Matrix (Fin m) (Fin m) ℂ} (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖adE Pᴴ P x‖ = ‖x‖ := by
  have hsq : ‖adE Pᴴ P x‖ ^ 2 = ‖x‖ ^ 2 := by
    show ‖realifyE (Pᴴ * unrealify x * P)‖ ^ 2 = ‖x‖ ^ 2
    conv_rhs => rw [← realifyE_unrealify x]
    rw [norm_sq_realifyE, norm_sq_realifyE]
    congr 1
    have e : (Pᴴ * unrealify x * P)ᴴ * (Pᴴ * unrealify x * P) = Pᴴ * ((unrealify x)ᴴ * unrealify x) * P := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (adE Pᴴ P x)), hsq, Real.sqrt_sq (norm_nonneg x)]

def adLE (P : Matrix (Fin m) (Fin m) ℂ) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun := adE Pᴴ P
  invFun := adE P Pᴴ
  map_add' := (adE Pᴴ P).map_add
  map_smul' := (adE Pᴴ P).map_smul
  left_inv x := by
    show realifyE (P * unrealify (realifyE (Pᴴ * unrealify x * P)) * Pᴴ) = x
    rw [unrealify_realifyE]
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, realifyE_unrealify]
  right_inv x := by
    show realifyE (Pᴴ * unrealify (realifyE (P * unrealify x * Pᴴ)) * P) = x
    rw [unrealify_realifyE]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one, realifyE_unrealify]

def adIso (P : Matrix (Fin m) (Fin m) ℂ) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  ⟨adLE P h1 h2, norm_adE h1 h2⟩

end Coords

section Lie

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem PHP (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h2 : P * Pᴴ = 1) :
    P * Hpk k r * Pᴴ = Formalism.REAL.Jm ε := by
  rw [← hPJ]
  simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem conj_UH_iff (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Pᴴ * g * P ∈ UH (Hpk k r) ↔ Formalism.REAL.inUJ ε g := by
  have key : (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [← PHP hPJ h2]
    simp only [Matrix.mul_assoc]
  show (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Hpk k r ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [key]
  constructor
  · intro h
    have h' := congrArg (fun M => P * M * Pᴴ) h
    have eL : P * (Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P) * Pᴴ = gᴴ * Formalism.REAL.Jm ε * g := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one]
    exact eL.symm.trans (h'.trans (PHP hPJ h2))
  · intro h
    rw [h, hPJ]

theorem isUnit_PH (h1 : Pᴴ * P = 1) : IsUnit Pᴴ :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h1)

theorem inv_PH (h1 : Pᴴ * P = 1) : (Pᴴ)⁻¹ = P := Matrix.inv_eq_right_inv h1

theorem exp_conjP (h1 : Pᴴ * P = 1) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (Pᴴ * X * P) = Pᴴ * NormedSpace.exp X * P := by
  have := Matrix.exp_conj Pᴴ X (isUnit_PH h1)
  rwa [inv_PH h1] at this

theorem lieOf_conj (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Pᴴ * X * P ∈ lieOf (UH (Hpk k r)) ↔ X ∈ lieOf {g | Formalism.REAL.inUJ ε g} := by
  simp only [lieOf, Set.mem_setOf_eq]
  refine forall_congr' fun t => ?_
  rw [show ((t : ℂ) • (Pᴴ * X * P)) = Pᴴ * ((t : ℂ) • X) * P by rw [Matrix.mul_smul, Matrix.smul_mul],
    exp_conjP h1, conj_UH_iff hPJ h1 h2]

theorem map_lieE (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    Submodule.map ((adIso P h1 h2 : _ ≃ₗᵢ[ℝ] _).toLinearEquiv.toLinearMap) (Formalism.MainNotions.S.Gauge.gLie ε) =
      lieE (UH (Hpk k r)) := by
  show Submodule.map _ (Submodule.span ℝ _) = Submodule.span ℝ _
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨Pᴴ * X * P, (lieOf_conj hPJ h1 h2 X).2 hX, ?_⟩
    show realifyE (Pᴴ * X * P) = realifyE (Pᴴ * unrealify (realifyE X) * P)
    rw [unrealify_realifyE]
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨realifyE (P * Y * Pᴴ), ⟨P * Y * Pᴴ, (lieOf_conj hPJ h1 h2 _).1 ?_, rfl⟩, ?_⟩
    · have : Pᴴ * (P * Y * Pᴴ) * P = Y := by
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [this]; exact hY
    · show realifyE (Pᴴ * unrealify (realifyE (P * Y * Pᴴ)) * P) = realifyE Y
      rw [unrealify_realifyE]
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def lieIso (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    Formalism.MainNotions.S.Gauge.gLie ε ≃ₗᵢ[ℝ] lieE (UH (Hpk k r)) :=
  (LinearIsometryEquiv.submoduleMap (Formalism.MainNotions.S.Gauge.gLie ε) (adIso P h1 h2)).trans
    (LinearIsometryEquiv.ofEq _ _ (map_lieE hPJ h1 h2))

theorem unrealify_lieIso (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (y : Formalism.MainNotions.S.Gauge.gLie ε) :
    unrealify ((lieIso hPJ h1 h2 y : lieE (UH (Hpk k r))) : EuclideanSpace ℝ _) =
      Pᴴ * unrealify (y : EuclideanSpace ℝ _) * P := by
  show unrealify (adE Pᴴ P (y : EuclideanSpace ℝ _)) = _
  exact unrealify_adE _ _ _

end Lie

section Gauge

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem sigmaFinite_smul' {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have hfin : ∀ i, (c • μ) (spanningSets μ i) < ⊤ := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
  exact ⟨⟨⟨spanningSets μ, fun _ => trivial, hfin, iUnion_spanningSets μ⟩⟩⟩

theorem isHaarOn_smul {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {ν : Measure (Mt k r)}
    (h : IsHaarOn S ν) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) : IsHaarOn S (c • ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨sigmaFinite_smul' ν hc, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, hc0, false_or] at this
    exact h2 (Measure.measure_univ_eq_zero.1 this)
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul c (measurable_lmulM (k := k) (r := r) s).aemeasurable, h4 s hs]

theorem preimage_expBall (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) (ρ : ℝ) :
    cM (ε := ε) Pᴴ P ⁻¹' expBall (UH (Hpk k r)) ρ = Formalism.MainNotions.S.Gauge.expSet ε (Metric.ball 0 ρ) := by
  ext g
  simp only [Set.mem_preimage, expBall, Set.mem_image, Formalism.MainNotions.S.Gauge.expSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hxe⟩
    set y := (lieIso hPJ h1 h2).symm x
    refine ⟨y, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
    · have hxy : lieIso hPJ h1 h2 y = x := LinearIsometryEquiv.apply_symm_apply _ _
      have hu := unrealify_lieIso hPJ h1 h2 y
      rw [hxy] at hu
      have hg : Pᴴ * uMat g * P = NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) := by
        have : (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) = cM (ε := ε) Pᴴ P g := hxe
        exact (funext fun i => funext fun j => congrFun (congrFun this i) j).symm
      rw [hu, exp_conjP h1] at hg
      have := congrArg (fun M => P * M * Pᴴ) hg
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul] at this
      rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one] at this
      exact this
  · rintro ⟨y, hy, hye⟩
    refine ⟨lieIso hPJ h1 h2 y, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hy
    · funext i j
      rw [unrealify_lieIso, exp_conjP h1, ← hye]
      rfl

theorem volume_ball_lie (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) (ρ : ℝ) :
    volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ) = volume (Metric.ball (0 : Formalism.MainNotions.S.Gauge.gLie ε) ρ) := by
  have hp := (lieIso hPJ h1 h2).measurePreserving
  have hpre : (lieIso hPJ h1 h2) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    ext y; simp only [Set.mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  rw [← hp.measure_preimage measurableSet_ball.nullMeasurableSet, hpre]

theorem muG_conj (t : Formalism.REAL.UJ ε) :
    (Formalism.REAL.muG ε).map (fun g => t⁻¹ * g * t) = Formalism.REAL.muG ε := by
  have e : (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) = (fun g => g * t) ∘ (fun g => t⁻¹ * g) := rfl
  rw [e, ← Measure.map_map (measurable_mul_const t) (measurable_const_mul t⁻¹), map_mul_left_eq_self,
    map_mul_right_eq_self]

end Gauge

theorem gaugeTr_of {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) :
    IsGaugeOn (UH (Hpk k r))
      (((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map
        (cM (ε := ε) (Qi (k := k) (r := r) ε e f wf z0) (Qm e f wf z0))) := by
  obtain ⟨P, hPJ, h1⟩ := exists_unitary ε (sig_of_frame hF)
  have h2 : P * Pᴴ = 1 := mul_eq_one_comm.mp h1
  set c : ℝ≥0∞ := (ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ with hc
  have hgpos := hG.2
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hgpos).ne'

  have hQ := gramQ hF
  have hQiQm := Qi_mul_Qm hF
  have hQmQi := Qm_mul_Qi hF
  have ht : (Qm e f wf z0 * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ) = Formalism.REAL.Jm ε := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    calc P * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ)
        = P * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hQ, PHP hPJ h2]
  set t : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * Pᴴ) ht
  have hut : uMat t = Qm e f wf z0 * Pᴴ := uMat_toUJ _ _
  have hut' : uMat t⁻¹ = P * Qi ε e f wf z0 := by
    have hinv : uMat t⁻¹ * uMat t = 1 := by rw [← uMat_mul, inv_mul_cancel, uMat_one]
    have hr : uMat t * (P * Qi ε e f wf z0) = 1 := by
      rw [hut, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h1, Matrix.one_mul, hQmQi]
    calc uMat t⁻¹ = uMat t⁻¹ * (uMat t * (P * Qi ε e f wf z0)) := by rw [hr, Matrix.mul_one]
      _ = P * Qi ε e f wf z0 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hfun : cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) = cM (ε := ε) Pᴴ P ∘ (fun g => t⁻¹ * g * t) := by
    funext g
    show (Qi ε e f wf z0 * uMat g * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      Pᴴ * uMat (t⁻¹ * g * t) * P
    rw [uMat_mul, uMat_mul, hut, hut']
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one]
  have emb := cM_measEmb (ε := ε) (A := Pᴴ) (B := P) (A' := P) (B' := Pᴴ) h2 h2
  have hmapeq : (c • Formalism.REAL.muG ε).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      (c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P) := by
    have hm : Measurable (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) := (measurable_const_mul t⁻¹).mul_const t
    rw [hfun, ← Measure.map_map emb.measurable hm, Measure.map_smul c hm.aemeasurable, muG_conj]
  rw [hmapeq]
  refine ⟨?_, ?_⟩
  · rw [Measure.map_smul c emb.measurable.aemeasurable]
    exact isHaarOn_smul (isHaarOn_G (P0 := P) (B0 := Pᴴ) ⟨hPJ, by
      rw [← hPJ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul,
        Formalism.REAL.Jm_mul_self, Matrix.mul_one]⟩) hc0 hct
  · have hratio : ∀ ρ : ℝ,
        (((c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P)) (expBall (UH (Hpk k r)) ρ)).toReal /
          (volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ)).toReal =
        (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ := by
      intro ρ
      rw [emb.map_apply, preimage_expBall hPJ h1 h2, volume_ball_lie hPJ h1 h2, Measure.smul_apply, smul_eq_mul,
        ENNReal.toReal_mul, hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal hgpos.le, Formalism.MainNotions.S.Gauge.ratioAt,
        mul_div_assoc]
    have hlim : Tendsto (fun ρ => (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ) (𝓝[>] 0)
        (𝓝 ((Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.gaugeU ε)) := hG.1.const_mul _
    rw [inv_mul_cancel₀ hgpos.ne'] at hlim
    exact hlim.congr fun ρ => (hratio ρ).symm

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCW
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj CoordinateScalingProducts

theorem coordW_exact (r k : ℕ) (T T' sc : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc)
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal ((2 ^ (r + 1) * nrm r sc * lamW r k sc)⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  have hlam0 : ∀ a, lam r sc a ≠ 0 := lam_ne hsc
  have hΛ0 : 0 < lamW r k sc := Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hlam0 a)) _
  have hN0 : 0 < nrm r sc := Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hlam0 a)
  have hpos : 0 < 2 ^ (r + 1) * nrm r sc * lamW r k sc := mul_pos (mul_pos (by positivity) hN0) hΛ0

  have hDl : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases hl : l ≤ r + 1
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun c => ∏ i : Fin l, c (Fin.castLE hl i) :=
        funext fun c => dl_diag c l hl
      rw [e]; fun_prop
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun _ => 0 :=
        funext fun c => by simp [Dl, hl]
      rw [e]; exact continuous_const
  have hGv : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hDl (r + 1)).norm.pow 2).sub (continuous_const.mul ((hDl r).norm.pow 2))
  have hGood : MeasurableSet (GoodLoc (r := r) T T') := by
    have e : GoodLoc (r := r) T T' =
        (⋂ l, {c : Fin (r + 1) → ℂ | c l ≠ 0}) ∩ {c | 0 < Gv T T' (Matrix.diagonal c)} := by
      ext c; simp [GoodLoc]
    rw [e]
    exact ((isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const).inter
      (isOpen_lt continuous_const hGv)).measurableSet

  have hptq : ∀ q : (Fin r → ℂ) × ℂ, Complex.normSq q.2 ≠ T * T' →
      Gi r k T T' F (coordSc r sc q) =
        ENNReal.ofReal (lamW r k sc) * (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := by
    intro q hq
    have hw := wt_cs hk T T' sc q
    have hg := gv_cs T T' sc q
    by_cases hq0 : ∀ a, q.1 a ≠ 0
    · by_cases hz : T * T' < Complex.normSq q.2
      · have hmem : coordSc r sc q ∈ GoodLoc (r := r) T T' := by
          refine ⟨fun l => ?_, ?_⟩
          · refine Fin.lastCases ?_ (fun a => ?_) l
            · rw [coordSc_last]
              intro h0
              rw [h0, map_zero] at hz
              exact absurd hz (not_lt.2 (mul_pos hT hT').le)
            · rw [coordSc_cs]; exact mul_ne_zero (hlam0 a) (hq0 a)
          · rw [hg]
            exact mul_pos (Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (mul_ne_zero (hlam0 a) (hq0 a))) 2)
              (by linarith)
        rw [Gi, Set.indicator_of_mem hmem, hw, Formalism.QuantumDeterminants.bcWeight, if_pos hz.le, ENNReal.ofReal_mul hΛ0.le, mul_assoc]
      · have hlt : Complex.normSq q.2 < T * T' := lt_of_le_of_ne (not_lt.1 hz) hq
        have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
          rintro ⟨-, hp⟩
          rw [hg] at hp
          exact absurd hp (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos
            (Finset.prod_nonneg fun a _ => by positivity) (sub_neg.2 hlt).le))
        rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), Formalism.QuantumDeterminants.bcWeight,
          if_neg (not_le.2 hlt), ENNReal.ofReal_zero, zero_mul, mul_zero]
    · push_neg at hq0
      obtain ⟨a, ha⟩ := hq0
      have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
        rintro ⟨hne, -⟩
        exact hne a.castSucc (by rw [coordSc_cs, ha, mul_zero])
      have hp : ∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by
          rw [ha, norm_zero]
          exact zero_pow (by have := a.isLt; unfold Formalism.QuantumDeterminants.Mdim; omega))
      have hb : Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
        unfold Formalism.QuantumDeterminants.bcWeight; split_ifs <;> simp [hp]
      rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), hb, ENNReal.ofReal_zero, zero_mul, mul_zero]

  have hnull : ∀ᵐ c : Fin (r + 1) → ℂ, Complex.normSq (c (Fin.last r)) ≠ T * T' := by
    have hS : (volume : Measure ℂ) {ζ | Complex.normSq ζ = T * T'} = 0 := by
      refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere volume (0 : ℂ) (Real.sqrt (T * T')))
      simp only [Set.mem_setOf_eq] at hζ
      rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have h0 : (volume : Measure (Fin (r + 1) → ℂ)) {c | Complex.normSq (c (Fin.last r)) = T * T'} = 0 := by
      exact Measure.pi_eval_preimage_null (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (i := Fin.last r) hS
    exact ae_iff.2 (by simpa using h0)
  have hpt : ∀ᵐ c : Fin (r + 1) → ℂ, Gi r k T T' F c = ENNReal.ofReal (lamW r k sc) *
      (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c) := by
    filter_upwards [hnull] with c hc
    have hc' : coordSc r sc ((Phe r sc hsc).symm c) = c := by
      rw [← phe_apply hsc, MeasurableEquiv.apply_symm_apply]
    have h2 : ((Phe r sc hsc).symm c).2 = c (Fin.last r) := by
      conv_rhs => rw [← hc']
      rw [coordSc_last]
    have key := hptq ((Phe r sc hsc).symm c) (by rw [h2]; exact hc)
    rw [hc'] at key
    exact key

  have hL : ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal (nrm r sc)⁻¹ * ∫⁻ c : Fin (r + 1) → ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_Phe hsc, lintegral_map_equiv]
    refine lintegral_congr fun q => ?_
    rw [MeasurableEquiv.symm_apply_apply, phe_apply]
  rw [hL, show (∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))) =
      ∫⁻ c, Gi r k T T' F c ∂(dcLoc (r := r)) from (lintegral_indicator hGood _).symm,
    dcLoc_eq, lintegral_smul_measure, smul_eq_mul, lintegral_congr_ae hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (inv_pos.2 hpos).le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem lam_one (r : ℕ) (a : Fin r) : lam r 1 a = 1 := by simp [lam]

theorem nrm_one (r : ℕ) : nrm r 1 = 1 := by simp [nrm, lam_one]

theorem lamW_one (r k : ℕ) : lamW r k 1 = 1 := by simp [lamW, lam_one]

theorem coordinate_weight_lintegral (r k : ℕ) (T T' : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T')
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r 1 q) =
      ENNReal.ofReal ((2 ^ (r + 1))⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  rw [coordW_exact r k T T' 1 hk hT hT' one_pos F, nrm_one, lamW_one, mul_one, mul_one]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem disint_switch {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' sc C : ℝ}
    (hF : FrameLoc ε k e z z' T T') {μS μS' : Measure (Formalism.REAL.UJ ε)}
    (hR : ∀ s ∈ SLoc ε e z, μS.map (fun x => x * s) = μS) (hR' : ∀ s ∈ SLoc ε e z', μS'.map (fun x => x * s) = μS')
    {h0 h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh0 : IsSecLoc ε sc e z z' T T' h0)
    (hh : IsSecLoc ε sc e z z' T T' h) (hD : DisintLoc ε k T T' μS μS' h0 C) : DisintLoc ε k T T' μS μS' h C := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun c hc => ?_)
  obtain ⟨s₁, hs₁, s₁', hs₁', hg⟩ :=
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  rw [hg, JL.inner_dc μS μS' s₁ s₁' (h0 c) (hR s₁ hs₁) (hR' s₁' hs₁') φ]

theorem jacLocX_of (hJ : JacGauge) : JacLocX := by
  intro k r ε e f wf z0 zB zB' hF hk hz hz' hT hT' hG μH μH' hH hH' a a' ha ha' hma hma' κ hκ h hh
  have emb := embQ hF
  have hFL : FrameLoc ε k e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') := by
    exact ⟨by omega, hk, sig_of_frame hF, e_li hF, hF.ee, hJ_e_Qm hF hz,
      hJ_e_Qm hF hz', hJ_Qm_self hF zB, hJ_Qm_self hF zB', hT, hT'⟩
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  have hpsi : JL.psiP (ε := ε) (Qm e f wf z0) = cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) := by
    funext u
    show (fun i j => ((Qm e f wf z0)⁻¹ * uMat u * Qm e f wf z0) i j) =
      (Qi ε e f wf z0 * uMat u * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    rw [hQinv]

  obtain ⟨μsec, hμ⟩ := JL.secWb_holds k r zB zB' hk hz hz' hT hT'
  let μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun ζ =>
    if Tz k r zB * Tz k r zB' < Complex.normSq ζ then μsec ζ else 1
  have hμs : IsSection k r zB zB' μs := by
    refine ⟨fun i j => (hμ.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
    · have hζ' : Tz k r zB * Tz k r zB' < Complex.normSq ζ := hζ
      simp only [μs, if_pos hζ']
    · simp only [μs, if_pos hζ]
      exact hμ.2 ζ hζ
  have hU : ∀ ζ, (μs ζ)ᴴ * Hb k * μs ζ = Hb k := by
    intro ζ
    by_cases hζ : Tz k r zB * Tz k r zB' < Complex.normSq ζ
    · simp only [μs, if_pos hζ]; exact (hμ.2 ζ hζ).1
    · simp only [μs, if_neg hζ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hMuj : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      Formalism.REAL.inUJ ε (Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹) := fun q hq =>
    JL.inUJ_conj (gramQ hF) hdet (JL.bigMem_holds k r q.1 (μs q.2) hq (hU q.2))

  let h0 : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε := fun c =>
    if hc : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 then JL.ujOf _ (hMuj (JL.qOf r 1 c) hc) else 1
  have hh0q : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      uMat (h0 (JL.coordSc r 1 q)) = Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹ := by
    intro q hq
    have hq' : ∀ a, (JL.qOf r 1 (JL.coordSc r 1 q)).1 a ≠ 0 := by rw [JL.qOf_coordSc r one_pos]; exact hq
    simp only [h0, dif_pos hq', JL.uMat_ujOf, JL.qOf_coordSc r one_pos]
  have hh0 : IsSecLoc ε 1 e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') h0 := by
    intro c hc
    have hq1 : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 := fun a =>
      mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ one_ne_zero)) (hc.1 _)
    have hζ : Tz k r zB * Tz k r zB' < Complex.normSq (JL.qOf r 1 c).2 := by
      have h2 := hc.2
      rw [JL.gv_diag_eq] at h2
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · show Tz k r zB * Tz k r zB' < Complex.normSq (c (Fin.last r)); linarith
      · exact absurd h3 (not_lt.2 (sq_nonneg _))
    have he0 := hh0q (JL.qOf r 1 c) hq1
    rw [JL.coordSc_qOf r one_pos] at he0
    show Zhat ε (famSc 1 e (Qm e f wf z0 *ᵥ zB)) (famSc 1 e (Qm e f wf z0 *ᵥ zB')) (uMat (h0 c)) = Matrix.diagonal c
    rw [he0, (JL.zBig r k ε e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') zB zB' (Qm e f wf z0) 1 (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz hz' rfl rfl one_pos μs hμs (JL.qOf r 1 c) hq1 hζ).2,
      JL.coordSc_qOf r one_pos]

  have hfin : μH Set.univ ≠ ⊤ := by rw [hma]; exact ENNReal.ofReal_ne_top
  have hfin' : μH' Set.univ ≠ ⊤ := by rw [hma']; exact ENNReal.ofReal_ne_top
  refine disint_switch hFL (fun s hs => rightX_of hF hz hT hH hfin κ hκ s hs)
    (fun s hs => rightX_of hF hz' hT' hH' hfin' κ hκ s hs) hh0 hh ?_
  have hW := measW_of hF hH
  have hW' := measW_of hF hH'
  have hWa : (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a := by
    rw [emb.map_apply, Set.preimage_univ, hma]
  have hWa' : (μH'.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a' := by
    rw [emb.map_apply, Set.preimage_univ, hma']
  open Filter Topology in
  have hGauge : IsGaugeOn (UH (Hpk k r))
        (((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map
          (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
    obtain ⟨P, hPJ, h1⟩ := exists_unitary ε (sig_of_frame hF)
    have h2 : P * Pᴴ = 1 := mul_eq_one_comm.mp h1
    set c : ℝ≥0∞ := (ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ with hc
    have hgpos := hG.2
    have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
    have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hgpos).ne'
  
    have hQ := gramQ hF
    have hQiQm := Qi_mul_Qm hF
    have hQmQi := Qm_mul_Qi hF
    have ht : (Qm e f wf z0 * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ) = Formalism.REAL.Jm ε := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose]
      calc P * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ)
          = P * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [hQ, PHP hPJ h2]
    set t : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * Pᴴ) ht
    have hut : uMat t = Qm e f wf z0 * Pᴴ := uMat_toUJ _ _
    have hut' : uMat t⁻¹ = P * Qi ε e f wf z0 := by
      have hinv : uMat t⁻¹ * uMat t = 1 := by rw [← uMat_mul, inv_mul_cancel, uMat_one]
      have hr : uMat t * (P * Qi ε e f wf z0) = 1 := by
        rw [hut, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h1, Matrix.one_mul, hQmQi]
      calc uMat t⁻¹ = uMat t⁻¹ * (uMat t * (P * Qi ε e f wf z0)) := by rw [hr, Matrix.mul_one]
        _ = P * Qi ε e f wf z0 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hfun : cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) = cM (ε := ε) Pᴴ P ∘ (fun g => t⁻¹ * g * t) := by
      funext g
      show (Qi ε e f wf z0 * uMat g * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        Pᴴ * uMat (t⁻¹ * g * t) * P
      rw [uMat_mul, uMat_mul, hut, hut']
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
      rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one]
    have emb := cM_measEmb (ε := ε) (A := Pᴴ) (B := P) (A' := P) (B' := Pᴴ) h2 h2
    have hmapeq : (c • Formalism.REAL.muG ε).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
        (c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P) := by
      have hm : Measurable (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) := (measurable_const_mul t⁻¹).mul_const t
      rw [hfun, ← Measure.map_map emb.measurable hm, Measure.map_smul, muG_conj]
      exact hm.aemeasurable
    rw [hmapeq]
    refine ⟨?_, ?_⟩
    · rw [Measure.map_smul]
      exact isHaarOn_smul (isHaarOn_G (P0 := P) (B0 := Pᴴ) ⟨hPJ, by
        rw [← hPJ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul,
          Formalism.REAL.Jm_mul_self, Matrix.mul_one]⟩) hc0 hct
      exact emb.measurable.aemeasurable
    · have hratio : ∀ ρ : ℝ,
          (((c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P)) (expBall (UH (Hpk k r)) ρ)).toReal /
            (volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ)).toReal =
          (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ := by
        intro ρ
        rw [emb.map_apply, preimage_expBall hPJ h1 h2, volume_ball_lie hPJ h1 h2, Measure.smul_apply, smul_eq_mul,
          ENNReal.toReal_mul, hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal hgpos.le, Formalism.MainNotions.S.Gauge.ratioAt,
          mul_div_assoc]
      have hlim : Tendsto (fun ρ => (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ) (𝓝[>] 0)
          (𝓝 ((Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.gaugeU ε)) := hG.1.const_mul _
      rw [inv_mul_cancel₀ hgpos.ne'] at hlim
      exact hlim.congr fun ρ => (hratio ρ).symm
  have hJG := hJ k r zB zB' hk hz hz' hT hT' _ _ _ hGauge hW hW' a a' ha ha' hWa hWa' κ hκ μs hμs
  have hS1 := measS_of hF hz hT hH κ hκ
  have hS2 := measS_of hF hz' hT' hH' κ hκ
  intro φ hφ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  let φh : Mt k r → ℝ≥0∞ := Function.extend Ψ φ 0
  have hφh : Measurable φh := emb.measurable_extend hφ measurable_const
  have hext : ∀ u, φh (Ψ u) = φ u := fun u => emb.injective.extend_apply φ 0 u
  have hgU : 0 < Formalism.MainNotions.S.Gauge.gaugeU ε := hG.2
  have hL : ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε) *
      ∫⁻ x, φh x ∂(((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map Ψ) := by
    rw [emb.lintegral_map, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hgU).ne' ENNReal.ofReal_ne_top, one_mul]
    simp only [hext]
  rw [hL, hJG φh hφh, ← hS1, ← hS2]
  set F : (Fin (r + 1) → ℂ) → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹)
    ∂(muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)) ∂(muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)) with hF0
  have hpt : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) *
      ∫⁻ s, ∫⁻ s', φh (fun i j => (Matrix.of s * bigCell k r q.1 (μs q.2) * (Matrix.of s')⁻¹) i j)
        ∂((muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ)
        ∂((muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ) =
      ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) * F (JL.coordSc r 1 q) := by
    intro q
    by_cases hq : ∀ a, q.1 a ≠ 0
    · congr 1
      rw [emb.lintegral_map]
      refine lintegral_congr fun u => ?_
      rw [emb.lintegral_map]
      refine lintegral_congr fun u' => ?_
      have hw := JL.psiP_mul_B hdet u u' (bigCell k r q.1 (μs q.2)) (h0 (JL.coordSc r 1 q)) (hh0q q hq)
      rw [hpsi] at hw
      rw [hw, hext]
    · push_neg at hq
      obtain ⟨a, ha0⟩ := hq
      rw [JL.bcWeight_zero _ _ q a ha0, ENNReal.ofReal_zero, zero_mul, zero_mul]
  rw [lintegral_congr hpt, JL.coordinate_weight_lintegral r k (Tz k r zB) (Tz k r zB') hk hT hT' F]
  have hK0 := Jac.jacConst_nonneg (k := k) (r := r) hT hT' ha ha' hκ
  have hV1 := Jac.volU_pos (k - 1)
  have hCX : Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) =
      Formalism.MainNotions.S.Gauge.gaugeU ε * (jacConst k r (Tz k r zB) (Tz k r zB') a a' κ * (2 ^ (r + 1))⁻¹) := by
    unfold jacConst
    field_simp
  have hC0 : 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) := by
    rw [hCX]; positivity
  have hpt2 : ∀ c, ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) * wtLoc k (Tz k r zB) (Tz k r zB') c) *
        F c =
      ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2)) *
        (ENNReal.ofReal (wtLoc k (Tz k r zB) (Tz k r zB') c) * F c) := fun c => by
    rw [ENNReal.ofReal_mul hC0, mul_assoc]
  rw [lintegral_congr hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCX,
    ENNReal.ofReal_mul hgU.le, ENNReal.ofReal_mul hK0]
  ring

end Formalism.L2.SG.Pf.NcReal.JX

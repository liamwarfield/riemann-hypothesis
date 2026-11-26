module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixRealSizeLeConstMulOfCompactTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixRealSizeLeConstMulOfCompactTranslate
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.RealMove

open GlobalTheory.Unf GlobalTheory.Unf.MajMeas

theorem realSize_mul_le_mul {D : D7} (θ : InfFam D) {m r n : ℕ} (Y : Mx D m r) (a : Mx D r n) :
    realSize θ (Y * a) ≤ n * realSize θ Y * realSize θ a := by
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = n * realSize θ Y * realSize θ a := by
        have h : ∀ τ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a =
            n * (∑ l, ‖compAt θ τ Y i l‖) * realSize θ a := by
          intro τ i
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, mul_assoc]
        simp_rw [h, ← Finset.sum_mul, ← Finset.mul_sum]
        rfl

theorem realSize_le_of_isCompact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.realSize θ x ≤ C * GlobalTheory.Unf.realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := by
  intro D θ hθ V n Q hQ
  have hc : Continuous (fun y : GA D V => realSize θ (Formalism.L2.Theta.mt V y)) :=
    (continuous_realSize hθ).comp (GlobalTheory.Core.Rk.Level.continuous_mt' V)
  obtain ⟨M, hM⟩ := (hQ.image hc).bddAbove
  refine ⟨max 1 (n * M), le_max_left _ _, fun y hy x => ?_⟩
  set a : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with ha
  have e : x = (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by
    rw [ha]
    rw [← Matrix.mul_assoc, ← GlobalTheory.Core.Rk.Level.mt_mul', mul_inv_cancel, GlobalTheory.Core.Rk.Level.mt_one',
      Matrix.one_mul]
  have hyM : realSize θ (Formalism.L2.Theta.mt V y) ≤ M := hM ⟨y, hy, rfl⟩
  have h0 := realSize_nonneg θ a
  have h1 := realSize_nonneg θ (Formalism.L2.Theta.mt V y)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc realSize θ x = realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by rw [← e]
    _ ≤ n * realSize θ (Formalism.L2.Theta.mt V y) * realSize θ a :=
        realSize_mul_le_mul θ _ _
    _ ≤ (n * M) * realSize θ a := by gcongr
    _ ≤ max 1 (n * M) * realSize θ a := by gcongr; exact le_max_right _ _

end GlobalTheory.Unf.RealMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixRealSizeLeConstMulOfCompactTranslateStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixRealSize_le_const_mul_of_compact_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.realSize θ x ≤ C * GlobalTheory.Unf.realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := by
  first | exact @GlobalTheory.Unf.RealMove.realSize_le_of_isCompact | exact GlobalTheory.Unf.RealMove.realSize_le_of_isCompact | (intros; apply GlobalTheory.Unf.RealMove.realSize_le_of_isCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompact
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BoxMove

theorem inBox_image_mul : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  intro D V n Q hQ K hK
  have hmt : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n) :=
    (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨(fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n)) '' (Q ×ˢ K), (hQ.prod hK).image hf, ?_⟩
  rintro y hy x ⟨k, hk, h0⟩
  refine ⟨(HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n), ⟨(y, k), ⟨hy, hk⟩, rfl⟩, ?_⟩
  have hyy : Formalism.L2.Theta.mt V y * Formalism.L2.Theta.mt V y⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hx : x - (HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n) = (HMul.hMul (Formalism.L2.Theta.mt V y) ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) - k) : Mx D V.rank n) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  rw [hx, Matrix.map_mul, h0, Matrix.mul_zero]

end GlobalTheory.BoxMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompactStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  first | exact @GlobalTheory.BoxMove.inBox_image_mul | exact GlobalTheory.BoxMove.inBox_image_mul | (intros; apply GlobalTheory.BoxMove.inBox_image_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLe
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MajMul

theorem maj_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  intro D θ hθ V n Q hQ K hK
  obtain ⟨K', hK', hbox⟩ := GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact D V n Q hQ K hK
  obtain ⟨C₀, hC₀, hreal⟩ := GlobalTheory.T.adelicMatrixRealSize_le_const_mul_of_compact_translate D θ hθ V n Q hQ
  refine ⟨K', hK', fun N => ⟨C₀ ^ N, by positivity, fun y hy x => ?_⟩⟩
  set z : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with hz
  unfold GlobalTheory.Unf.maj
  by_cases hin : GlobalTheory.Unf.InBox K z
  · rw [if_pos hin, if_pos (hbox y hy x hin)]
    have h0 := GlobalTheory.Unf.realSize_nonneg θ z
    have h1 := GlobalTheory.Unf.realSize_nonneg θ x
    have h2 := hreal y hy x
    have h3 : 1 + GlobalTheory.Unf.realSize θ x ≤ C₀ * (1 + GlobalTheory.Unf.realSize θ z) := by nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ z) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ (C₀ * (1 + GlobalTheory.Unf.realSize θ z)) ^ N := by gcongr
      _ = C₀ ^ N * (1 + GlobalTheory.Unf.realSize θ z) ^ N := by rw [mul_pow]
  · rw [if_neg hin]
    have := GlobalTheory.Unf.maj_nonneg θ K' N x
    unfold GlobalTheory.Unf.maj at this
    have hC : (0:ℝ) ≤ C₀ ^ N := by positivity
    exact mul_nonneg hC this

end GlobalTheory.MajMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLeStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  first | exact @GlobalTheory.MajMul.maj_mul_le | exact GlobalTheory.MajMul.maj_mul_le | (intros; apply GlobalTheory.MajMul.maj_mul_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfSumSqLtOne
namespace GlobalTheory.NormBoundSumSquares

theorem norm_le_one_of_sum_sq_lt_one :
    (let d1 : {E : Type} → [inst : Field E] → [NumberField E] → {a : ℕ} → GlobalTheory.CuspRep.Lie E a → ℝ := @(fun {E : Type} [Field E] [NumberField E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a) ↦ ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ)); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a), d1 x < (1 : ℝ) → ‖x‖ ≤ (1 : ℝ)) := by
  intro d1 E _ _ _ a x hx
  have hsum : ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ) < 1 := hx
  have entry : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E), ‖x i j w‖ ≤ 1 := by
    intro i j w
    by_contra hcon
    have hgt : 1 < ‖x i j w‖ := lt_of_not_ge hcon
    have hsq : 1 < ‖x i j w‖ ^ (2 : ℕ) := one_lt_pow₀ hgt (by norm_num)
    have h₃ : ‖x i j w‖ ^ (2 : ℕ) ≤ ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun j' => ‖x i j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h₂ : ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ)
        ≤ ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h₁ : ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ)
        ≤ ∑ w' : NumberField.InfinitePlace E, ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun w' => ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ w)
    linarith
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => entry i j w

end GlobalTheory.NormBoundSumSquares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompact
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjKinf (k : Kinf E a) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse
    ((lmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))).comp (rmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))))
    ((lmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))).comp (rmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))))
    (fun x => by
      change toL (star (k : Matrix (Fin a) (Fin a) (Cinf E)) * ((k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) * (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]; rfl)
    (fun x => by
      change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * (k : Matrix (Fin a) (Fin a) (Cinf E))) * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.one_mul]; rfl)

theorem conjKinf_apply (k : Kinf E a) (x : Lie E a) :
    conjKinf k x = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) := by
  change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = _
  rw [Matrix.mul_assoc]

def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w‖ ^ 2

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem trace_mul_conjTranspose_cinf (M : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    (M * M.conjTranspose).trace w = ((∑ i, ∑ j, ‖M i j w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_apply,
    Pi.mul_apply, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem frobSq_eq (x : Lie E a) :
    frobSq x = ∑ w, ((Matrix.of x * (Matrix.of x).conjTranspose).trace w).re := by
  simp only [frobSq, trace_mul_conjTranspose_cinf, Complex.ofReal_re]; rfl

theorem frobSq_conjKinf (k : Kinf E a) (x : Lie E a) : frobSq (conjKinf k x) = frobSq x := by
  rw [frobSq_eq, frobSq_eq, conjKinf_apply]
  have h : ∀ M : Matrix (Fin a) (Fin a) (Cinf E),
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
        ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))).conjTranspose =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (M * M.conjTranspose) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro M
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (k : Matrix (Fin a) (Fin a) (Cinf E))) (k : Matrix (Fin a) (Fin a) (Cinf E)),
      Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]
  rw [show Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
    (k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) from rfl, h,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

theorem norm_le_one_of_frobSq (x : Lie E a) (h : frobSq x < 1) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | (apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one ..)

theorem continuous_frobSq : Continuous (frobSq : Lie E a → ℝ) := by
  unfold frobSq
  fun_prop

theorem measurePreserving_conjKinf (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (k : Kinf E a) :
    MeasurePreserving (conjKinf k) ν ν := by
  refine ⟨(conjKinf k).continuous.measurable, ?_⟩
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hdet : LinearMap.det ((conjKinf k : Lie E a ≃L[ℝ] Lie E a).toLinearEquiv.toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have e := Measure.map_linearMap_addHaar_eq_smul_addHaar ν hdet
  change Measure.map (conjKinf k) ν = _ at e
  set B : Set (Lie E a) := frobSq ⁻¹' Set.Iio 1
  have hBo : IsOpen B := isOpen_Iio.preimage continuous_frobSq
  have hB0 : (0 : Lie E a) ∈ B := by simp [B, frobSq]
  have hpos : ν B ≠ 0 := (hBo.measure_pos ν ⟨0, hB0⟩).ne'
  have hfin : ν B ≠ ⊤ := (measure_mono fun x hx => (mem_closedBall_zero_iff.2 (norm_le_one_of_frobSq x hx))).trans_lt
    (measure_closedBall_lt_top (μ := ν) (x := (0 : Lie E a)) (r := 1)) |>.ne
  have hpre : conjKinf k ⁻¹' B = B := by
    ext x; simp [B, frobSq_conjKinf]
  have h1 := congrArg (fun m : Measure (Lie E a) => m B) e
  simp only [Measure.map_apply (conjKinf k).continuous.measurable hBo.measurableSet, hpre, Measure.smul_apply,
    smul_eq_mul] at h1
  have hc := (ENNReal.mul_eq_right hpos hfin).1 h1.symm
  rw [e, hc, one_smul]

theorem smoothing_rt_Kinf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a))
    [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : KInv α) (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a) :
    smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  unfold smoothing
  rw [chart_rt_inf, chart_mul, ← (measurePreserving_conjKinf ν k).integral_comp (conjKinf k).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  congr 1
  · rw [conjKinf_apply]; exact hα k x
  · congr 1
    rw [conjKinf_apply]
    change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
      (k : Matrix (Fin a) (Fin a) (Cinf E))) = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x)
    rw [Matrix.mul_assoc _ (star _), Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompactStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_right_translate_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), KInv α → ∀ (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a), smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.AutGrowth.smoothing_rt_Kinf | exact GlobalTheory.AutGrowth.smoothing_rt_Kinf | (intros; apply GlobalTheory.AutGrowth.smoothing_rt_Kinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.FinEig

open Polynomial

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem fd_inf_ker_mul (N : Submodule ℂ M) (f g : Module.End ℂ M) (hf : ∀ v ∈ N, f v ∈ N)
    (h1 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker f)) (h2 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker g)) :
    FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (g * f)) := by
  rw [← Submodule.fg_iff_finiteDimensional]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker f
  · have hle : (N ⊓ LinearMap.ker (g * f)).map f ≤ N ⊓ LinearMap.ker g := by
      rintro _ ⟨v, ⟨hvN, hv⟩, rfl⟩
      exact ⟨hf v hvN, by simpa [LinearMap.mem_ker] using hv⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  · have hle : N ⊓ LinearMap.ker (g * f) ⊓ LinearMap.ker f ≤ N ⊓ LinearMap.ker f :=
      fun v hv => ⟨hv.1.1, hv.2⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance

theorem adjoin_preserves (N : Submodule ℂ M) (s : Set (Module.End ℂ M)) (hs : ∀ u ∈ s, ∀ v ∈ N, u v ∈ N)
    {b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s) : ∀ v ∈ N, b v ∈ N := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => intro v hv; simpa [Module.algebraMap_end_apply] using N.smul_mem r hv
  | add x y _ _ hx hy => intro v hv; exact N.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy => intro v hv; exact hx _ (hy v hv)

theorem fd_inf_ker_aeval (N : Submodule ℂ M) (t : Module.End ℂ M) (ht : ∀ v ∈ N, t v ∈ N)
    (h : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ))) :
    ∀ n : ℕ, ∀ q : ℂ[X], q.natDegree = n → q ≠ 0 → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (aeval t q)) := by
  intro n
  induction n with
  | zero =>
    intro q hq hq0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hq] at hq0 ⊢
    have ha : q.coeff 0 ≠ 0 := fun e => hq0 (by rw [e, map_zero])
    have hle : N ⊓ LinearMap.ker (aeval t (C (q.coeff 0))) ≤ ⊥ := by
      intro v hv
      have h2 := hv.2
      simp only [LinearMap.mem_ker, aeval_C, Module.algebraMap_end_apply] at h2
      simpa [Submodule.mem_bot] using (smul_eq_zero.1 h2).resolve_left ha
    exact Submodule.finiteDimensional_of_le hle
  | succ n ih =>
    intro q hq hq0
    have hdeg : 0 < q.degree := by
      rw [Polynomial.degree_eq_natDegree hq0, hq]; exact_mod_cast Nat.succ_pos n
    obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (a := μ) (p := q)).2 hμ
    set q' := q /ₘ (X - C μ) with hq'
    have hq'0 : q' ≠ 0 := by
      intro e; apply hq0; rw [← hfac, e, mul_zero]
    have hq'deg : q'.natDegree = n := by
      rw [hq', Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C μ), hq, Polynomial.natDegree_X_sub_C]; rfl
    have hmul : aeval t q = (t - algebraMap ℂ (Module.End ℂ M) μ) * aeval t q' := by
      conv_lhs => rw [← hfac]
      simp [map_mul, map_sub, aeval_X, aeval_C]
    rw [hmul]
    apply fd_inf_ker_mul N _ _ _ (ih q' hq'deg hq'0) (h μ)
    exact adjoin_preserves N {t} (by simpa using ht) (Polynomial.aeval_mem_adjoin_singleton ℂ t)

theorem fd_of_finset (T : Finset (Module.End ℂ M)) (hc : ∀ u ∈ T, ∀ w ∈ T, u * w = w * u)
    (ha : ∀ u ∈ T, ∃ q : ℂ[X], q ≠ 0 ∧ aeval u q = 0) :
    ∀ N : Submodule ℂ M, (∀ u ∈ T, ∀ v ∈ N, u v ∈ N) →
      (∀ c : Module.End ℂ M → ℂ,
        FiniteDimensional ℂ ↥(N ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u)))) →
      FiniteDimensional ℂ ↥N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro N _ h
    haveI := h 0
    refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ (∅ : Finset (Module.End ℂ M)),
      LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) ((0 : Module.End ℂ M → ℂ) u))) ?_
    intro v hv
    refine ⟨hv, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro u
    rw [Submodule.mem_iInf]
    intro hu
    simp at hu
  | insert t T htT ih =>
    intro N hN h
    obtain ⟨q, hq0, hq⟩ := ha t (Finset.mem_insert_self t T)
    have key : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ)) := by
      intro μ
      apply ih (fun u hu w hw => hc u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw))
        (fun u hu => ha u (Finset.mem_insert_of_mem hu))
      · intro u hu v hv
        refine ⟨hN u (Finset.mem_insert_of_mem hu) v hv.1, ?_⟩
        have h2 : (t - algebraMap ℂ (Module.End ℂ M) μ) v = 0 := hv.2
        have hcom := hc t (Finset.mem_insert_self t T) u (Finset.mem_insert_of_mem hu)
        show (t - algebraMap ℂ (Module.End ℂ M) μ) (u v) = 0
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply] at h2 ⊢
        rw [← Module.End.mul_apply, hcom, Module.End.mul_apply, ← map_smul, ← map_sub, h2, map_zero]
      · intro c
        haveI := h (Function.update c t μ)
        refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ insert t T,
          LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (Function.update c t μ u))) ?_
        intro v hv
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
        obtain ⟨⟨hvN, hvt⟩, hvT⟩ := hv
        refine ⟨hvN, fun u hu => ?_⟩
        rcases Finset.mem_insert.1 hu with rfl | hu'
        · simpa using hvt
        · have hne : u ≠ t := fun e => htT (e ▸ hu')
          rw [Function.update_of_ne hne]
          exact hvT u hu'
    have := fd_inf_ker_aeval N t (hN t (Finset.mem_insert_self t T)) key _ q rfl hq0
    rwa [hq, LinearMap.ker_zero, inf_top_eq] at this

end GlobalTheory.FinEig

namespace GlobalTheory.AutGrowth

theorem finiteDimensional_of_commuting_finite_eigen :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) →
      FiniteDimensional ℂ (Algebra.adjoin ℂ S) →
      (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) →
      FiniteDimensional ℂ M := by
  intro M _ _ S hS hB hE
  classical
  letI : IsMulCommutative (Algebra.adjoin ℂ S) :=
    Algebra.isMulCommutative_adjoin ℂ (fun x hx y hy _ => hS x hx y hy)
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ S, ∀ y ∈ Algebra.adjoin ℂ S, x * y = y * x := by
    intro x hx y hy
    exact setLike_mul_comm hx hy
  obtain ⟨T, hT⟩ : (Algebra.adjoin ℂ S).FG :=
    Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hB)
  have hTA : ∀ u ∈ T, u ∈ Algebra.adjoin ℂ S := fun u hu => hT ▸ Algebra.subset_adjoin hu
  have key := GlobalTheory.FinEig.fd_of_finset T (fun u hu w hw => hcomm u (hTA u hu) w (hTA w hw))
    (fun u hu => ((IsIntegral.of_finite ℂ (⟨u, hTA u hu⟩ : Algebra.adjoin ℂ S)).map
      (Algebra.adjoin ℂ S).val).isAlgebraic) ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  intro c
  have scal : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ v ∈ (⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u))), b v = μ • v := by
    intro b hb
    rw [← hT] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨c x, fun v hv => ?_⟩
      rw [Submodule.mem_iInf] at hv
      have h3 := hv x
      rw [Submodule.mem_iInf] at h3
      have h4 := h3 hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h4
      exact h4
    | algebraMap r => exact ⟨r, fun v _ => by simp [Module.algebraMap_end_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ + μ₂, fun v hv => by rw [LinearMap.add_apply, h₁ v hv, h₂ v hv, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ * μ₂, fun v hv => by
        rw [Module.End.mul_apply, h₂ v hv, map_smul, h₁ v hv, smul_smul, mul_comm]⟩
  let c' : Module.End ℂ M → ℂ := fun s => if h : s ∈ Algebra.adjoin ℂ S then Classical.choose (scal s h) else 0
  haveI := hE c'
  refine Submodule.finiteDimensional_of_le
    (S₂ := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c' s))) ?_
  intro v hv
  replace hv := hv.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  intro s hs
  have hsA : s ∈ Algebra.adjoin ℂ S := Algebra.subset_adjoin hs
  simp only [c', dif_pos hsA]
  exact Classical.choose_spec (scal s hsA) v hv

end GlobalTheory.AutGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEiStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → FiniteDimensional ℂ (Algebra.adjoin ℂ S) → (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | exact GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

abbrev ovT (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : Over (Sp R) :=
  Over.mk (spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))

abbrev ovB (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R B))

theorem one_left (A : Over (Sp R)) [GrpObj A] (T : Over (Sp R)) : (1 : T ⟶ A).left = T.hom ≫ η[A].left := rfl

theorem inl_w (A : Over (Sp R)) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    (spMap (TrivSqZeroExt.inlHom B M) ≫ P) ≫ A.hom = (ovT R B M).hom := by
  rw [Category.assoc, hP]
  exact (GlobalTheory.Cris.spMap_comp _ _).symm

theorem fst_w (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ (ovT R B M).hom = (ovB R B).hom := by
  show _ ≫ spMap _ = spMap _
  rw [← GlobalTheory.Cris.spMap_comp]
  congr 1 <;> ext r <;> simp

theorem fst_inl (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (TrivSqZeroExt.inlHom B M) = 𝟙 (Sp B) := by
  rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
  congr 1 <;> ext r <;> simp

def eFst (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : ovB R B ⟶ ovT R B M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) (fst_w B M)


open Classical in
def tau (A : Over (Sp R)) [GrpObj A] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) :
    Sp (TrivSqZeroExt B M) ⟶ A.left :=
  if h : P ≫ A.hom = spMap (algebraMap R B) ∧ z ≫ A.hom = (ovT R B M).hom then
    ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P h.1) *
      Over.homMk (U := ovT R B M) (V := A) z h.2 : ovT R B M ⟶ A)).left
  else z

theorem tau_eq (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B))
    (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : z ≫ A.hom = (ovT R B M).hom) :
    tau A B M P z = ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) *
      Over.homMk (U := ovT R B M) (V := A) z hz : ovT R B M ⟶ A)).left := by
  rw [tau, dite_eq_left ⟨hP, hz⟩]

theorem red_iff (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (g : ovT R B M ⟶ A) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ g.left = P ↔
      eFst B M ≫ g = Over.homMk (U := ovB R B) (V := A) P hP := by
  constructor
  · intro h; ext; simpa [eFst] using h
  · intro h; have := congrArg CommaMorphism.left h; simpa [eFst] using this

theorem unit_eq (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B]
    (h : unitPt A B ≫ A.hom = spMap (algebraMap R B)) :
    Over.homMk (U := ovB R B) (V := A) (unitPt A B) h = 1 := by
  ext; rw [one_left]; rfl

end GlobalTheory.AbTan.Transl

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

theorem unit_w (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] :
    unitPt A B ≫ A.hom = spMap (algebraMap R B) := by
  rw [unitPt, Category.assoc, Over.w η[A]]
  exact Category.comp_id _

theorem bijOn_tau (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    Set.BijOn (tau A B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z} := by
  set Q : ovT R B M ⟶ A := Over.homMk (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) with hQ
  have hU := unit_w A B
  have keyQ : eFst B M ≫ Q = Over.homMk (U := ovB R B) (V := A) P hP := by
    ext
    simp only [eFst, Q, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, fst_inl]
    exact Category.id_comp _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := hz
    show Lifts A.hom P (tau A B M P z)
    rw [tau_eq A P hP z h1]
    refine ⟨Over.w _, ?_⟩
    rw [red_iff A _ P hP, MonObj.comp_mul, keyQ,
      (red_iff A (Over.homMk (U := ovT R B M) (V := A) z h1) (unitPt A B) hU).1 h2, unit_eq, _root_.mul_one]
  · intro z1 hz1 z2 hz2 he
    obtain ⟨h11, -⟩ := hz1
    obtain ⟨h21, -⟩ := hz2
    rw [tau_eq A P hP z1 h11, tau_eq A P hP z2 h21] at he
    have := mul_left_cancel (Over.OverMorphism.ext he)
    exact congrArg CommaMorphism.left this
  · intro z' hz'
    obtain ⟨h1, h2⟩ := hz'
    set Z : ovT R B M ⟶ A := Q⁻¹ * Over.homMk (U := ovT R B M) (V := A) z' h1 with hZ
    refine ⟨Z.left, ⟨Over.w Z, ?_⟩, ?_⟩
    · rw [red_iff A Z (unitPt A B) hU, unit_eq, hZ, MonObj.comp_mul, GrpObj.comp_inv, keyQ,
        (red_iff A (Over.homMk (U := ovT R B M) (V := A) z' h1) P hP).1 h2, inv_mul_cancel]
    · show tau A B M P Z.left = z'
      rw [tau_eq A P hP Z.left (Over.w Z)]
      have e : Over.homMk (U := ovT R B M) (V := A) Z.left (Over.w Z) = Z := by ext; rfl
      rw [← hQ, e, hZ, mul_inv_cancel_left]
      rfl

theorem tau_natural (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] {B' M' : Type} [CommRing B'] [Algebra R B']
    [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (hβ : IsSum β α f) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) (z : Sp (TrivSqZeroExt B M) ⟶ A.left)
    (hz : Lifts A.hom (unitPt A B) z) :
    Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧
      tau A B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ tau A B M P z := by
  obtain ⟨hz1, hz2⟩ := hz
  have hβinl : β.comp (TrivSqZeroExt.inlHom B M) = (TrivSqZeroExt.inlHom B' M').comp (α : B →+* B') :=
    RingHom.ext fun b => hβ.1 b
  have hβT : β.comp ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) =
      (TrivSqZeroExt.inlHom B' M').comp (algebraMap R B') := by
    rw [← RingHom.comp_assoc, hβinl, RingHom.comp_assoc, AlgHom.comp_algebraMap]
  have hβfst : (TrivSqZeroExt.fstHom B' B' M').toRingHom.comp β =
      (α : B →+* B').comp (TrivSqZeroExt.fstHom B B M).toRingHom := by
    ext x
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp [map_add (f := _), hβ.1, hβ.2]
  let b : ovT R B' M' ⟶ ovT R B M := Over.homMk (spMap β) (by
    show spMap β ≫ spMap _ = spMap _
    rw [← GlobalTheory.Cris.spMap_comp, hβT])
  set Z : ovT R B M ⟶ A := Over.homMk z hz1 with hZ
  have hz' : (spMap β ≫ z) ≫ A.hom = (ovT R B' M').hom := Over.w (b ≫ Z)
  have hP' : (spMap (α : B →+* B') ≫ P) ≫ A.hom = spMap (algebraMap R B') := by
    rw [Category.assoc, hP, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  refine ⟨⟨hz', ?_⟩, ?_⟩
  · rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hβfst, GlobalTheory.Cris.spMap_comp, Category.assoc, hz2, unitPt,
      unitPt, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [tau_eq A _ hP' _ hz', tau_eq A P hP z hz1]
    have e1 : b ≫ (Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP)) =
        Over.homMk (U := ovT R B' M') (V := A) (spMap (TrivSqZeroExt.inlHom B' M') ≫ spMap (α : B →+* B') ≫ P)
          (inl_w A _ hP') := by
      ext
      simp only [b, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp, hβinl]
    have e2 : b ≫ Z = Over.homMk (U := ovT R B' M') (V := A) (spMap β ≫ z) hz' := by ext; rfl
    show _ = (b ≫ (_ * Z)).left
    rw [MonObj.comp_mul, e1, e2]

end GlobalTheory.AbTan.Transl


open GlobalTheory.AbTan.Transl in
theorem GlobalTheory.AbTan.exists_translation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  intro R _ A _
  refine ⟨fun B M => tau A B M, ?_, ?_⟩
  · intro B M _ _ _ _ _ _ P hP
    exact bijOn_tau A P hP
  · intro B M _ _ _ _ _ _ B' M' _ _ _ _ _ _ α f β hβ P hP z hz
    exact tau_natural A α f β hβ P hP z hz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPointStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_sqZeroPoints_unit_to_point : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  first | exact @GlobalTheory.AbTan.exists_translation | exact GlobalTheory.AbTan.exists_translation | (intros; apply GlobalTheory.AbTan.exists_translation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariant
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell

theorem cellU_haar_rightInv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ _ p
  have hS := GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hU n k hk hn y hy hw
  haveI : LocallyCompactSpace (cellU y) :=
    (hS.1 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hS.1 0).1.mem_nhds (hS.1 0).2.2.1)
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mulRight p).toMeasurableEquiv
  have he : ∀ u, e u = u * p := fun _ => rfl
  let ν : Measure (cellU y) := μ.map e
  haveI : ν.IsMulLeftInvariant := by
    have : ν = μ.map (fun x => x * p) := rfl
    rw [this]; exact isMulLeftInvariant_map_mul_right p
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    show μ.map e K < ⊤
    rw [e.map_apply]
    exact ((hK.image (Homeomorph.mulRight p).symm.continuous)).measure_lt_top.trans_le' (by
      apply le_of_eq; congr 1; ext x; simp [e, Homeomorph.mulRight, Equiv.mulRight])

  set j : ℕ := depthU k (p : GU σ n)
  have hp : p ∈ shellU k y (j : ℤ) := mem_shellU_depth k y p
  obtain ⟨ho, hc, h1, hmul, hinv⟩ := hS.1 (j : ℤ)
  have hνS : ν (shellU k y j) = 1 * μ (shellU k y j) := by
    rw [one_mul]
    show μ.map e _ = _
    rw [e.map_apply]
    congr 1
    ext u
    simp only [Set.mem_preimage, he]
    constructor
    · intro h
      simpa using hmul _ _ h (hinv p hp)
    · intro h; exact hmul _ _ h hp
  have hνμ : ν = μ := by
    have := GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen (cellU y) μ ν (fun i : ℕ => shellU k y (i : ℤ))
      (fun i => ⟨(hS.1 i).2.1, (hS.1 i).1.measurableSet⟩)
      (Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩)
      _ 1 ho hc ⟨1, h1⟩ hνS
    rwa [one_smul] at this
  have hmp : MeasurePreserving e μ μ := ⟨e.measurable, hνμ⟩
  refine ⟨fun F => ?_, fun F => ?_⟩
  · exact hmp.integral_comp' (g := fun u : cellU y => F (u : GU σ n))
  · exact hmp.lintegral_comp_emb e.measurableEmbedding (fun u : cellU y => F (u : GU σ n))

end GlobalTheory.WeylCell.WeylUnipotentShell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariantStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryWeylCell_haar_rightTranslate_invariant : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv | exact GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv <;> assumption)
end
end

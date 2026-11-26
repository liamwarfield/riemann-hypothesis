module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UGraph

open GlobalTheory.Doubling Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_GLint_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {x : GL ι L}
    (h1 : ∀ i j, x.1 i j ∈ Formalism.UG.intL L) (h2 : ∀ i j, (x⁻¹).1 i j ∈ Formalism.UG.intL L) :
    x ∈ Formalism.UG.GLint ι (Formalism.UG.intL L) := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem unif_mem_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
  omega

theorem exp_rev {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (i : Fin n) : d (Fin.rev i) = -d i := by
  have h : Formalism.UG.cT σ t.1.1 * Formalism.UG.antiJ L n * t.1.1 = Formalism.UG.antiJ L n := t.2
  have h1 := congrFun (congrFun h i) (Fin.rev i)
  have hJ : Formalism.UG.antiJ L n i (Fin.rev i) = 1 := by
    simp only [Formalism.UG.antiJ, Fin.val_rev]
    rw [if_pos (by omega)]
  rw [hJ, ht, Formalism.UG.cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, hJ] at h1
  rw [map_zpow₀, hU.2.2.1, mul_one, ← zpow_add₀ ϖ.ne_zero] at h1
  have h2 := congrArg Formalism.UG.ordL h1
  rw [Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1, ← zpow_zero (ϖ : L), Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h2
  omega

theorem antiJ_mul_diagonal {n : ℕ} (f g : Fin n → L) (h : ∀ i, f (Fin.rev i) = g i) :
    Formalism.UG.antiJ L n * Matrix.diagonal f = Matrix.diagonal g * Formalism.UG.antiJ L n := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.UG.antiJ]
  split_ifs with hij
  · have : j = Fin.rev i := Fin.ext (by rw [Fin.val_rev]; omega)
    subst this
    rw [h]
    ring
  · simp

theorem exists_kappa {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (d : Fin n → ℤ)
    (hd : ∀ i, d (Fin.rev i) = -d i) :
    ∃ κ : GL (Fin (n + n)) L, κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n ∧ κ ∈ Formalism.UG.GLint (Fin (n + n)) (Formalism.UG.intL L) ∧
      GlobalTheory.Doubling.KeepsDiag finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) ∧
      GlobalTheory.Doubling.leviMat finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) =
        Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
  set e := finSumFinEquiv (m := n) (n := n)
  set J := Formalism.UG.antiJ L n
  set u : Fin n → L := fun i => (ϖ : L) ^ (-d i).toNat - 1 with hu
  set w : Fin n → L := fun i => (ϖ : L) ^ (d i).toNat - 1 with hw
  have huw : ∀ i, u i * w i = 0 := fun i => by
    rcases le_total (d i) 0 with h | h
    · simp [hw, Int.toNat_of_nonpos h]
    · simp [hu, Int.toNat_of_nonpos (neg_nonpos.2 h)]
  set B : Matrix (Fin n) (Fin n) L := Matrix.diagonal u with hB
  set C : Matrix (Fin n) (Fin n) L := Matrix.diagonal w with hC
  have hBC : B * C = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [huw]
  have hCB : C * B = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [mul_comm (w _), huw]
  have hJB : J * B = C * J := antiJ_mul_diagonal u w fun i => by simp [hu, hw, hd]
  have hJC : J * C = B * J := antiJ_mul_diagonal w u fun i => by simp [hu, hw, hd]
  have hσu : B.map σ = B := by
    rw [hB, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hu, map_sub, map_pow, hU.2.2.1]
  have hσw : C.map σ = C := by
    rw [hC, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hw, map_sub, map_pow, hU.2.2.1]
  let κ : GL (Fin (n + n)) L := ⟨(fromBlocks 1 B C 1).submatrix e.symm e.symm,
    (fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB],
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB]⟩
  have hint : ∀ i j, (fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1) i j ∈ Formalism.UG.intL L ∧
      (fromBlocks (1 : Matrix (Fin n) (Fin n) L) (-B) (-C) 1) i j ∈ Formalism.UG.intL L := by
    have h1 : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) L) a b ∈ Formalism.UG.intL L := fun a b => by
      rw [Matrix.one_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h2 : ∀ (f : Fin n → ℕ) (a b : Fin n),
        (Matrix.diagonal fun i => (ϖ : L) ^ f i - 1) a b ∈ Formalism.UG.intL L := fun f a b => by
      rw [diagonal_apply]; split_ifs
      · exact sub_mem (pow_mem (unif_mem_int hU) _) (one_mem _)
      · exact zero_mem _
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, neg_apply]
    all_goals first
      | exact ⟨h1 _ _, h1 _ _⟩
      | exact ⟨h2 _ _ _, neg_mem (h2 _ _ _)⟩
  have hM : (GlobalTheory.Doubling.blkMat e (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1).submatrix e e =
      fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) ((Matrix.diagonal fun i => (ϖ : L) ^ d i) * B) C 1 := by
    show ((fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) 0 0 1).submatrix e.symm e.symm *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [submatrix_mul_equiv, submatrix_submatrix]
    simp [fromBlocks_multiply]
  have h1 : (Matrix.diagonal fun i => (ϖ : L) ^ d i) + (Matrix.diagonal fun i => (ϖ : L) ^ d i) * B =
      Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hB, diagonal_mul_diagonal, diagonal_add]
    congr 1; funext i
    simp only [hu]
    rw [mul_sub, mul_one, add_sub_cancel, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ϖ.ne_zero]
    congr 1
    omega
  have h2 : C + 1 = Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hC, ← diagonal_one, diagonal_add]
    congr 1; funext i
    simp [hw]
  refine ⟨κ, ?_, mem_GLint_of_entries (fun i j => (hint _ _).1) (fun i j => (hint _ _).2), ?_, ?_⟩
  · show Formalism.UG.cT σ ((fromBlocks 1 B C 1).submatrix e.symm e.symm) * GlobalTheory.Doubling.blkMat e J (-J) *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm = GlobalTheory.Doubling.blkMat e J (-J)
    have hcT : Formalism.UG.cT σ ((fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1).submatrix e.symm e.symm) =
        (fromBlocks 1 C B 1).submatrix e.symm e.symm := by
      rw [Formalism.UG.cT, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose, hσu, hσw]
      simp [hB, hC, diagonal_transpose]
    rw [hcT, GlobalTheory.Doubling.blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    have e1 : C * J * C = 0 := by rw [Matrix.mul_assoc, hJC, ← Matrix.mul_assoc, hCB, Matrix.zero_mul]
    have e2 : B * J * B = 0 := by rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, hBC, Matrix.zero_mul]
    simp [Matrix.mul_neg, Matrix.neg_mul, hJB, hJC, e1, e2]
  · rw [GlobalTheory.Doubling.KeepsDiag, GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, h1, h2]
  · rw [GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, h1]

theorem secVal_unif_pow {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ)
    (k : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ k := by
  have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem sphericalDoublingSection_graph_diagonal_cartan [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q)
    {χ : Lˣ →* ℂˣ} (hχ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ) {s : ℂ} {Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ}
    (hΦ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (k₁ : GU σ n) (hk₁ : k₁ ∈ KU σ n) (k₂ : GU σ n)
    (hk₂ : k₂ ∈ KU σ n) :
    Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  obtain ⟨κ, hκG, hκI, hkeep, hlev⟩ := exists_kappa hU d (exp_rev hU ht)
  set e := finSumFinEquiv (m := n) (n := n)
  let K : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := ⟨κ, hκG⟩
  have hK : K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n := ⟨hκG, hκI⟩
  obtain ⟨x₁, hx₁⟩ := hk₁.2
  obtain ⟨x₂, hx₂⟩ := hk₂.2
  obtain ⟨y₁, hy₁⟩ := (inv_mem hk₁).2
  let p0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁)
  let r : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
  have hp0P : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n :=
    GlobalTheory.Doubling.mem_siegelOf.2 ((GlobalTheory.Doubling.keepsDiag_blkMat e).2 rfl)
  have hp0K : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨p0.2, GlobalTheory.Doubling.blkGL e (x₁, x₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₁]; rfl⟩
  have hrK : r ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨r.2, GlobalTheory.Doubling.blkGL e (x₂, y₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₂, hy₁]; rfl⟩
  have hp1P : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := by
    refine GlobalTheory.Doubling.mem_siegelOf.2 ?_
    change GlobalTheory.Doubling.KeepsDiag e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)
    rw [ht]
    exact hkeep
  let P0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨p0, hp0P⟩
  let P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨_, hp1P⟩
  have hdec : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂) = ((P0 * P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n) :
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n) * (K⁻¹ * r) := by
    rw [Subgroup.coe_mul]
    change _ = p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r)
    rw [show p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r) = p0 * GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * r by group]
    change GlobalTheory.Doubling.ioU σ e rfl (k₁ * t * k₂, 1) = GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁) *
      GlobalTheory.Doubling.ioU σ e rfl (t, 1) * GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
    rw [← map_mul, ← map_mul]
    congr 1
    ext1
    · rfl
    · simp
  have ha1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD σ n P1 = ϖ ^ (∑ i, (d i).toNat) := by
    apply Units.ext
    rw [GlobalTheory.Doubling.val_aOf, Units.val_pow_eq_pow_val]
    change (GlobalTheory.Doubling.leviMat e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)).det = _
    rw [ht, hlev, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdec, hΦ _ _ (mul_mem (inv_mem hK) hrK), map_mul, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_mul hq,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_unit q hχ _ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.v_aD_eq P0 hp0K), one_mul, ha1, secVal_unif_pow hU]
  rw [show ∑ i, max (d i) 0 = ((∑ i, (d i).toNat : ℕ) : ℤ) by push_cast; simp [Int.toNat_eq_max], zpow_natCast]

theorem sphSec_io_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (χ : Lˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  intro L _ _ _ ϖ σ q n hU χ hχ s Φ hΦ d t ht k₁ hk₁ k₂ hk₂
  exact sphericalDoublingSection_graph_diagonal_cartan hU hχ hΦ d t ht k₁ hk₁ k₂ hk₂

end GlobalTheory.UGraph

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (χ : Lˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  first | exact @GlobalTheory.UGraph.sphSec_io_diag | exact GlobalTheory.UGraph.sphSec_io_diag | (intros; apply GlobalTheory.UGraph.sphSec_io_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockTargetGlActionEqQuadraticAddNonRaising
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockTargetGlActionEqQuadraticAddNonRaising
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.FockTDec

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

section General

variable {σ : Type}

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  zero_mem' := fun P => by simp
  add_mem' := fun {L L'} h h' P => by
    rw [LinearMap.add_apply]
    exact (totalDegree_add _ _).trans (max_le (h P) (h' P))
  smul_mem' := fun c L h P => by
    rw [LinearMap.smul_apply]
    exact (totalDegree_smul_le _ _).trans (h P)

theorem one_mem : (1 : Module.End ℂ (MvPolynomial σ ℂ)) ∈ nonRaising σ := fun _ => le_rfl

theorem mul_mem {L L' : Module.End ℂ (MvPolynomial σ ℂ)} (h : L ∈ nonRaising σ) (h' : L' ∈ nonRaising σ) :
    L * L' ∈ nonRaising σ := fun P => (h _).trans (h' P)

theorem totalDegree_X_mul_pderiv (x y : σ) (P : MvPolynomial σ ℂ) :
    (X x * pderiv y P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s y = 0
  · simp [h0]
  · have hs' : (Finsupp.single y 1) + (s - Finsupp.single y 1) = s := by
      rw [add_tsub_cancel_of_le]
      rw [Finsupp.single_le_iff]; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    refine le_trans ?_ (le_totalDegree hs)
    have h1 := totalDegree_monomial_le (s - Finsupp.single y 1) (AddMonoidAlgebra.coeff P s * (s y : ℂ))
    have h2 : (s.sum fun _ e => e) = 1 + (s - Finsupp.single y 1).sum fun _ e => e := by
      conv_lhs => rw [← hs']
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2]
    exact Nat.add_le_add_left h1 1

theorem pderiv_mem (y : σ) : (pderiv y).toLinearMap ∈ nonRaising σ := by
  intro P
  change (pderiv y P).totalDegree ≤ _
  by_cases h : pderiv y P = 0
  · simp [h]
  · refine le_trans ?_ (totalDegree_X_mul_pderiv y y P)
    rw [totalDegree_mul_of_isDomain (X_ne_zero y) h]
    omega

theorem mul_pderiv_mem (x y : σ) :
    LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) * (pderiv y).toLinearMap ∈ nonRaising σ :=
  fun P => totalDegree_X_mul_pderiv x y P

theorem pderiv_mul_mem (x y : σ) :
    (pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) ∈ nonRaising σ := by
  classical
  intro P
  have e : ((pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) :
      Module.End ℂ (MvPolynomial σ ℂ)) P = pderiv y (X x * P) := rfl
  rw [e]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_X_mul_pderiv x y P) ?_)
  by_cases h : x = y
  · subst h; rw [pderiv_X_self, mul_one]
  · rw [pderiv_X_of_ne h, mul_zero, totalDegree_zero]; exact Nat.zero_le _

end General

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i l : Fin b) (j : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' l ≠ ε j then X (τ, i, j) * X (τ, l, j) else 0

theorem sgn_mul_self (e : Bool) : sgn e * sgn e = 1 := by
  cases e <;> simp [sgn]

theorem term_mem (i l : Fin b) (j : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  rw [smul_mul_smul_comm, sgn_mul_self, one_smul]
  by_cases hi : ε' i = ε j <;> by_cases hl : ε' l = ε j
  · simp only [hi, hl, if_true, ne_eq, not_true, and_false, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero]
    exact mul_pderiv_mem _ _
  · simp only [hi, hl, if_true, ne_eq, not_false_iff, and_self, if_false]
    rw [LinearMap.mulLeft_mul, Module.End.mul_eq_comp, sub_self]
    exact Submodule.zero_mem _
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (mul_mem (pderiv_mem _) (pderiv_mem _))
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (pderiv_mul_mem _ _)

def quadAll (Y : Matrix (Fin b) (Fin b) ℂ) : PolF D b a :=
  ∑ i, ∑ l, Y i l • ∑ j, quad τ ε ε' i l j

theorem quadAll_hom (Y : Matrix (Fin b) (Fin b) ℂ) : (quadAll τ ε ε' Y).IsHomogeneous 2 := by
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => ?_)
  unfold quad
  split_ifs
  · exact (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)
  · exact Submodule.zero_mem _

theorem fockQuadraticPart_ne_zero_of_offBlock_entry (Y : Matrix (Fin b) (Fin b) ℂ) (i₀ l₀ : Fin b) (j₀ : Fin a) (hi : ε' i₀ = ε j₀)
    (hl : ε' l₀ ≠ ε j₀) (hY : Y i₀ l₀ ≠ 0) : quadAll τ ε ε' Y ≠ 0 := by
  classical
  intro h0
  let pt : FVar D b a → ℂ := fun v => if v = (τ, i₀, j₀) ∨ v = (τ, l₀, j₀) then 1 else 0
  have hq : ∀ i l j, eval pt (quad τ ε ε' i l j) = if j = j₀ ∧ l = l₀ ∧ i = i₀ then 1 else 0 := by
    intro i l j
    unfold quad
    by_cases hc : ε' i = ε j ∧ ε' l ≠ ε j
    · rw [if_pos hc, map_mul, eval_X, eval_X]
      by_cases hj : j = j₀
      · subst hj
        have h1 : i ≠ l₀ := fun h => hl (h ▸ hc.1)
        have h2 : l ≠ i₀ := fun h => hc.2 (h ▸ hi)
        by_cases h3 : i = i₀ <;> by_cases h4 : l = l₀ <;> simp [pt, h1, h2, h3, h4]
      · simp [pt, hj]
    · rw [if_neg hc, map_zero, if_neg]
      rintro ⟨rfl, rfl, rfl⟩
      exact hc ⟨hi, hl⟩
  have := congrArg (eval pt) h0
  unfold quadAll at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, smul_eval, hq, map_zero, ite_and] at this
  apply hY
  simpa using this

theorem sub_mem (Y : Matrix (Fin b) (Fin b) ℂ) :
    fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) ∈ nonRaising (FVar D b a) := by
  have : fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
      ∑ i, ∑ l, Y i l • ∑ j, ((raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j)) +
        if i = l then (1 / 2 : ℂ) • 1 else 0) := by
    have hm : LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
        ∑ i, ∑ l, Y i l • ∑ j, LinearMap.mulLeft ℂ (quad τ ε ε' i l j) := by
      refine LinearMap.ext fun P => ?_
      simp [quadAll, Finset.sum_mul, LinearMap.sum_apply]
    rw [hm]
    unfold fockT
    simp only [← Finset.sum_sub_distrib, ← smul_sub]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    abel
  rw [this]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ (term_mem τ ε ε' i l j) ?_)
  split_ifs
  · exact Submodule.smul_mem _ _ one_mem
  · exact Submodule.zero_mem _

theorem fockT_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ), 0 < a → (∃ i l, ε' i ≠ ε' l ∧ Y i l ≠ 0 ∧ Y l i ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' Y ha ⟨i, l, hil, h1, h2⟩
  refine ⟨quadAll τ ε ε' Y, _, ?_, quadAll_hom τ ε ε' Y, sub_mem τ ε ε' Y, by abel⟩
  by_cases h : ε' i = ε ⟨0, ha⟩
  · exact fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y i l ⟨0, ha⟩ h (fun h' => hil (h.trans h'.symm)) h1
  · refine fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y l i ⟨0, ha⟩ ?_ h h2
    revert h hil
    cases ε' i <;> cases ε' l <;> cases ε ⟨0, ha⟩ <;> simp

end GlobalTheory.Chain.FockTDec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockTargetGlActionEqQuadraticAddNonRaisingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockTargetGlAction_eq_quadratic_add_nonRaising : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ), 0 < a → (∃ i l, ε' i ≠ ε' l ∧ Y i l ≠ 0 ∧ Y l i ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y = LinearMap.mulLeft ℂ Q + L := by
  first | exact @GlobalTheory.Chain.FockTDec.fockT_decomp | exact GlobalTheory.Chain.FockTDec.fockT_decomp | (intros; apply GlobalTheory.Chain.FockTDec.fockT_decomp <;> assumption)
end
end

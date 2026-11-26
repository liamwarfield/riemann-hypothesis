module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf

open PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem lowerC_apply' (M : Matrix (Fin (n + n)) (Fin (n + n)) K) (i j : Fin n) :
    lowerC M i j = M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) := rfl

theorem lowerC_siegel_mul {y : Matrix (Fin (n + n)) (Fin (n + n)) K} (hy : IsSiegelP y)
    (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    lowerC (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * lowerC W := by
  have hy' : ∀ i j : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := hy
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hy', zero_mul, Finset.sum_const_zero, zero_add, GlobalTheory.CompanionTheory.RatPtsUnn.blkD]

theorem lowerC_mul_unip (X : Matrix (Fin (n + n)) (Fin (n + n)) K) (b : Matrix (Fin n) (Fin n) K) :
    lowerC (X * blk4 1 b 0 1) = lowerC X := by
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]

end Blocks

variable {D : D7} {n : ℕ}

private theorem incA_injective' (D : D7) : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing D.host.F ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))
  haveI : Nontrivial (AF D.host.F ⊗[D.host.F] D.host.E) :=
    Function.Injective.nontrivial
      (Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective)
  exact (incA D).injective

theorem isUnit_det_of_mat (x : GF D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (h : mat (x : G D n) = g.map (incA D)) : IsUnit g.det := by
  obtain ⟨g', hg', -, hg'm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 (x : G D n) x.2
  have hgg : g = g' := Matrix.map_injective (incA_injective' D) (h.symm.trans hg'm)
  rw [hgg]
  exact hg'

private theorem mat_mul_eq_ite_of_hasMult {D : D7} {n : ℕ} (a b : G D n) : mat (a * b) = mat a * mat b := by
  simp only [mat, map_mul, Units.val_mul]

theorem cosetCell_rmulEquiv : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  intro D n q γ b h
  set q' := rmulEquiv (P D n) (GF D n) γ q with hq'
  have e3 : GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) :=
    calc GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = q' := Quotient.out_eq q'
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ q := rfl
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ (GlobalTheory.AutomorphicL2Unitary.mk _ q.out) :=
        congrArg (GlobalTheory.AutomorphicL2Unitary.rmul _ γ) (Quotient.out_eq q).symm
      _ = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) := GlobalTheory.AutomorphicL2Unitary.rmul_mk _ _
  obtain ⟨p, hp⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.mp e3
  have hp' : ((p : GF D n) : G D n) * (q'.out : G D n) = (q.out : G D n) * (γ : G D n) :=
    congrArg Subtype.val hp
  have hb : blk4 1 (b.map (incA D)) 0 1 = (blk4 1 b 0 1).map (incA D) := by
    have h1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := (incA D).mapMatrix.map_one
    have h0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := (incA D).mapMatrix.map_zero
    unfold blk4
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, h1, h0]
  have hm := congrArg mat hp'
  rw [mat_mul_eq_ite_of_hasMult, mat_mul_eq_ite_of_hasMult, h, mat_ratOf, mat_ratOf, mat_ratOf, hb, ← Matrix.map_mul,
    ← Matrix.map_mul] at hm
  have hm2 : ratOf (p : GF D n) * ratOf q'.out = ratOf q.out * blk4 1 b 0 1 :=
    Matrix.map_injective (incA_injective' D) hm
  have hpP : ((p : GF D n) : G D n) ∈ P D n := Subgroup.mem_subgroupOf.mp p.2
  have hS : IsSiegelP (ratOf (p : GF D n)) :=
    (GlobalTheory.CompanionTheory.RatPtsUnn.clause3 _ (p : GF D n).2 _ (mat_ratOf (p : GF D n))).mp hpP
  have hC : lowerC (ratOf q.out) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) * lowerC (ratOf q'.out) := by
    rw [← lowerC_mul_unip (ratOf q.out) b, ← hm2, lowerC_siegel_mul hS]
  have hU : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n))).det := by
    have hd := isUnit_det_of_mat (p : GF D n) (mat_ratOf (p : GF D n))
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero _ hS] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hinj : ∀ w, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ hU, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  simp only [cosetCell, cellKer]
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hC, ← Matrix.mulVec_mulVec]
  constructor
  · intro h0
    rw [h0, Matrix.mulVec_zero]
  · intro h0
    exact hinj _ h0

end GlobalTheory.CompanionTheory.SwUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotentStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_cell_invariant_unipotent : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | exact GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | (intros; apply GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

theorem exists_right_invariant {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ S : Set G, IsOpen S ∧ (1 : G) ∈ S ∧ ∀ s ∈ S, ∀ p : G, f.1.1.1 (p * s) = f.1.1.1 p := by
  have hopen : IsOpen {s : G | GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1} := f.1.2
  refine ⟨_, hopen, ?_, fun s hs p => ?_⟩
  · show GlobalTheory.PRep.ind H ρ 1 f.1.1 = f.1.1
    simp
  · have hs' : GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1 := hs
    exact congrFun (congrArg Subtype.val hs') p

theorem exists_compact_support {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ C : Set G, IsCompact C ∧ ∀ p : G, f.1.1.1 p ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, p = h * c :=
  f.2

section Column

variable (k : Type) [Field k]

def col (n : ℕ) (p : Mir k n) : Fin n → k :=
  fun j => ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc j) (Fin.last n)

theorem last_last (n : ℕ) (p : Mir k n) :
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have h := congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2) (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using h

theorem last_column_entry_product_formula (n : ℕ) (a : Fin n → k) (A : Matrix (Fin n) (Fin n) k)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hP : P (Fin.last n) (Fin.last n) = 1) (j : Fin n) :
    ((1 + colMat k n a) * glEmbMat k n A * P) (Fin.castSucc j) (Fin.last n) =
      a j + (A.mulVec (fun l => P (Fin.castSucc l) (Fin.last n))) j := by
  rw [add_mul, one_mul, GlobalTheory.BZMir.colMat_mul_glEmbMat, add_mul, Matrix.add_apply]
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.mulVec,
    dotProduct, hP, Fin.castSucc_ne_last]
  all_goals ring

theorem col_uM_levi_mul (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) (p : Mir k n) :
    col k n (uM k n a * levi k n g * p) = a + (g : Matrix (Fin n) (Fin n) k).mulVec (col k n p) := by
  funext j
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_column_entry_product_formula k n a (g : Matrix (Fin n) (Fin n) k)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_last k n p) j

theorem col_one (n : ℕ) : col k n 1 = 0 := by
  funext j
  simp [GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col, Matrix.one_apply, Fin.castSucc_ne_last]

theorem col_uM_levi (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) :
    col k n (uM k n a * levi k n g) = a := by
  have h := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul k n a g 1
  rwa [mul_one, GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_one, Matrix.mulVec_zero, add_zero] at h

end Column

section Top

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_midV (i t : ℕ) : Continuous (midV k i t) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.castAdd t l)
    simp only [Fin.append_left, Pi.zero_apply]
    exact continuous_const
  | right l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.natAdd i l)
    simp only [Fin.append_right]
    exact continuous_apply l

theorem continuous_col_inv (n : ℕ) : Continuous (fun c : Mir k n => col k n c⁻¹) :=
  continuous_pi fun j =>
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem (Fin.castSucc j) (Fin.last n)

theorem isLocallyConstant_uM {Z : Type} (n : ℕ) (F : Mir k n → Z) (S : Set (Mir k n)) (hS : IsOpen S)
    (h1 : (1 : Mir k n) ∈ S) (hF : ∀ s ∈ S, ∀ p, F (p * s) = F p) (g : GL (Fin n) k) :
    IsLocallyConstant (fun y : Fin n → k => F (uM k n y * levi k n g)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y₀
  have hu := GlobalTheory.CompanionTheory.BZPsiPG.Cont.continuous_uM k n
  set L := GlobalTheory.BZMir.levi k n g
  let φ : (Fin n → k) → GlobalTheory.BZMir.Mir k n := fun y => L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) * L
  have hφ : Continuous φ :=
    (continuous_const.mul (hu.comp (continuous_id.sub continuous_const))).mul continuous_const
  refine ⟨φ ⁻¹' S, hS.preimage hφ, ?_, fun y hy => ?_⟩
  · show L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y₀ - y₀) * L ∈ S
    rw [sub_self, GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, mul_one, inv_mul_cancel]
    exact h1
  · have hadd : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y =
        GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
      congr 1
      abel
    have hy' : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L * φ y := by
      rw [hadd]
      simp only [φ]
      group
    show F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L) = F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L)
    rw [hy']
    exact hF _ hy _

end Top

theorem fibV_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ _ f g
  constructor
  · obtain ⟨S, hS, h1, hSf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_right_invariant _ _ f
    exact (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.isLocallyConstant_uM k (i + t) _ S hS h1 hSf g).comp_continuous
      (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_midV k i t)
  · obtain ⟨C, hC, hCf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_compact_support _ _ f
    let proj : GlobalTheory.BZMir.Mir k (i + t) → Fin t → k := fun c j =>
      -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j))
    have hproj : Continuous proj := continuous_pi fun j =>
      ((continuous_apply (Fin.natAdd i j)).comp
        (continuous_const.matrix_mulVec (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_col_inv k (i + t)))).neg
    refine HasCompactSupport.of_support_subset_isCompact (hC.image hproj) ?_
    intro v hv
    obtain ⟨h, hh, c, hc, hp⟩ := hCf (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) g) hv
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, q, hxq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t ⟨h, hh⟩
    have hxq' : h = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) *
        GlobalTheory.BZMir.levi k (i + t) q := hxq
    have key : GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x = GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v +
        (g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹ := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul, hp, mul_inv_cancel_right, hxq',
        GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi]
    funext j
    have hj := congrFun key (Fin.natAdd i j)
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.topV, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_right, Pi.add_apply, Pi.zero_apply] at hj
    show -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j)) = v j
    rw [neg_eq_iff_add_eq_zero, add_comm]
    exact hj.symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_function_locally_constant_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.SwUnf.BigCell

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem cT_mul_sq (σ : K →+* K) (x y : Matrix (Fin n) (Fin n) K) : cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem cT_blk4 (σ : K →+* K) (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem block_identity_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem lowerLeft_block {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : lowerC (blk4 a b c d) = c := by
  ext i j
  simp [lowerC, blk4]

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b, M = blk4 a b (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, ?_⟩
  have h : Matrix.fromBlocks (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) =
      M.submatrix finSumFinEquiv finSumFinEquiv :=
    Matrix.fromBlocks_toBlocks _
  unfold blk4
  rw [h]
  ext i j
  simp

theorem isSiegelParabolic_iff (M : Matrix (Fin (n + n)) (Fin (n + n)) K) : IsSiegelP M ↔ lowerC M = 0 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem cellKer_eq_bot_iff' {E : Type} [Field E] (C : Matrix (Fin n) (Fin n) E) :
    LinearMap.ker C.mulVecLin = ⊥ ↔ IsUnit C.det := by
  rw [LinearMap.ker_eq_bot, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  rfl

abbrev cellM (b : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 0 1 (-1) (-b)

theorem cellM_mul (b : Matrix (Fin n) (Fin n) K) : cellM b * blk4 (-b) (-1) 1 0 = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem mul_cellM (b : Matrix (Fin n) (Fin n) K) : blk4 (-b) (-1) 1 0 * cellM b = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem cellM_det (b : Matrix (Fin n) (Fin n) K) : IsUnit (cellM b).det :=
  Matrix.isUnit_det_of_left_inverse (mul_cellM b)

theorem cellM_inv (b : Matrix (Fin n) (Fin n) K) : (cellM b)⁻¹ = blk4 (-b) (-1) 1 0 :=
  Matrix.inv_eq_right_inv (cellM_mul b)

theorem lower_rel (σ : K →+* K) {A B C Dd : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B C Dd)) : Dd * cT σ C = C * cT σ Dd := by
  have hJJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 (-1) 1 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have h0 : cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0 * blk4 A B C Dd = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 A B C Dd = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  have h2 := mul_eq_one_comm.1 h1
  have h3 : blk4 A B C Dd * blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) = blk4 0 (-1) 1 0 := by
    calc _ = blk4 A B C Dd * (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 0 (-1) 1 0 := by
          simp only [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h2, one_mul]
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h3
  obtain ⟨-, -, -, h4⟩ := blockMatrixTwoByTwoFin_injective h3
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero] at h4
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg, add_comm] using h4)

theorem herm_of_rel (σ : K →+* K) {C Dd : Matrix (Fin n) (Fin n) K} (hC : IsUnit C.det)
    (h : Dd * cT σ C = C * cT σ Dd) : cT σ (C⁻¹ * Dd) = C⁻¹ * Dd := by
  have a1 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have b1 : cT σ C * cT σ C⁻¹ = 1 := by rw [← cT_mul_sq, a1, cT_one_sq]
  have b2 : C⁻¹ * Dd * cT σ C = cT σ Dd := by rw [mul_assoc, h, ← mul_assoc, a1, one_mul]
  rw [cT_mul_sq, ← b2, mul_assoc, b1, mul_one]

theorem lower_unit {x : Matrix (Fin (n + n)) (Fin (n + n)) K} (hx : IsUnit x.det) (b : Matrix (Fin n) (Fin n) K)
    (hS : IsSiegelP (x * (cellM b)⁻¹)) : IsUnit (lowerC x).det := by
  rw [cellM_inv] at hS
  set S := x * blk4 (-b) (-1) 1 0 with hSd
  have hSx : S * cellM b = x := by rw [hSd, mul_assoc, mul_cellM, mul_one]
  have hdet : IsUnit S.det := by
    rw [hSd, Matrix.det_mul]
    exact hx.mul (Matrix.isUnit_det_of_left_inverse (cellM_mul b))
  have hd : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD S).det := by
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero S hS] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨a, c, hb⟩ := exists_blockMatrixTwoByTwoFin_eq S
  have h0 : lowerC S = 0 := (isSiegelParabolic_iff S).1 hS
  rw [h0] at hb
  have e : lowerC x = -GlobalTheory.CompanionTheory.RatPtsUnn.blkD S := by
    rw [← hSx, hb, cellM, submatrix_fromBlocks_mul, lowerLeft_block, ← hb]
    simp
  rw [e, ← Matrix.isUnit_iff_isUnit_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).2 hd).neg

theorem of_lower_unit (σ : K →+* K) {x : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hu : IsUnitary σ (blk4 0 1 (-1) 0) x) (hC : IsUnit (lowerC x).det) :
    cT σ ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) = (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x ∧
      IsSiegelP (x * (cellM ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x))⁻¹) := by
  obtain ⟨a, b, hb⟩ := exists_blockMatrixTwoByTwoFin_eq x
  have hu' : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b (lowerC x) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)) := by
    rw [← hb]
    exact hu
  refine ⟨herm_of_rel σ hC (lower_rel σ hu'), ?_⟩
  rw [cellM_inv, isSiegelParabolic_iff]
  have a2 : lowerC x * (lowerC x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  generalize hl : (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = l
  have e : lowerC x * l = GlobalTheory.CompanionTheory.RatPtsUnn.blkD x := by
    rw [← hl, ← mul_assoc, a2, one_mul]
  conv_lhs => rw [hb]
  rw [submatrix_fromBlocks_mul, lowerLeft_block, mul_neg, e]
  simp

end Field

variable {D : D7} {n : ℕ}

theorem ratOf_spec (γ : GF D n) : IsUnit (ratOf γ).det ∧
    IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (blk4 0 1 (-1) 0) (ratOf γ) := by
  obtain ⟨g, hd, hu, hm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 γ.1 γ.2
  have e : ratOf γ = g := Matrix.map_injective incA_injective ((mat_ratOf γ).symm.trans hm)
  rw [e]
  exact ⟨hd, hu⟩

theorem mat_cell_rat {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : Matrix (Fin n) (Fin n) D.host.E)
    (hu : mat u = blk4 1 (b.map (incA D)) 0 1) : mat (w * u) = (cellM b).map (incA D) := by
  rw [mat_cell hw hu, cellM, blk4_map_alt]
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  have e2 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = -1 := by
    have := map_neg (incA D).mapMatrix (1 : Matrix (Fin n) (Fin n) D.host.E)
    rwa [map_one] at this
  have e3 : (-b).map (incA D) = -(b.map (incA D)) := map_neg (incA D).mapMatrix b
  rw [e0, e1, e2, e3]

theorem exists_hermQ (l : ratHerm D n) : ∃ b : HermQ D n, b.1.map (incA D) = l.1.1 := by
  have hm : l.1.1 ∈ ratMx D n n := l.2
  obtain ⟨b, hb⟩ := hm
  have hb' : b.map (incA D) = l.1.1 := hb
  have hadj : adj (b.map (incA D) : Mx D n n) = b.map (incA D) := by
    rw [hb']
    exact l.1.2
  refine ⟨⟨b, fun i j => incA_injective ?_⟩, hb'⟩
  exact congrFun (congrFun hadj i) j

theorem bigCell : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  intro D n w hw nb hnb
  choose β hβ using exists_hermQ (D := D) (n := n)
  have hu : ∀ l, mat (nb l.1) = blk4 1 ((β l).1.map (incA D)) 0 1 := fun l => by
    rw [hβ]
    exact hnb l.1
  let c : ratHerm D n → GF D n := fun l => ⟨w * nb l.1, cell_mem_GF hw (β l) (hu l)⟩
  have hc : ∀ l, mat (c l).1 = (cellM (β l).1).map (incA D) := fun l => mat_cell_rat hw _ (hu l)
  refine ⟨fun l => mk ((P D n).subgroupOf (GF D n)) (c l), ?_, ?_, ?_⟩
  · intro l l' h
    obtain ⟨δ, hδ⟩ := mk_eq_iff.1 h
    have hP : (w * nb l'.1) * (w * nb l.1)⁻¹ ∈ P D n := by
      have e : (w * nb l'.1) * (w * nb l.1)⁻¹ = δ.1.1 := by
        have := congrArg Subtype.val hδ
        change δ.1.1 * (w * nb l.1) = w * nb l'.1 at this
        rw [← this]
        exact mul_inv_cancel_right _ _
      rw [e]
      exact Subgroup.mem_subgroupOf.1 δ.2
    have hbb := cell_inj hw (hu l) (hu l') hP
    apply Subtype.ext
    apply Subtype.ext
    rw [← hβ l, ← hβ l', hbb]
  · intro q
    have hspec := ratOf_spec (Quotient.out q)
    have hker : cosetCell q = ⊥ ↔ IsUnit (lowerC (ratOf (Quotient.out q))).det :=
      cellKer_eq_bot_iff' _
    rw [hker]
    constructor
    · intro hC
      obtain ⟨hh, hS⟩ := of_lower_unit _ hspec.2 hC
      set lam := (lowerC (ratOf (Quotient.out q)))⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (Quotient.out q)) with hlam
      let b : HermQ D n := ⟨lam, fun i j => congrFun (congrFun hh i) j⟩
      let l : ratHerm D n := ⟨⟨lam.map (incA D), adj_map_herm b⟩, ⟨lam, rfl⟩⟩
      have hbl : (β l).1 = lam := Matrix.map_injective incA_injective (hβ l)
      refine ⟨l, ?_⟩
      have hmk := (GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) (Quotient.out q)
        (cellM_det _) (hc l) (mat_ratOf _)).2 (by rw [hbl]; exact hS)
      exact hmk.trans (Quotient.out_eq q)
    · rintro ⟨l, rfl⟩
      have hmk : mk ((P D n).subgroupOf (GF D n)) (c l) =
          mk ((P D n).subgroupOf (GF D n)) (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l))) :=
        (Quotient.out_eq _).symm
      exact lower_unit hspec.1 _ ((GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) _
        (cellM_det _) (hc l) (mat_ratOf _)).1 hmk)
  · intro f hf l y
    exact term_mk hf y (c l)

end GlobalTheory.CompanionTheory.SwUnf.BigCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParamStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_cell_cosets_hermitian_param : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | exact GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | (intros; apply GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ConjSat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem locU_eq_of_under {w u : HeightOneSpectrum (𝓞 E)}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : locU n u = locU n w := by
  simp only [locU, h]

abbrev flipGL (w : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E) ≃* GL (Fin n) (w.adicCompletion E) :=
  GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n

theorem flipGL_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)) :
    flipGL w g = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem continuous_flipGL (w : HeightOneSpectrum (𝓞 E)) : Continuous (flipGL (n := n) w) := by
  have : (flipGL (n := n) w : _ → _) = fun g => GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
    funext (flipGL_eq w)
  rw [this]
  exact (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1))

theorem cLoc_eq_flipGL (x : UA E n) (w : HeightOneSpectrum (𝓞 E)) :
    cLoc w x = flipGL w (cLoc (GlobalTheory.ThetaSatake.cw w) x) :=
  (GlobalTheory.BCT.LocCpt.cLoc_eq_invT x w).trans (flipGL_eq w _).symm

def flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) : SmIrr (GLw n (GlobalTheory.ThetaSatake.cw w)) where
  V := σ.V
  ρ := σ.ρ.comp (flipGL w).toMonoidHom
  smooth v := (σ.smooth v).preimage (continuous_flipGL w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (flipGL w).surjective σ.irred

theorem hasSatGL_flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) {B : Multiset ℂˣ}
    (h : HasSatGL w σ.ρ B) : HasSatGL (GlobalTheory.ThetaSatake.cw w) (flipIrr σ).ρ (B.map (·⁻¹)) := by
  refine GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w).symm (fun a => ?_)
    (GlobalTheory.ThetaSatake.absNorm_cw w) (LinearEquiv.refl ℂ σ.V) (fun g x => ?_) h
  · have := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w).2.2 ((GlobalTheory.ThetaSatake.cloc w).symm a)
    exact (this.symm.trans (congrArg _ ((GlobalTheory.ThetaSatake.cloc w).apply_symm_apply a)))
  · change σ.ρ (flipGL w ((flipGL w).symm g)) x = σ.ρ g x
    rw [MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.ConjSat


open GlobalTheory.CompanionTheory.ConjSat in
theorem GlobalTheory.CompanionTheory.ConjSat.satConj : PositivityTheory.Rg.BcB.F.RS.SatConj := by
  intro E _ _ _ n π w u B _ _ hc ⟨σ, ⟨hirr, f, f0, hf, hfx⟩, hB⟩
  obtain rfl : u = GlobalTheory.ThetaSatake.cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
  refine ⟨flipIrr σ, ⟨(flipIrr σ).irred, f, f0, hf, fun x v => ?_⟩, hasSatGL_flipIrr σ hB⟩
  have hx : (x : UA E n) ∈ locU n w := locU_eq_of_under hc.1 ▸ x.2
  have := hfx ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply] at this
  change f (σ.ρ (flipGL w (cLoc _ x.1)) v) = _
  rw [← cLoc_eq_flipGL]
  exact this

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBound
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.JtUnif

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel GlobalTheory.Eis GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.SiegelFormula

variable {D : D7}

abbrev ht (D : D7) (n : ℕ) (g : G D n) : ℝ≥0 := iwAbs (modP (D := D) (n := n)) (K D n) g

theorem continuous_ht (n : ℕ) : Continuous (ht D n) := by
  exact (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).continuous_iwAbs
    GlobalTheory.StdUnn.HeightExists.isClosed_P GlobalTheory.StdUnn.PolesModel.continuous_modP
    GlobalTheory.StdUnn.HeightExists.isCompact_K

theorem norm_le_of_law {n : ℕ} {χ : (AE D)ˣ →* Circle} {t : ℂ} {f : G D n → ℂ} (hc : Continuous f)
    (hl : ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      f (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) t * f g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖f g‖ ≤ C * (ht D n g : ℝ) ^ t.re := by
  obtain ⟨C, hC⟩ := (GlobalTheory.StdUnn.HeightExists.isCompact_K (D := D) (n := n)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
  have hlaw : GlobalTheory.Doubling.IndLaw GlobalTheory.StdUnn.PolesModel.modP (χ.comp GlobalTheory.StdUnn.PolesModel.detP) t f := by
    intro p g
    exact hl p.1 p.2 ((GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n)) p) rfl g
  exact (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).norm_le hlaw
    (fun k hk => (hC k hk).trans (le_max_left _ _)) g

theorem ht_mul_le {n : ℕ} {S : Set (G D n)} (hS : IsCompact S) :
    ∃ C : ℝ≥0, ∀ x, ∀ u ∈ S, ht D n (x * u) ≤ C * ht D n x := by
  obtain ⟨C, hC⟩ := ((GlobalTheory.StdUnn.HeightExists.isCompact_K (D := D) (n := n)).prod hS).image
    ((continuous_ht (D := D) n).comp continuous_mul) |>.bddAbove
  refine ⟨C, fun x u hu => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).1 x
  have h1 : ht D n (↑p * k * u) = GlobalTheory.StdUnn.PolesModel.modP p * ht D n (k * u) := by
    rw [mul_assoc]
    exact (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).iwAbs_left p (k * u)
  have h2 : ht D n (↑p * k) = GlobalTheory.StdUnn.PolesModel.modP p :=
    (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).iwAbs_mul p hk
  have h3 : ht D n (k * u) ≤ C := hC ⟨(k, u), Set.mk_mem_prod hk hu, rfl⟩
  calc ht D n (↑p * k * u) = GlobalTheory.StdUnn.PolesModel.modP p * ht D n (k * u) := h1
    _ ≤ GlobalTheory.StdUnn.PolesModel.modP p * C := by gcongr
    _ = C * ht D n (↑p * k) := by rw [h2, mul_comm]

theorem continuous_block_matrix {n : ℕ} {X : Type} [TopologicalSpace X] {f : X → Mx D n n} (hf : Continuous f) :
    Continuous fun x => (blk4 1 (f x) 0 1 : Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.blk4
  exact (Continuous.matrix_fromBlocks continuous_const hf continuous_const continuous_const).matrix_submatrix _ _

theorem exists_continuous_unip (n : ℕ) :
    ∃ N : hermA D n → G D n, Continuous N ∧ ∀ b, mat (N b) = blk4 1 b.1 0 1 := by
  have hex : ∀ b : hermA D n, ∃ g : G D n, mat g = blk4 1 b.1 0 1 :=
    fun b => (GlobalTheory.StdUnn.Model.exists_unip (D := D) b.1).2 b.2
  choose N hN using hex
  refine ⟨N, ?_, hN⟩
  have hinv : ∀ b, mat (N b)⁻¹ = blk4 1 (-b.1) 0 1 := by
    intro b
    have h1 : mat (N b) * blk4 1 (-b.1) 0 1 = 1 := by
      rw [hN, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      simp [GlobalTheory.StdUnn.Model.block_matrix_one]
    calc mat (N b)⁻¹ = mat (N b)⁻¹ * (mat (N b) * blk4 1 (-b.1) 0 1) := by rw [h1, mul_one]
      _ = blk4 1 (-b.1) 0 1 := by
        rw [← mul_assoc, ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one,
          one_mul]
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_block_matrix continuous_subtype_val).congr (fun b => (hN b).symm)
  · exact (continuous_block_matrix continuous_subtype_val.neg).congr (fun b => (hinv b).symm)

theorem exists_hermQ {n : ℕ} (c : ratHerm D n) : ∃ b : HermQ D n, b.1.map (incA D) = c.1.1 := by
  obtain ⟨M, hM⟩ := c.2
  refine ⟨⟨M, fun i j => ?_⟩, hM⟩
  have hM' : M.map (incA D) = c.1.1 := hM
  have hh : GlobalTheory.MixModel.adj (c.1.1 : Mx D n n) = c.1.1 := c.1.2
  have hij := congrFun (congrFun hh i) j
  rw [← hM'] at hij
  have hij' : Formalism.L2.Theta.cA D (incA D (M j i)) = incA D (M i j) := by
    simpa [GlobalTheory.MixModel.adj] using hij
  apply GlobalTheory.RatAut.incA_inj
  rw [← hij']
  simp [Formalism.L2.Theta.cA, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

private theorem leftInv_ht {n : ℕ} : GlobalTheory.AutomorphicL2Unitary.LeftInv (P D n ⊓ GF D n) (ht D n) := by
  intro γ hγ g
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 ((GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n)) ⟨γ, hγ.1⟩) rfl
  have h1 : GlobalTheory.StdUnn.PolesModel.modP (⟨γ, hγ.1⟩ : P D n) = 1 := by
    show GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det ((GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n)) ⟨γ, hγ.1⟩)) = 1
    rw [hu]
    exact GlobalTheory.Doubling.absE_inclR u
  have h := (GlobalTheory.StdUnn.PolesModel.isIwasawa (D := D) (n := n)).iwAbs_left ⟨γ, hγ.1⟩ g
  rw [h1, one_mul] at h
  exact h

theorem summable_ht {n : ℕ} {s₁ : ℂ} (hs : (n : ℝ) / 2 < s₁.re) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0)
    {N : hermA D n → G D n} (hN : ∀ b, mat (N b) = blk4 1 b.1 0 1) :
    Summable fun c : ratHerm D n => (ht D n (w * N c.1) : ℝ) ^ (s₁ + (n : ℂ) / 2).re := by
  have hmem : ∀ c : ratHerm D n, w * N c.1 ∈ GF D n := fun c => by
    obtain ⟨b, hb⟩ := exists_hermQ c
    exact GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.cell_mem_GF hw b (by rw [hN, hb])
  let i : ratHerm D n → GlobalTheory.Eis.Cosets (P D n) (GF D n) :=
    fun c => GlobalTheory.AutomorphicL2Unitary.mk ((P D n).subgroupOf (GF D n)) ⟨w * N c.1, hmem c⟩
  have hi : Function.Injective i := by
    intro c c' h
    have h' : (⟨w * N c'.1, hmem c'⟩ : GF D n) * (⟨w * N c.1, hmem c⟩)⁻¹ ∈ (P D n).subgroupOf (GF D n) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    rw [Subgroup.mem_subgroupOf] at h'
    have e := GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.cell_inj hw (hN c.1) (hN c'.1) (by simpa using h')
    exact Subtype.ext (Subtype.ext e)
  have hs' := (GlobalTheory.StdUnn.PolesModel.summable_spherical (D := D) (n := n) s₁.re hs).comp_injective hi
  refine hs'.congr (fun c => ?_)
  simp only [Function.comp_apply, i]
  rw [GlobalTheory.Eis.term_mk leftInv_ht, mul_one]
  congr 1
  simp

theorem jt_bound {r : ℕ} {V : HSp D} (hV : 2 * r < V.rank) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank r)} {ω : G D r →* Module.End ℂ (schwartzA θ V.rank r)}
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank r) (hc : Continuous fun g : G D r => (ω g Φ).1 0)
    (Kc : Set (hermA D r)) (hK : IsCompact Kc) :
    ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ Kc, ‖Jt ψ V μ Φ.1 (b + c.1)‖ ≤ u c := by
  obtain ⟨w, hw⟩ := GlobalTheory.StdUnn.Model.exists_weyl (D := D) (n := r)
  obtain ⟨N, hNc, hN⟩ := exists_continuous_unip (D := D) r
  obtain ⟨C, hC0, hC⟩ := norm_le_of_law (t := GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2) hc
    (fun p hp a ha g => GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law D r ψ χ θ V μ ω hω Φ p hp a ha g)
  obtain ⟨C', hC'⟩ := ht_mul_le (D := D) (n := r) (hK.image hNc)
  have hV' : (2 * r : ℝ) < V.rank := by exact_mod_cast hV
  have hs : (r : ℝ) / 2 < (GlobalTheory.StdUnn.s0 V r).re := by
    simp [GlobalTheory.StdUnn.s0]
    linarith
  have hsum := summable_ht hs hw hN
  have ht0 : 0 ≤ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re := by
    simp [GlobalTheory.StdUnn.s0]
    positivity
  refine ⟨fun c => C * (C' : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re *
    (ht D r (w * N c.1) : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re, hsum.mul_left _, fun c b hb => ?_⟩
  have e1 : Jt ψ V μ Φ.1 (b + c.1) = (ω (w * N (b + c.1)) Φ).1 0 :=
    (GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.cell_value hω hw (hN (b + c.1)) Φ).symm
  have e2 : N (b + c.1) = N c.1 * N b := by
    apply GlobalTheory.StdUnn.LeftInvSect.mat_inj
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hN, hN, hN, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp
  have h2 : ht D r (w * N c.1 * N b) ≤ C' * ht D r (w * N c.1) := hC' _ _ ⟨b, hb, rfl⟩
  have h2' : (ht D r (w * N c.1 * N b) : ℝ) ≤ (C' : ℝ) * ht D r (w * N c.1) := by exact_mod_cast h2
  rw [e1, e2, ← mul_assoc]
  calc ‖(ω (w * N c.1 * N b) Φ).1 0‖
      ≤ C * (ht D r (w * N c.1 * N b) : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re := hC _
    _ ≤ C * ((C' : ℝ) * ht D r (w * N c.1)) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h2' ht0) hC0
    _ = C * (C' : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re *
          (ht D r (w * N c.1) : ℝ) ^ (GlobalTheory.StdUnn.s0 V r + (r : ℂ) / 2).re := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        ring

theorem exists_weil_value (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (lam : D.host.F) (hlam0 : lam ≠ 0) (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (Mx D B.rank A.rank))
    (𝓖 : Set (Mx D B.rank A.rank)) (hcov : IsCovolOne (ratMx D B.rank A.rank) ν 𝓖) (Φ : schwartzA θ B.rank A.rank) :
    ∃ (χ : (AE D)ˣ →* Circle) (ω : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)),
      IsWeilSch (shift ψ lam) χ θ B ν ω ∧ Continuous fun γ : G D A.rank => (ω γ Φ).1 0 := by
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam0
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hμ : IsSkew μ := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨χ, hχ₁, hχ₂⟩ := GlobalTheory.RawLift.exists_hecke_resEta D B.rank
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨ω, hW⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (dblSp A) B 1 χ hψ
    ⟨continuous_const, fun _ => rfl⟩ hχ₁ hr1 hχ₂
  obtain ⟨omS, hT⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A B χ ω hW ν 𝓖 hcov θ hθ κ
  have hWS : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν omS :=
    ⟨GlobalTheory.StdUnn.transport_levi D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.Unip.transport_unip D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.WeylStd.main D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam⟩
  obtain ⟨f, hf, hfΦ⟩ := ((GlobalTheory.SchSchwartzAll.schSchwartz D) ψ hψ θ hθ A B ν 𝓖 hcov).2.1 Φ.1 Φ.2
  have hΦ : Φ.1 = sch ψ A B ν 𝓖 (ω (((1 : siegel A) : GA D (dblSp A))⁻¹, 1) f) := by
    simp only [OneMemClass.coe_one, inv_one, Prod.mk_one_one, map_one, Module.End.one_apply]
    exact hfΦ.symm
  obtain ⟨-, -, hact⟩ := GlobalTheory.StdUnn.flat_swSec_eq_sect D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam 1 1 f hf Φ hΦ
  have hact' : ∀ g, (omS (κ g) Φ).1 = sch ψ A B ν 𝓖 (ω (g, 1) f) := fun g => by
    have := hact g; rwa [OneMemClass.coe_one, mul_one] at this
  have hval : ∀ g, swSection A B ν 𝓖 ω f g = 1 * (fun γ => (omS γ Φ).1 0) (κ (g * 1)) := fun g => by
    simp only [one_mul, mul_one]
    rw [hact' g, GlobalTheory.Core.Rk.IP.swSection_eq_swSec]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, sch, mixS_dblDec_zero]
  refine ⟨χ⁻¹, omS, hWS, ?_⟩
  have e : (fun γ : G D A.rank => (omS γ Φ).1 0) = swSection A B ν 𝓖 ω f ∘ κ.symm := by
    funext γ
    have := hval (κ.symm γ)
    simp only [one_mul, mul_one, MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e]
  exact (GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous D ψ A B χ ω hW f hf ν 𝓖 hcov).comp
    (GlobalTheory.CompanionTheory.ChartSymm.continuous_symm D A μ hμ κ hκ)

theorem jt_unif : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r))
    (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r →
    ∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧
      ∀ c : ratHerm D r, ∀ b ∈ K, ‖Jt ψ V μ φ (b + c.1)‖ ≤ u c := by
  intro D r V ψ θ μ φ hV hψ hθ h𝓕 hφ Kc hK
  obtain ⟨𝓕, h𝓕⟩ := h𝓕
  obtain ⟨A, hA⟩ : ∃ A : HSp D, A.rank = r :=
    ⟨Formalism.BasicNotions.Examples₂.stdSpace (fun x hx => hx.map (starRingEnd D.host.E).toIntAlgHom) r (fun _ => false) 0 0, rfl⟩
  subst hA
  obtain ⟨ψ₀, hstd, a, ha, hψa⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = GlobalTheory.StdUnn.shift ψ₀ a := AddChar.ext _ _ (fun x => by rw [hψa]; rfl)
  obtain ⟨χ, ω, hω, hc⟩ := exists_weil_value A V ψ₀ hstd a ha θ hθ μ 𝓕 h𝓕 ⟨φ, hφ⟩
  subst hsh
  exact jt_bound hV hω ⟨φ, hφ⟩ hc Kc hK

end GlobalTheory.CompanionTheory.JtUnif

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_locally_summable_bound : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → ∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖Jt ψ V μ φ (b + c.1)‖ ≤ u c := by
  first | exact @GlobalTheory.CompanionTheory.JtUnif.jt_unif | exact GlobalTheory.CompanionTheory.JtUnif.jt_unif | (intros; apply GlobalTheory.CompanionTheory.JtUnif.jt_unif <;> assumption)
end
end

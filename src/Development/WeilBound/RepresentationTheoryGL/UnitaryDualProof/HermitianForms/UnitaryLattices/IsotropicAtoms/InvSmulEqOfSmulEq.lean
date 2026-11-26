module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpen
open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.ComapLat

theorem comap_mulVec_compact_open : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  intro k _ _ _ _ n g hg A hc ho
  haveI : IsTopologicalRing k := inferInstance
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hcont : ∀ m : Matrix (Fin n) (Fin n) k, Continuous (fun x : Fin n → k => m.mulVec x) :=
    fun m => continuous_const.matrix_mulVec continuous_id
  have hset : ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k))
      = (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k)) := rfl
  rw [hset]
  refine ⟨?_, ho.preimage (hcont g)⟩
  have himg : (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k))
      = (fun x : Fin n → k => g⁻¹.mulVec x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.mulVec x, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet,
        Matrix.one_mulVec]
      exact hy
  rw [himg]
  exact hc.image (hcont g⁻¹)

end GlobalTheory.CompanionTheory.Dblock.ComapLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpenStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_isOpen_comap_mulVecLin : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | exact GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | (intros; apply GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup
open Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Topology

theorem isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB

end GlobalTheory.CompanionTheory.Topology
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroupStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_sup_addSubgroup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | exact GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | (intros; apply GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhds
open Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.CharDual

theorem exists_compact_annihilator_subset : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) →
    ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  intro k _ _ _ _ ψ _ hψ n S hS
  obtain ⟨x₁, hx₁⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext x; simp [h x])
  rw [nhds_pi] at hS
  obtain ⟨⟨I, γ⟩, ⟨-, hγ⟩, hsub⟩ :=
    (Filter.hasBasis_pi fun _ : Fin n => IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hS
  let ε : Fin n → ValueGroupWithZero k := fun i => valuation k x₁ / γ i
  let Ξ : AddSubgroup (Fin n → k) :=
    { carrier := {ξ | ∀ i, valuation k (ξ i) ≤ ε i}
      zero_mem' := fun i => by simp
      add_mem' := fun {a b} ha hb i =>
        ((valuation k).map_add_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by
        simpa [Valuation.map_neg] using ha i }
  refine ⟨Ξ, ?_, fun t ht => hsub ?_⟩
  · have hc := isCompact_univ_pi fun i : Fin n =>
      IsNonarchimedeanLocalField.isCompact_closedBall k (ε i)
    convert hc using 1
    ext ξ
    simp [Ξ, Set.mem_pi]
  · intro i hi
    by_contra hlt
    have hle : γ i ≤ valuation k (t i) := not_lt.1 hlt
    have hγi : γ i ≠ 0 := hγ i hi
    have hpos : 0 < γ i := zero_lt_iff.2 hγi
    have hti : t i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hle
      exact hγi (le_antisymm hle zero_le')
    have hmem : (Pi.single i (x₁ / t i) : Fin n → k) ∈ Ξ := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.single_eq_same, map_div₀, ε]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        gcongr
      · simp [Pi.single_eq_of_ne hj]
    have h1 := ht _ hmem
    rw [single_dotProduct, div_mul_cancel₀ _ hti] at h1
    exact hx₁ h1

end GlobalTheory.CompanionTheory.CharDual
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhdsStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_compact_within_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) → ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧ ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | exact GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.FinSumFinEquivSymmDite
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Atom

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finSumFinEquiv_symm_dite (n r : ℕ) (x : Fin (n + r)) :
    finSumFinEquiv.symm x = if h : (x : ℕ) < n then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x - n, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem unip_val_apply (n : ℕ) (v : Multiplicative (Fin n → k)) (a b : Fin (n + 1)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (if a = b then 1 else 0) + (if ha : (a : ℕ) < n then (if (b : ℕ) = n then v.toAdd ⟨a, ha⟩ else 0) else 0) := by
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  congr 1
  have hb : (b = Fin.last n) ↔ (b : ℕ) = n := by rw [Fin.ext_iff, Fin.val_last]
  induction a using Fin.lastCases with
  | last => simp [colMat]
  | cast a => simp [colMat, hb]

theorem glEmb_val_apply (n : ℕ) (g : GL (Fin n) k) (a b : Fin (n + 1)) :
    ((glEmb k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      if ha : (a : ℕ) < n then (if hb : (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, ha⟩ ⟨b, hb⟩ else 0)
      else (if a = b then 1 else 0) := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a b = _
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [glEmbMat, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem eq_unip_glEmb' {n : ℕ} (p : Mir k n) :
    (p : GL (Fin (n + 1)) k) =
      unip k n (Multiplicative.ofAdd fun r => ((p : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.last n)) *
        glEmb k n (mirabolicProjection k n p) := by
  have hh := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext1
  rw [Units.val_mul]
  show _ = (1 + colMat k n _) * glEmbMat k n (blockMat k n (p : GL (Fin (n + 1)) k))
  rw [add_mul, one_mul, colMat_mul_glEmbMat]
  ext a b
  induction a using Fin.lastCases with
  | last =>
    rw [hh]
    induction b using Fin.lastCases <;>
      simp [glEmbMat, colMat, eLast, Fin.castSucc_ne_last, Pi.single_apply]
  | cast a =>
    induction b using Fin.lastCases <;>
      simp [glEmbMat, colMat, blockMat, Fin.castSucc_ne_last]

theorem mem_colFix_iff' (N n : ℕ) (g : GL (Fin N) k) :
    g ∈ colFix k N n ↔ ∀ i j : Fin N, (j : ℕ) < n → (g : Matrix (Fin N) (Fin N) k) i j = if i = j then 1 else 0 := by
  constructor
  · intro hg i j hj
    have := congrFun (hg j hj) i
    simpa [mulVec, dotProduct, Pi.single_apply, eq_comm] using this
  · intro hg j hj
    funext i
    simp [mulVec, dotProduct, Pi.single_apply, hg i j hj]

theorem blkAt_val_apply (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    ((blkAt k n N h g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else (if i = j then 1 else 0) := by
  show (reindexAlgEquiv k k (finCongr (Nat.add_sub_cancel' h))
    (reindexAlgEquiv k k finSumFinEquiv (fromBlocks (g : Matrix (Fin n) (Fin n) k) 0 0 1))) i j = _
  rw [coe_reindexAlgEquiv, coe_reindexAlgEquiv, reindex_apply, reindex_apply, submatrix_apply, submatrix_apply]
  simp only [finCongr_symm, finCongr_apply, finSumFinEquiv_symm_dite, Fin.val_cast]
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;>
    simp [hi, hj, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply,
      Fin.ext_iff]
  all_goals (try split_ifs) <;> first | rfl | omega

theorem colEl_add (m N : ℕ) (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

theorem colEl_zero (m N : ℕ) (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp [colEl]

theorem colEl_val_apply (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i j : Fin N) :
    ((colEl k m N h x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (if i = j then 1 else 0) + (if hi : (i : ℕ) < m + 1 then (if (j : ℕ) = m + 1 then x ⟨i, hi⟩ else 0) else 0) := by
  rw [colEl, blkAt_val_apply]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;> simp only [hi, hj, dite_true, dite_false]
  · rw [unip_val_apply]
    simp only [Fin.ext_iff, toAdd_ofAdd]
  · simp [Fin.ext_iff, show ¬ (i : ℕ) = j by omega, show ¬ (j : ℕ) = m + 1 by omega]
  · simp [Fin.ext_iff]; omega
  · simp
    intro h1 h2
    omega

theorem continuous_colEl (m N : ℕ) (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  have hc : Continuous fun x => ((colEl k m N h x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    refine continuous_matrix fun i j => ?_
    simp only [colEl_val_apply]
    by_cases hi : (i : ℕ) < m + 1 <;> by_cases hj : (j : ℕ) = m + 1 <;> simp only [hi, hj, dite_true, dite_false,
      if_true, if_false] <;> fun_prop
  have hinv : ∀ x, ((colEl k m N h x)⁻¹ : GL (Fin N) k) = colEl k m N h (-x) := fun x => by
    rw [eq_comm, eq_inv_iff_mul_eq_one, ← colEl_add, neg_add_cancel, colEl_zero]
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  exact (hc.comp continuous_neg).congr fun x => by simp only [Function.comp, hinv]

theorem blkAt_glEmb (m N : ℕ) (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 2) N h (glEmb k (m + 1) g) = blkAt k (m + 1) N (by omega) g := by
  ext i j
  rw [blkAt_val_apply, blkAt_val_apply]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>
    simp only [hi, hj, dite_true, dite_false, glEmb_val_apply]
  all_goals (try split_ifs) <;> simp_all [Fin.ext_iff] <;> omega

theorem det_glEmb (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (glEmb k n g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).det = _
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have e : (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
      (g : Matrix (Fin n) (Fin n) k) := by
    ext a b
    simp [glEmbMat]
  simp only [e]
  simp [glEmbMat, ← two_mul]

theorem det_unip (n : ℕ) (x : Multiplicative (Fin n → k)) : Matrix.GeneralLinearGroup.det (unip k n x) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    rw [unip_val_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · intro a b hab
    rw [unip_val_apply]
    have hab' : (b : ℕ) < a := hab
    split_ifs <;> first | (exfalso; omega) | simp_all [Fin.ext_iff]

theorem blkAt_mul_colEl (m N : ℕ) (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N (by omega) g * colEl k m N h x =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x) * blkAt k (m + 1) N (by omega) g := by
  rw [← blkAt_glEmb m N h g, colEl, colEl, ← map_mul, ← map_mul, glEmb_mul_unip']
  rfl

theorem unip_mem_Mir (m : ℕ) (x : Fin (m + 1) → k) : unip k (m + 1) (Multiplicative.ofAdd x) ∈ Mir k (m + 1) := by
  exact MirU_le_Mir k (m + 1) ⟨_, rfl⟩

theorem glEmb_mem_Mir' (m : ℕ) (g : GL (Fin (m + 1)) k) : glEmb k (m + 1) g ∈ Mir k (m + 1) := glEmb_mem_Mir k (m + 1) g

theorem mir_decomp (m N : ℕ) (h : m + 2 ≤ N) (p : GL (Fin (m + 2)) k) (hp : p ∈ Mir k (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (g : GL (Fin (m + 1)) k),
      blkAt k (m + 2) N h p = colEl k m N h x * blkAt k (m + 1) N (by omega) g ∧
      Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det g := by
  have e : p = _ := eq_unip_glEmb' (⟨p, hp⟩ : Mir k (m + 1))
  refine ⟨fun r => (p : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (Fin.castSucc r) (Fin.last (m + 1)),
    mirabolicProjection k (m + 1) ⟨p, hp⟩, ?_, ?_⟩
  · conv_lhs => rw [e]
    rw [map_mul, ← blkAt_glEmb m N h]
    rfl
  · calc Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det (unip k (m + 1) _ * glEmb k (m + 1) _) :=
          congrArg _ e
      _ = _ := by rw [map_mul, det_unip, one_mul, det_glEmb]

theorem derUnip_decomp (ψ : AddChar k Circle) (m N : ℕ) (h : m + 2 ≤ N) (u : GL (Fin N) k)
    (hu : u ∈ derUnip k N (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (u' : GL (Fin N) k) (hu' : u' ∈ derUnip k N (m + 2)),
      u = colEl k m N h x * u' ∧
      ((derChar k ψ N (m + 1) ⟨u, hu⟩ : ℂˣ) : ℂ) = ((lvlChar k ψ N (m + 2) ⟨u', hu'⟩ : ℂˣ) : ℂ) := by
  have hu1 := (mem_unipB k).1 (Subgroup.mem_inf.1 hu).1
  have hcf := (mem_colFix_iff' N (m + 1) u).1 (Subgroup.mem_inf.1 hu).2
  have hlow : ∀ i j : Fin N, (j : ℕ) < i → (u : Matrix (Fin N) (Fin N) k) i j = 0 := fun i j hij => hu1.1 i j hij
  have hdiag := hu1.2
  set r : Fin N := ⟨m + 1, by omega⟩ with hr
  set x : Fin (m + 1) → k := fun i => (u : Matrix (Fin N) (Fin N) k) ⟨i, by omega⟩ r with hx
  set u' : GL (Fin N) k := colEl k m N h (-x) * u with hu'def
  have hent : ∀ i j, (u' : Matrix (Fin N) (Fin N) k) i j = (u : Matrix (Fin N) (Fin N) k) i j -
      (if hi : (i : ℕ) < m + 1 then x ⟨i, hi⟩ * (u : Matrix (Fin N) (Fin N) k) r j else 0) := by
    intro i j
    rw [hu'def, Units.val_mul, Matrix.mul_apply]
    simp only [colEl_val_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases hi : (i : ℕ) < m + 1
    · simp only [hi, dite_true, ite_mul, zero_mul]
      rw [Finset.sum_eq_single r (fun b _ hb => if_neg (fun e => hb (Fin.ext e))) (by simp)]
      simp [hr, sub_eq_add_neg]
    · simp [hi]
  have hu' : u' ∈ derUnip k N (m + 2) := by
    refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩, (mem_colFix_iff' N (m + 2) u').2 fun i j hj => ?_⟩
    · have hij' : (j : ℕ) < i := hij
      rw [hent, hlow i j hij']
      split_ifs with hi
      · rw [hlow r j (by simp [hr]; omega)]; simp
      · simp
    · rw [hent, hdiag]
      split_ifs with hi
      · rw [hlow r i (by simp [hr]; omega)]; simp
      · simp
    · rw [hent]
      by_cases hj' : (j : ℕ) < m + 1
      · rw [hcf i j hj', hcf r j hj']
        simp [hr, Fin.ext_iff]
        intro _ e
        omega
      · have hjr : j = r := Fin.ext (by simp [hr]; omega)
        rw [hjr, hdiag r]
        by_cases hi : (i : ℕ) < m + 1
        · simp [hi, hx, hr, Fin.ext_iff, show (i : ℕ) ≠ m + 1 by omega]
        · by_cases hir : i = r
          · rw [hir, hdiag r]; simp [hr]
          · have : (r : ℕ) < i := by
              have := Fin.val_ne_of_ne hir
              simp [hr] at this ⊢; omega
            rw [hlow i r this]; simp [hi, hir]
  refine ⟨x, u', hu', ?_, ?_⟩
  · rw [hu'def, ← mul_assoc, ← colEl_add, add_neg_cancel, colEl_zero, one_mul]
  · have hs : (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), (u : Matrix (Fin N) (Fin N) k) p.1 p.2) =
        ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ), (u' : Matrix (Fin N) (Fin N) k) p.1 p.2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_filter.1 hp).2
      rw [hent, dite_eq_right (by omega), sub_zero]
    exact congrArg (fun t => ((Circle.toUnits (ψ t) : ℂˣ) : ℂ)) hs

end PositivityTheory.RgUd.Form.U.Atom
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.ChartRestriction
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.Form.U.Atom

section Transversal

variable {X : Type} [AddCommGroup X]

theorem sum_transversal_add {M : Type} [AddCommMonoid M] {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t :=
  GlobalTheory.T.coset_sum_translate_invariant hHA hT hTr F hF ha

theorem card_smul_sum_eq {M : Type} [AddCommGroup M] [Module ℂ M] {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A)
    {T T' : Finset X} (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hT' : ∀ t ∈ T', t ∈ A) (hTr' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H') (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∀ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, F t := fun s hs =>
    sum_transversal_add hH hT hTr F hF (hT' s hs)
  have h2 : ∀ t ∈ T, ∑ s ∈ T', F (s + t) = ∑ s ∈ T', F s := fun t ht =>
    sum_transversal_add hH' hT' hTr' F hF' (hT t ht)
  have e1 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
  have e2 : ∑ t ∈ T, ∑ s ∈ T', F (s + t) = T.card • ∑ s ∈ T', F s := by
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
  have e3 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, ∑ s ∈ T', F (s + t) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← e1, ← e2, e3]

theorem sum_transversal_char {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (χ : X → ℂ)
    (hχ : ∀ a b, χ (a + b) = χ a * χ b) (hH : ∀ h ∈ H, χ h = 1) {a : X} (ha : a ∈ A) (hne : χ a ≠ 1) :
    ∑ t ∈ T, χ t = 0 := by
  have key := sum_transversal_add hHA hT hTr χ (fun b h hh => by rw [hχ, hH h hh, mul_one]) ha
  simp only [hχ] at key
  rw [← Finset.sum_mul] at key
  have h0 : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

theorem transversal_nonempty {A H : AddSubgroup X} {T : Finset X} (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    T.Nonempty := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hTr 0 A.zero_mem
  exact ⟨t, ht⟩

variable [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem exists_transversal (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  GlobalTheory.T.exists_finite_coset_representatives A H hA hH hHA

theorem isCompact_sup (A B : AddSubgroup X) (hA : IsCompact (A : Set X)) (hB : IsCompact (B : Set X)) :
    IsCompact ((A ⊔ B : AddSubgroup X) : Set X) :=
  GlobalTheory.T.isCompact_sup_addSubgroup A B hA hB

theorem relIndex_ne_zero' (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    H.relIndex A ≠ 0 :=
  GlobalTheory.T.relIndex_open_compact_ne_zero A H hA hH hHA

end Transversal

section Forms

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem apply_eq_zero_of_isotropic (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hB' : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 :=
  GlobalTheory.T.hermitian_semidefinite_null_radical B hB hB' x hx w

theorem eq_zero_of_diag (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v, B v v = 0) : B = 0 :=
  GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero B hB

end Forms

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ker_char (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} :=
  GlobalTheory.T.isOpen_additive_character_kernel ψ hψ

theorem exists_lat_mem (n : ℕ) (x : Fin n → k) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ x ∈ A :=
  GlobalTheory.T.exists_compact_open_subgroup_mem n x

theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) : IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} :=
  GlobalTheory.T.isOpen_character_annihilator ψ hψ n A hA

theorem exists_small_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (n : ℕ) (S : Set (Fin n → k))
    (hS : S ∈ nhds (0 : Fin n → k)) : ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S :=
  GlobalTheory.T.annihilator_compact_within_nhds ψ hψ hψ1 n S hS

theorem comap_lat (n : ℕ) (g : Matrix (Fin n) (Fin n) k) (hg : IsUnit g) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) (hA' : IsOpen (A : Set (Fin n → k))) :
    IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧
      IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) :=
  GlobalTheory.T.isCompact_isOpen_comap_mulVecLin n g hg A hA hA'

end Local

theorem exists_GL_vecMul {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 :=
  GlobalTheory.T.exists_GL_vecMul_eq_last_basis n ξ hξ

end PositivityTheory.RgUd.Form.U.Atom
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Atom

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Subs

variable {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)

def stabSub (v : V) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | π (colEl k m N h x) v = v}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [colEl_add, map_mul, Module.End.mul_apply, hb, ha]
  zero_mem' := by simp [colEl_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, neg_add_cancel, colEl_zero, map_one, Module.End.one_apply]


variable (k) in
def charSub {n : ℕ} (ψ : AddChar k Circle) (ξ : Fin n → k) : AddSubgroup (Fin n → k) where
  carrier := {x | ψ (ξ ⬝ᵥ x) = 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_add, AddChar.map_add_eq_mul, ha, hb, one_mul]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_neg, AddChar.map_neg_eq_inv, ha, inv_one]


variable (k) in
def annSub {n : ℕ} (ψ : AddChar k Circle) (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  add_mem' {a b} ha hb := by
    intro x hx
    rw [add_dotProduct, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
  zero_mem' := by intro x _; simp
  neg_mem' {a} ha := by
    intro x hx
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, ha x hx, inv_one]

end Subs

section Api

variable {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
  (ψ : AddChar k Circle)

theorem inv_smul_eq_of_smul_eq_alt {M : Type} [AddCommGroup M] [Module ℂ M] {a b : ℂ} {x y : M} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk : b • x = a • y) : a⁻¹ • x = b⁻¹ • y := by
  rw [← inv_smul_smul₀ hb x, hk, smul_smul, smul_smul]
  congr 1
  field_simp

theorem transversal_neg {X : Type} [AddCommGroup X] [DecidableEq X] {A H : AddSubgroup X} {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    (∀ t ∈ T.image Neg.neg, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T.image Neg.neg ∧ a - t ∈ H := by
  refine ⟨fun t ht => ?_, fun a ha => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact A.neg_mem (hT s hs)
  · obtain ⟨s, ⟨hs, hs'⟩, hu⟩ := hTr (-a) (A.neg_mem ha)
    refine ⟨-s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
    · have := H.neg_mem hs'
      rwa [show -(-a - s) = a - -s by abel] at this
    · rintro t ⟨ht, ht'⟩
      obtain ⟨s', hs'', rfl⟩ := Finset.mem_image.mp ht
      have := hu s' ⟨hs'', by
        have := H.neg_mem ht'
        rwa [show -(a - -s') = -a - s' by abel] at this⟩
      rw [this]

theorem conj_psi (y : k) : starRingEnd ℂ ((ψ y : Circle) : ℂ) = ((ψ (-y) : Circle) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem avgF_add {ξ : Fin (m + 1) → k} {v : V} (a b : Fin (m + 1) → k) (hb : π (colEl k m N h b) v = v)
    (hb' : ψ (ξ ⬝ᵥ b) = 1) :
    (starRingEnd ℂ ((ψ (ξ ⬝ᵥ (a + b)) : Circle) : ℂ)) • π (colEl k m N h (a + b)) v =
      (starRingEnd ℂ ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ)) • π (colEl k m N h a) v := by
  rw [dotProduct_add, AddChar.map_add_eq_mul, hb', mul_one, colEl_add, map_mul, Module.End.mul_apply, hb]

theorem isOpen_stabSub (hπ : IsSmooth π) (v : V) : IsOpen (stabSub h π v : Set (Fin (m + 1) → k)) := by
  exact (hπ v).preimage (continuous_colEl m N h)

theorem isOpen_charSub (hψ : Continuous ψ) {n : ℕ} (ξ : Fin n → k) : IsOpen (charSub k ψ ξ : Set (Fin n → k)) := by
  have hc : Continuous fun x : Fin n → k => ξ ⬝ᵥ x := continuous_const.dotProduct continuous_id
  exact (isOpen_ker_char ψ hψ).preimage hc

theorem isLat_comap {n : ℕ} (g : GL (Fin (n + 1)) k) {A : AddSubgroup (Fin (n + 1) → k)} (hA : IsLat A) :
    IsLat (A.comap (Matrix.mulVecLin (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).toAddMonoidHom) := by
  exact comap_lat (n + 1) _ (Units.isUnit g) A hA.1 hA.2

theorem avg_eq {ξ : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p) :
    avg ψ h π ξ A v = ((p.2.card : ℂ)⁻¹) •
      ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v := by
  have hd : ∃ p, AvgData ψ h π ξ A v p := ⟨p, hp⟩
  rw [avg, dite_eq_left hd]
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hd.choose_spec
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  have key := card_smul_sum_eq hq1 hp1 hq5 hq6 hp5 hp6
    (fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v)
    (fun a b hb => avgF_add h π ψ a b (hq3 b hb) (hq4 b hb)) (fun a b hb => avgF_add h π ψ a b (hp3 b hb) (hp4 b hb))
  have hcq : (hd.choose.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hq6).card_pos.ne'
  have hcp : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hp6).card_pos.ne'
  exact inv_smul_eq_of_smul_eq_alt hcq hcp key

theorem exists_avgData_of (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V)
    (U : AddSubgroup (Fin (m + 1) → k)) (hU : IsOpen (U : Set (Fin (m + 1) → k))) (hUA : U ≤ A)
    (hUv : U ≤ stabSub h π v) (hUξ : U ≤ charSub k ψ ξ) : ∃ T, AvgData ψ h π ξ A v (U, T) := by
  obtain ⟨T, hT, hTr⟩ := exists_transversal A U hA.1 hU hUA
  exact ⟨T, hUA, hU, fun a ha => hUv ha, fun a ha => hUξ ha, hT, hTr⟩

theorem exists_avgData (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (v : V) (U : AddSubgroup (Fin (m + 1) → k)) (hU : IsOpen (U : Set (Fin (m + 1) → k))) :
    ∃ p, AvgData ψ h π ξ A v p ∧ p.1 ≤ U := by
  obtain ⟨T, hT⟩ := exists_avgData_of h π ψ ξ hA v (U ⊓ A ⊓ stabSub h π v ⊓ charSub k ψ ξ)
    (by
      simp only [AddSubgroup.coe_inf]
      exact ((hU.inter hA.2).inter (isOpen_stabSub h π hπ v)).inter (isOpen_charSub ψ hψ ξ))
    (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right) inf_le_right
  exact ⟨_, hT, inf_le_left.trans (inf_le_left.trans inf_le_left)⟩

theorem avgData_of_fix {ξ : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v w : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p)
    (hw : ∀ a ∈ p.1, π (colEl k m N h a) w = w) : AvgData ψ h π ξ A w p :=
  ⟨hp.1, hp.2.1, hw, hp.2.2.2⟩

theorem exists_avgData₂ (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) :
    ∃ p, AvgData ψ h π ξ A v p ∧ AvgData ψ h π ξ A w p := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (stabSub h π w) (isOpen_stabSub h π hπ w)
  exact ⟨p, hp, avgData_of_fix h π ψ hp (fun a ha => hpU ha)⟩

theorem avg_add (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (v w : V) : avg ψ h π ξ A (v + w) = avg ψ h π ξ A v + avg ψ h π ξ A w := by
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v w
  have hpvw : AvgData ψ h π ξ A (v + w) p :=
    avgData_of_fix h π ψ hp (fun a ha => by rw [map_add (f := _), hp.2.2.1 a ha, hpw.2.2.1 a ha])
  rw [avg_eq h π ψ hpvw, avg_eq h π ψ hp, avg_eq h π ψ hpw, ← smul_add, ← Finset.sum_add_distrib]
  simp only [map_add (f := _), smul_add]

theorem avg_smul (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (c : ℂ) (v : V) : avg ψ h π ξ A (c • v) = c • avg ψ h π ξ A v := by
  obtain ⟨p, hp, -⟩ := exists_avgData h π ψ hψ hπ ξ hA v (stabSub h π v) (isOpen_stabSub h π hπ v)
  have hpc : AvgData ψ h π ξ A (c • v) p :=
    avgData_of_fix h π ψ hp (fun a ha => by rw [map_smul, hp.2.2.1 a ha])
  rw [avg_eq h π ψ hpc, avg_eq h π ψ hp, smul_comm c]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, smul_comm]

theorem colEl_comm_avg' (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (a : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h a) (avg ψ h π ξ A v) = avg ψ h π ξ A (π (colEl k m N h a) v) := by
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v (π (colEl k m N h a) v)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_eq h π ψ hp, avg_eq h π ψ hpw, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : π (colEl k m N h a) (π (colEl k m N h t) v) = π (colEl k m N h t) (π (colEl k m N h a) v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, add_comm, colEl_add, map_mul, Module.End.mul_apply]
  rw [map_smul, e]

theorem avg_colEl (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) {a : Fin (m + 1) → k} (ha : a ∈ A) (v : V) :
    avg ψ h π ξ A (π (colEl k m N h a) v) = ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) • avg ψ h π ξ A v := by
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v (π (colEl k m N h a) v)
  have hs := sum_transversal_add hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    (fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v)
    (fun x y hy => avgF_add h π ψ x y (hp.2.2.1 y hy) (hp.2.2.2.1 y hy)) ha
  have e : ∀ t, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) (π (colEl k m N h a) v) =
      ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) •
        ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ (t + a)) : Circle) : ℂ)) • π (colEl k m N h (t + a)) v) := by
    intro t
    rw [colEl_add, map_mul, Module.End.mul_apply, smul_smul]
    congr 1
    rw [conj_psi, conj_psi, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, dotProduct_add]
    congr 2
    ring
  rw [avg_eq h π ψ hpw, avg_eq h π ψ hp, Finset.sum_congr rfl (fun t _ => e t), ← Finset.smul_sum, hs, smul_comm]

open Classical in
theorem char_sum {ξ η : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p)
    (hη : ∀ a ∈ p.1, ψ (η ⬝ᵥ a) = 1) :
    ((p.2.card : ℂ)⁻¹) * ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ) =
      if ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (η ⬝ᵥ a) then 1 else 0 := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  have e : ∀ t, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ) =
      ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ) := by
    intro t
    rw [conj_psi, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, sub_dotProduct]
    congr 2
    ring
  simp only [e]
  have hc : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hp6).card_pos.ne'
  split_ifs with hA
  · have h1 : ∀ t ∈ p.2, ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ) = 1 := by
      intro t ht
      rw [sub_dotProduct, AddChar.map_sub_eq_div, hA t (hp5 t ht), div_self', Circle.coe_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc]
  · push Not at hA
    obtain ⟨a, ha, hne⟩ := hA
    have hz : ∑ t ∈ p.2, ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ) = 0 := by
      refine sum_transversal_char hp1 hp5 hp6 (fun t => ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ)) ?_ ?_ ha ?_
      · intro x y
        rw [dotProduct_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      · intro x hx
        rw [sub_dotProduct, AddChar.map_sub_eq_div, hη x hx, hp4 x hx, div_one, Circle.coe_one]
      · intro H
        apply hne
        have H2 : ψ ((η - ξ) ⬝ᵥ a) = 1 := by
          rw [← Circle.coe_inj, Circle.coe_one]
          exact H
        rw [sub_dotProduct, AddChar.map_sub_eq_div] at H2
        exact (div_eq_one.mp H2).symm
    rw [hz, mul_zero]


theorem avg_zero' (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) : avg ψ h π ξ A 0 = 0 := by
  have := avg_smul h π ψ hψ hπ ξ hA 0 0
  simpa using this

theorem avg_sum' (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) {ι : Type} (s : Finset ι) (f : ι → V) :
    avg ψ h π ξ A (∑ i ∈ s, f i) = ∑ i ∈ s, avg ψ h π ξ A (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, avg_zero' h π ψ hψ hπ ξ hA]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, avg_add h π ψ hψ hπ ξ hA, ih]


open Classical in
theorem avg_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ η : Fin (m + 1) → k) {A A' : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (hA' : IsLat A') (hAA' : A ≤ A') (v : V) :
    avg ψ h π η A' (avg ψ h π ξ A v) = if ∀ a ∈ A, ψ (η ⬝ᵥ a) = ψ (ξ ⬝ᵥ a) then avg ψ h π η A' v else 0 := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (charSub k ψ η) (isOpen_charSub ψ hψ η)
  have hs := char_sum h π ψ hp (fun a ha => hpU ha)
  rw [avg_eq h π ψ hp, avg_smul h π ψ hψ hπ η hA', avg_sum' h π ψ hψ hπ η hA']
  have e : ∀ t ∈ p.2, avg ψ h π η A' ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v) =
      ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ)) • avg ψ h π η A' v := by
    intro t ht
    rw [avg_smul h π ψ hψ hπ η hA', avg_colEl h π ψ hψ hπ η hA' (hAA' (hp.2.2.2.2.1 t ht)), smul_smul]
  rw [Finset.sum_congr rfl e, ← Finset.sum_smul, smul_smul, hs]
  by_cases hc : ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (η ⬝ᵥ a)
  · rw [if_pos hc, if_pos (fun a ha => (hc a ha).symm), one_smul]
  · rw [if_neg hc, if_neg (fun H => hc (fun a ha => (H a ha).symm)), zero_smul]

theorem form_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x v w, B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) :
    B (avg ψ h π ξ A v) w = B v (avg ψ h π ξ A w) := by
  classical
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v w
  rw [avg_eq h π ψ hp, avg_eq h π ψ hpw]
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  obtain ⟨hT', hTr'⟩ := transversal_neg hp5 hp6
  have hF : ∀ a, ∀ b ∈ p.1, ((ψ (ξ ⬝ᵥ (a + b)) : Circle) : ℂ) * B v (π (colEl k m N h (a + b)) w) =
      ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) * B v (π (colEl k m N h a) w) := by
    intro a b hb
    rw [dotProduct_add, AddChar.map_add_eq_mul, hp4 b hb, mul_one, colEl_add, map_mul, Module.End.mul_apply,
      hpw.2.2.1 b hb]
  have key := card_smul_sum_eq hp1 hp1 hp5 hp6 hT' hTr'
    (fun s => ((ψ (ξ ⬝ᵥ s) : Circle) : ℂ) * B v (π (colEl k m N h s) w)) hF hF
  rw [Finset.card_image_of_injective _ neg_injective, Finset.sum_image (fun x _ y _ hxy => neg_injective hxy)] at key
  have hc : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hp6).card_pos.ne'
  have key' := smul_right_injective ℂ hc key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_smulₛₗ, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    smul_eq_mul, map_inv₀, map_natCast, starRingEnd_self_apply]
  congr 1
  refine (Finset.sum_congr rfl fun t _ => ?_).trans key'.symm
  show _ = ((ψ (ξ ⬝ᵥ (-t)) : Circle) : ℂ) * B v (π (colEl k m N h (-t)) w)
  have hv : π (colEl k m N h (-t)) (π (colEl k m N h t) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, neg_add_cancel, colEl_zero, map_one, Module.End.one_apply]
  rw [conj_psi, dotProduct_neg, ← hB (-t) (π (colEl k m N h t) v) w, hv]

theorem avg_conj (hψ : Continuous ψ) (hπ : IsSmooth π) (g : GL (Fin (m + 1)) k) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (u : V) :
    avg ψ h π ξ (A.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom)
        (π (blkAt k (m + 1) N (by omega) g) u) =
      π (blkAt k (m + 1) N (by omega) g) (avg ψ h π (Matrix.vecMul ξ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) A u) := by
  classical
  obtain ⟨p, hp, -⟩ := exists_avgData h π ψ hψ hπ (Matrix.vecMul ξ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) hA u
    (stabSub h π u) (isOpen_stabSub h π hπ u)
  have hp0 := hp
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp0
  have hgg : ∀ x : Fin (m + 1) → k, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
      (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hgg' : ∀ x : Fin (m + 1) → k, ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinj : Function.Injective (fun x : Fin (m + 1) → k => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) := by
    intro x y hxy
    have := congrArg (fun z => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ z) hxy
    simpa only [hgg'] using this
  have hcomm : ∀ (y : Fin (m + 1) → k) (w : V),
      π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ y)) (π (blkAt k (m + 1) N (by omega) g) w) =
        π (blkAt k (m + 1) N (by omega) g) (π (colEl k m N h y) w) := by
    intro y w
    rw [← Module.End.mul_apply, ← map_mul, ← blkAt_mul_colEl, map_mul, Module.End.mul_apply]
  have hq : AvgData ψ h π ξ
      (A.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom)
      (π (blkAt k (m + 1) N (by omega) g) u)
      (p.1.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom,
        p.2.image (fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact hp1 hx
    · rw [AddSubgroup.coe_comap]
      exact hp2.preimage (Continuous.matrix_mulVec continuous_const continuous_id)
    · intro x hx
      have := hcomm (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) u
      rw [hgg] at this
      rw [this, hp3 (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) hx]
    · intro x hx
      have := hp4 (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) hx
      rwa [← Matrix.dotProduct_mulVec, hgg] at this
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      change ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
        ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s) ∈ A
      rw [hgg']
      exact hp5 s hs
    · intro a ha
      obtain ⟨s, ⟨hs, hs'⟩, hu⟩ := hp6 _ ha
      refine ⟨(g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
      · change ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
          (a - (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s) ∈ p.1
        rw [Matrix.mulVec_sub, hgg']
        exact hs'
      · rintro t ⟨ht, ht'⟩
        obtain ⟨s', hs'', rfl⟩ := Finset.mem_image.mp ht
        change ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
          (a - (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s') ∈ p.1 at ht'
        rw [Matrix.mulVec_sub, hgg'] at ht'
        rw [hu s' ⟨hs'', ht'⟩]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_eq h π ψ hq, avg_eq h π ψ hp, Finset.card_image_of_injective _ hinj,
    Finset.sum_image (fun x _ y _ hxy => hinj hxy), map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, hcomm, Matrix.dotProduct_mulVec]

theorem continuous_one_char : Continuous (⇑(1 : AddChar k Circle)) := by
  have : ⇑(1 : AddChar k Circle) = fun _ => 1 := funext fun x => AddChar.one_apply x
  rw [this]
  exact continuous_const

theorem avg_zero_char (ξ0 : Fin (m + 1) → k) (hξ0 : ξ0 = 0) (A : AddSubgroup (Fin (m + 1) → k)) (v : V) :
    avg ψ h π ξ0 A v = avg (1 : AddChar k Circle) h π 0 A v := by
  subst hξ0
  have hiff : ∀ p, AvgData ψ h π 0 A v p ↔ AvgData 1 h π 0 A v p := by
    intro p
    constructor
    · rintro ⟨a, b, c, -, e, f⟩
      exact ⟨a, b, c, fun x _ => by simp, e, f⟩
    · rintro ⟨a, b, c, -, e, f⟩
      exact ⟨a, b, c, fun x _ => by simp, e, f⟩
  by_cases hd : ∃ p, AvgData ψ h π 0 A v p
  · obtain ⟨p, hp⟩ := hd
    rw [avg_eq h π ψ hp, avg_eq h π 1 ((hiff p).mp hp)]
    simp only [zero_dotProduct, AddChar.map_zero_eq_one]
  · have hd' : ¬ ∃ p, AvgData 1 h π 0 A v p := fun ⟨p, hp⟩ => hd ⟨p, (hiff p).mpr hp⟩
    rw [avg, avg, dite_eq_right hd, dite_eq_right hd']

theorem avg_congr_char (hψ : Continuous ψ) (hπ : IsSmooth π) {ξ ξ' : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (hξ : ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (ξ' ⬝ᵥ a)) (v : V) :
    avg ψ h π ξ A v = avg ψ h π ξ' A v := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (charSub k ψ ξ') (isOpen_charSub ψ hψ ξ')
  have hp' : AvgData ψ h π ξ' A v p := ⟨hp.1, hp.2.1, hp.2.2.1, fun a ha => hpU ha, hp.2.2.2.2⟩
  rw [avg_eq h π ψ hp, avg_eq h π ψ hp']
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hξ t (hp.2.2.2.2.1 t ht)]

theorem colEl_comm_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (a : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h a) (avg ψ h π ξ A v) = avg ψ h π ξ A (π (colEl k m N h a) v) :=
  colEl_comm_avg' h π ψ hψ hπ ξ hA a v

end Api

end PositivityTheory.RgUd.Form.U.Atom

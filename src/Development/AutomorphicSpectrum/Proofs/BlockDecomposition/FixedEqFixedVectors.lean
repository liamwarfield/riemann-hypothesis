module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.AdmDict

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  constructor
  · intro hv h hh
    simpa using hv ⟨h, hh⟩
  · intro hv h
    simpa using hv h h.2

theorem isAdmissible_iff : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ
  have hs : GlobalTheory.PRep.IsSmooth ρ ↔ GroundTheory.Automorphic.IsSmooth ρ := Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hs.1 h1, fun K hc ho => ?_⟩
    have := h2 K ho hc
    rwa [fixed_eq_fixedVectors] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hs.2 h1, fun K ho hc => ?_⟩
    rw [fixed_eq_fixedVectors]
    exact h2 K hc ho

end GlobalTheory.CompanionTheory.AdmDict
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaInv

theorem thetaW_val_apply {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) (i j : Fin N) :
    (thetaW A N g).1 i j = (g⁻¹).1 (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix,
    Matrix.transpose_apply, Fin.revPerm]

theorem thetaW_thetaW_ring {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N (thetaW A N g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaW_val_apply, ← map_inv, thetaW_val_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem thetaW_thetaW {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k) :
    thetaW k N (thetaW k N g) = g :=
  thetaW_thetaW_ring N g

end GlobalTheory.CompanionTheory.ThetaInv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApplyStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_inverse_involution_apply : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k), thetaW k N (thetaW k N g) = g := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | exact GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BlockIndex

theorem sum_castLE_eq_range {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    ∑ b : Fin a, d (Fin.castLE a.2.le b) =
      ∑ c ∈ Finset.range a, (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) c := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dite_eq_left (b.2.trans a.2)] <;> rfl

theorem partial_sum_succ_le {h : ℕ} (d : Fin h → ℕ) {a b : Fin h} (hab : b < a) :
    ∑ c : Fin b, d (Fin.castLE b.2.le c) + d b ≤ ∑ c : Fin a, d (Fin.castLE a.2.le c) := by
  have hsub : Finset.range ((b : ℕ) + 1) ⊆ Finset.range a := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (show (b : ℕ) + 1 ≤ a from hab))
  have key := Finset.sum_le_sum_of_subset (f := fun c => if hc : c < h then d ⟨c, hc⟩ else 0) hsub
  rw [Finset.sum_range_succ, dite_eq_left b.2] at key
  rw [GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d b, GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d a]
  exact key

theorem stdBlocks_lt_of_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (hab : b < a)
    (x : Fin (d a)) (y : Fin (d b)) : stdBlocks d hd ⟨b, y⟩ < stdBlocks d hd ⟨a, x⟩ := by
  rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val,
    GlobalTheory.SmGL.stdBlocks_val]
  have h1 := GlobalTheory.CompanionTheory.BlockIndex.partial_sum_succ_le d hab
  have h2 := y.2
  omega

theorem blockIdx_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  intro h N d hd i j hij
  by_contra H
  rw [not_le] at H
  have H' : ((GlobalTheory.SmGL.stdBlocks d hd).symm j).1 <
      ((GlobalTheory.SmGL.stdBlocks d hd).symm i).1 := H
  have key := GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd H'
    ((GlobalTheory.SmGL.stdBlocks d hd).symm i).2
    ((GlobalTheory.SmGL.stdBlocks d hd).symm j).2
  simp only [Sigma.eta, Equiv.apply_symm_apply] at key
  exact absurd hij (not_le.mpr key)

end GlobalTheory.CompanionTheory.BlockIndex
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotoneStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_index_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | exact GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | (intros; apply GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommute
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommute
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.CapComm

open Formalism.REAL

theorem commute_qdet_of {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A} {x : A}
    (h : ∀ a b, Commute x (X a b)) (u : ℂ) : Commute x (qdet X u) := by
  have hm : ∀ a b, X a b ∈ Subalgebra.centralizer ℂ ({x} : Set A) := fun a b =>
    (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact (h a b).eq
  have hq : qdet X u ∈ Subalgebra.centralizer ℂ ({x} : Set A) := by
    unfold qdet qminor
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    unfold Tm
    refine Subalgebra.add_mem _ ?_ (hm _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 hq x rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A}
    (hX : GlRel X) (u v : ℂ) : Commute (qdet X u) (qdet X v) :=
  commute_qdet_of (fun a b => qDetCentral A k X hX u a b) v

theorem capR_capS_commute (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ)
    (u v : ℂ) :
    Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧
      Commute (capS r s τ u) (capS r s τ v) := by
  have hE := glRel_Eop (E := E) (a := r + s) τ
  refine ⟨?_, ?_, ?_⟩
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.castAdd_injective _ _)) _ _
  · exact (GlobalTheory.CapHC.qdet_comm hE _ _).symm
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.natAdd_injective _ _)) _ _

end GlobalTheory.CompanionTheory.CTFin.CapComm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommuteStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operators_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ), Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧ Commute (capS r s τ u) (capS r s τ v) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute | exact GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMatMir
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

def rowQ (n : ℕ) (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  fun j => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) (Fin.castSucc j)

def unipM (n : ℕ) : Multiplicative (Fin (n + 1) → k) →* Mir k (n + 1) :=
  (unip k (n + 1)).codRestrict (Mir k (n + 1)) (fun v => MirU_le_Mir k (n + 1) ⟨v, rfl⟩)

theorem unipM_val (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) :
    ((unipM k n v : Mir k (n + 1)) : GL (Fin (n + 2)) k) = unip k (n + 1) v := rfl

theorem unipM_mem_MirUin (n : ℕ) (v : Multiplicative (Fin (n + 1) → k)) : unipM k n v ∈ MirUin k (n + 1) := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

variable (k : Type) [Field k]

theorem rowQ_one (n : ℕ) : rowQ k n 1 = Pi.single (Fin.last n) 1 := by
  funext j
  by_cases h : j = Fin.last n
  · subst h
    simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ]
  · simp [GlobalTheory.CompanionTheory.BZPhiPhi.rowQ, Matrix.one_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.CompanionTheory.BZPhiPhi

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_matMir (n : ℕ) :
    Continuous fun g : Mir k (n + 1) => ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_rowQ (n : ℕ) : Continuous (rowQ k n) :=
  continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp (continuous_matMir n))

theorem continuous_unipM (n : ℕ) :
    Continuous fun v : Fin (n + 1) → k => unipM k n (Multiplicative.ofAdd v) := by
  have hcol : Continuous fun v : Fin (n + 1) → k => GlobalTheory.BZMir.colMat k (n + 1) v := by
    refine continuous_matrix fun i j => ?_
    unfold GlobalTheory.BZMir.colMat
    by_cases hj : j = Fin.last (n + 1)
    · simp only [if_pos hj]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simp only [Fin.lastCases_castSucc]
        exact continuous_apply i
      · simp only [Fin.lastCases_last]
        exact continuous_const
    · simp only [if_neg hj]
      exact continuous_const
  have hval : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) + GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.add hcol
  have hinv : Continuous fun v : Fin (n + 1) → k =>
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) - GlobalTheory.BZMir.colMat k (n + 1) v :=
    continuous_const.sub hcol
  have hGL : Continuous fun v : Fin (n + 1) → k =>
      GlobalTheory.BZMir.unip k (n + 1) (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelConjugation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAEqOfUnip
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k]

theorem thetaA_eq_of_unip (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : MirUin k n)
    (w : Multiplicative (Fin n → k))
    (hx : ((x : Mir k n) : GL (Fin (n + 1)) k) = unip k n w) :
    thetaA k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ w.toAdd)) := by
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hx
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x)).toAdd)) = _
  rw [key]

theorem thetaConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : ThetaConj k := by
  intro ψ n a m u
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  have e : glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ =
      unip k n (Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) := by
    rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  have h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n := by
    show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n
    rw [e]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  rw [thetaA_eq_of_unip ψ _ u v hv', thetaA_eq_of_unip ψ a ⟨_, h⟩ _ e]
  simp only [toAdd_ofAdd]
  rw [dotProduct_mulVec]

end GlobalTheory.CompanionTheory.BZMirabolic

end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem twKer_le_comap_levi (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) (m : GL (Fin n) k) :
    twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ≤
      (twKer τ (MirUin k n) (thetaA k ψ a)).comap (τ (levi k n m)) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  intro x hx
  have key : ∀ (u : GlobalTheory.BZMir.MirUin k n) (w : V),
      τ (GlobalTheory.BZMir.levi k n m) (τ u w) =
        τ (GlobalTheory.BZMir.levi k n m * u * (GlobalTheory.BZMir.levi k n m)⁻¹) (τ (GlobalTheory.BZMir.levi k n m) w) := by
    intro u w
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  first
    | (obtain ⟨u, w, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨⟨_, hm⟩, _, rfl⟩)
    | (obtain ⟨⟨u, w⟩, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨(⟨_, hm⟩, _), rfl⟩)

theorem twKerConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TwKerConj k := by
  unfold GlobalTheory.BZMir.Fun.TwKerConj
  intro ψ n V _ _ τ a m v
  constructor
  · intro hv
    exact GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ a m hv
  · intro hv
    have ha : vecMul (vecMul a (m : Matrix (Fin n) (Fin n) k))
        ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = a := by
      rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    rw [← ha] at hv
    have h := GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ _ m⁻¹ hv
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
      map_one, map_one, Module.End.one_apply] at h
    exact h

end GlobalTheory.CompanionTheory.BZMirabolic

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTop
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTop
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

section Groups

variable {k : Type} [Field k]

theorem blk_stdBlocks_two {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (i : Fin N) :
    blk (stdBlocks ![n, N - n] h) i = if (i : ℕ) < n then 0 else 1 := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks ![n, N - n] h).surjective i
  rw [blk_apply]
  have := stdBlocks_val ![n, N - n] h c i'
  fin_cases c
  · have hi := i'.2
    simp at this hi ⊢
    omega
  · have hi := i'.2
    simp at this hi ⊢
    omega

theorem mem_unipRad_two_iff {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks ![n, N - n] h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_stdBlocks_two, blk_stdBlocks_two]
  have : ((if (i : ℕ) < n then (0 : Fin 2) else 1) < if (j : ℕ) < n then 0 else 1) ↔
      ((i : ℕ) < n ∧ n ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;> simp [hi, hj] <;> omega
  rw [this]

theorem unipRad_two_le_derUnip {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) :
    unipRad k (stdBlocks ![n, N - n] h) ≤ derUnip k N n := by
  intro g hg
  have hE := (mem_unipRad_two_iff h).1 hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · intro i hi
    ext r
    have hc : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hc, hE r i (by omega)]
    by_cases hri : r = i
    · subst hri; simp
    · rw [one_apply_ne hri, Pi.single_apply, if_neg hri]

theorem unipRad_two_ne_bot {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (h1 : 1 ≤ n) (h2 : n < N) :
    unipRad k (stdBlocks ![n, N - n] h) ≠ ⊥ := by
  set i : Fin N := ⟨0, by omega⟩
  set j : Fin N := ⟨n, h2⟩
  have hne : i ≠ j := by
    intro e
    have := congrArg Fin.val e
    simp [i, j] at this
    omega
  let t : GL (Fin N) k := ⟨transvection i j 1, transvection i j (-1),
    by rw [transvection_mul_transvection_same i j hne]; simp,
    by rw [transvection_mul_transvection_same i j hne]; simp⟩
  have ht : t ∈ unipRad k (stdBlocks ![n, N - n] h) := by
    refine (mem_unipRad_two_iff h).2 fun r s hrs => ?_
    show transvection i j (1 : k) r s = _
    have : ¬ (r = i ∧ s = j) := by
      rintro ⟨rfl, rfl⟩
      exact hrs ⟨by simp [i]; omega, le_refl _⟩
    simp only [transvection, Matrix.add_apply]
    rw [Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact this ⟨rfl, rfl⟩
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ht
  simp [t, transvection, one_apply_ne hne] at this

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derChar_eq_one_of_mem_unipRad_two {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    (u : derUnip k N n) (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks ![n, N - n] h)) :
    derChar k ψ N n u = 1 := by
  have hE := (mem_unipRad_two_iff h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem twKer_unipRad_two_le {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 ≤ twKer π (derUnip k N n) (derChar k ψ N n) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_two_le_derUnip h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad_two ψ h _ u.2]
  simp

end Chars

theorem twKer_derUnip_eq_top_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  intro k _ _ _ _ ψ N n V _ _ π hπ h1 h2
  have h : ∑ c, ![n, N - n] c = N := by
    simp [Fin.sum_univ_two]
    omega
  have hs := hπ.2 2 ![n, N - n] (stdBlocks ![n, N - n] h) (unipRad_two_ne_bot h h1 h2)
  have htop : twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hs
  exact eq_top_iff.2 (htop ▸ twKer_unipRad_two_le ψ h π)

end GlobalTheory.CompanionTheory.BZMir
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTopStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twisted_kernel_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N → twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitone
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitone
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceSubgroups

theorem Km_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  intro k _ _ _ _ N m m' h
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have hg' : Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g = 1 := hg
  have h2 := congrArg (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)) hg'
  rw [map_one] at h2
  show Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g = 1
  rw [← h2]
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

end GlobalTheory.CompanionTheory.CongruenceSubgroups
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitoneStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | exact GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | (intros; apply GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivial
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.TensorIrr

theorem nontrivial_space_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Subsingleton.elim _ _))

theorem nontrivial_piTensorProduct_of_nontrivial {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  have hv : ∀ i, ∃ v : V i, v ≠ 0 := fun i => exists_ne 0
  choose v hv using hv
  have hf : ∀ i, ∃ f : Module.Dual ℂ (V i), f (v i) ≠ 0 := fun i => by
    by_contra hc
    exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1
      fun f => not_not.1 (not_exists.1 hc f))
  choose f hf using hf
  let F : (Π i, V i) →ₘₗ[ℂ] ℂ := (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f
  have hF : PiTensorProduct.lift F (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [PiTensorProduct.lift.tprod]
    simpa [F] using Finset.prod_ne_zero_iff.2 fun i _ => hf i
  refine ⟨PiTensorProduct.tprod ℂ v, 0, fun h => hF ?_⟩
  rw [h, map_zero]

theorem nontrivial_piTensorProduct_irrGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  intro k _ _ _ _ h x
  have : ∀ a, Nontrivial (x a).2.rep.V := fun a =>
    nontrivial_space_of_isIrreducible _ (x a).2.rep.irr
  exact nontrivial_piTensorProduct_of_nontrivial

end GlobalTheory.CompanionTheory.TensorIrr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivialStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_irreducible_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  first | exact @GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | exact GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | (intros; apply GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupFiniteVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupFiniteVolume
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_integralGL (N : ℕ) :
    IsCompact {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
      ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hO : IsCompact ((𝒪[k] : Subring k) : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hM : IsCompact {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    have h := isCompact_univ_pi fun _ : Fin N => isCompact_univ_pi fun _ : Fin N => hO
    have e : {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} =
        Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => ((𝒪[k] : Subring k) : Set k) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin N) (Fin N) k)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

theorem Km_subset_integralGL (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) ⊆
      {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
        ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  have key : ∀ (h : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := fun h i j =>
    ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j).2
  rintro g ⟨h, -, rfl⟩
  refine ⟨key h, fun i j => ?_⟩
  rw [← map_inv]
  exact key h⁻¹ i j

theorem measure_image_Km_lt_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) < ⊤ := by
  intro k _ _ _ _ N _ _ μ hμ m
  refine lt_of_le_of_lt (measure_mono (Set.image_mono (Km_subset_integralGL N m))) ?_
  exact ((isCompact_integralGL N).image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.KmVol
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupFiniteVolumeStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_finite_volume : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top | exact GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top | (intros; apply GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMono
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMono
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdCompat

theorem sum_castLE_eq_sum_filter {s : ℕ} (f : Fin s → ℕ) (c : Fin s) :
    ∑ b : Fin (c : ℕ), f (Fin.castLE c.2.le b) = ∑ j ∈ Finset.univ.filter (· < c), f j := by
  refine Finset.sum_bij (fun b _ => Fin.castLE c.2.le b) ?_ ?_ ?_ ?_
  · intro b _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b.2⟩
  · intro x _ y _ h
    exact Fin.castLE_injective _ h
  · intro j hj
    have hj' : (j : ℕ) < c := (Finset.mem_filter.1 hj).2
    exact ⟨⟨j, hj'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro _ _
    rfl

theorem partial_sum_drop_empty {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r)
    (ho : StrictMono o) (hr : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    ∑ b ∈ Finset.univ.filter (· < a), d (o b) = ∑ j ∈ Finset.univ.filter (· < o a), d j := by
  rw [← Finset.sum_image (s := Finset.univ.filter (· < a)) (g := o) (f := d)
    (fun x _ y _ h => ho.injective h)]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hj
    have hb' : b < a := (Finset.mem_filter.1 hb).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ho hb'⟩
  · intro j hj hj'
    by_contra hne
    obtain ⟨b, rfl⟩ := hr j hne
    have hlt : o b < o a := (Finset.mem_filter.1 hj).2
    exact hj' (Finset.mem_image.2
      ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, ho.lt_iff_lt.1 hlt⟩, rfl⟩)

theorem stdBlocks_drop_empty : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N)
    (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) →
    ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))),
      stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  intro r r' N d hd o ho hr hd' a t
  apply Fin.ext
  have h1 := stdBlocks_val (fun a => d (o a)) hd' a t
  have h2 := stdBlocks_val d hd (o a) t
  have h3 := sum_castLE_eq_sum_filter (fun a => d (o a)) a
  have h4 := sum_castLE_eq_sum_filter d (o a)
  have h5 := partial_sum_drop_empty d o ho hr a
  rw [h1, h2]
  rw [h3, h4, h5]

end GlobalTheory.CompanionTheory.StdCompat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMonoStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_blocks_reindex_strictMono : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))), stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  first | exact @GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty | exact GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty | (intros; apply GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacter
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZlScalar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow_range (u : kˣ) (n : ℕ) :
    ∏ a ∈ Finset.range n, ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ) =
      ((absPow k (((n * (n - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [← Finset.sum_range_id]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Nat.cast_add, absPow_add, MonoidHom.mul_apply,
      Units.val_mul]

theorem prod_fin_absPow (l : ℕ) (c : ℂ) (u : kˣ) :
    ∏ a : Fin l, (c * ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)) =
      c ^ l * ((absPow k (((l * (l - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun a => ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)), prod_absPow_range]

theorem smul_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f)
    (g : G) (C : ℂ) (h : ∀ w, π g w = C • w) (v : W) : σ g v = C • v := by
  obtain ⟨w, rfl⟩ := hf v
  rw [← map_smul, ← h w]
  exact (Representation.IntertwiningMap.isIntertwining π σ f g w).symm

theorem exists_surjective_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π) :
    ∃ f : π.IntertwiningMap σ, Function.Surjective f :=
  let ⟨_, f, hf, _⟩ := h
  ⟨f, hf⟩

theorem smul_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π)
    (g : G) (C : ℂ) (hg : ∀ w, π g w = C • w) (v : W) : σ g v = C • v :=
  let ⟨f, hf⟩ := exists_surjective_of_isCosocle h
  smul_of_surjective f hf g C hg v

theorem scalarBy_term (Δ : Segment k) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) (a : Fin Δ.len) :
    Zl.ScalarBy (Δ.term a) t (c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) :=
  GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first ((a : ℕ) : ℂ) t c hc

theorem scalarBy_lseg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) (y : IrrGL (k := k)) (hy : IsLSeg Δ y.rep) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) :
    Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  rcases hy with ⟨hd, hco⟩
  have key := GlobalTheory.CompanionTheory.ZCentre.prodIrr_scalar k Δ.len y.1 Δ.term hd t (fun a => c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) (scalarBy_term Δ t c hc)
  simp only [prod_fin_absPow] at key
  intro v
  exact smul_of_isCosocle hco (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) _ key v

end GlobalTheory.CompanionTheory.ZlScalar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Δ.first t c → Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | exact GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | (intros; apply GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientCartanTranslate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientCartanTranslate
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceCoef

theorem conj_mem_Km (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N m : ℕ) {p x : GL (Fin N) k}
    (hp : p ∈ KO k (Fin N)) (hx : x ∈ Zls.Km k N m) : p * x * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (MonoidHom.normal_ker _).conj_mem b hb a

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem coef_const_translated_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  intro k _ _ _ _ N V _ _ π m v hv l hl p1 p2 hp1 hp2
  have hv' := (mem_fixed_iff π _ v).1 hv
  have h1 : ∀ y ∈ Zls.Km k N m, π y (π p2 v) = π p2 v := by
    intro y hy
    have hc : p2⁻¹ * y * p2⁻¹⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m (inv_mem hp2) hy
    have e : y * p2 = p2 * (p2⁻¹ * y * p2⁻¹⁻¹) := by group
    have h := hv' _ hc
    calc π y (π p2 v) = π (y * p2) v := by rw [map_mul, Module.End.mul_apply]
      _ = π p2 (π (p2⁻¹ * y * p2⁻¹⁻¹) v) := by rw [e, map_mul, Module.End.mul_apply]
      _ = π p2 v := by rw [h]
  have h2 : ∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1 := by
    intro x hx
    have hc : p1 * x * p1⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m hp1 hx
    have e : p1 * x = (p1 * x * p1⁻¹) * p1 := by group
    have h := hl _ hc
    ext w
    have hw := LinearMap.congr_fun h (π p1 w)
    simp only [LinearMap.comp_apply] at hw ⊢
    calc l (π p1 (π x w)) = l (π (p1 * x) w) := by rw [map_mul, Module.End.mul_apply]
      _ = l (π (p1 * x * p1⁻¹) (π p1 w)) := by rw [e, map_mul, Module.End.mul_apply]; simp
      _ = l (π p1 w) := hw
  refine ⟨(mem_fixed_iff π _ _).2 h1, h2, ?_⟩
  intro D x hx y hy
  have h3 := LinearMap.congr_fun (h2 x hx) (π D (π p2 v))
  simp only [LinearMap.comp_apply] at h3
  have e : π (p1 * x * D * y * p2) v = π p1 (π x (π D (π y (π p2 v)))) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, h1 y hy, h3]
  simp only [LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.CongruenceCoef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientCartanTranslateStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_cartan_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset | exact GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset | (intros; apply GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset <;> assumption)
end
end

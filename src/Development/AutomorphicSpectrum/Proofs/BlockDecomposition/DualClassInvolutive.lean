module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.Zcore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) : IsAdmissible x.rep := by
  exact hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr

theorem isIrreducible_contra_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x) x.2.rep.irr

theorem dualCl_eq_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra_rep hA x)]

private theorem dualCl_eq_of_eq_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL (k := k))
    (hy : y = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x)) :
    dualCl y = x := by
  subst hy
  rw [dualCl_eq_of hA]
  conv_rhs => rw [← IrrGL.of_rep x]
  exact IrrGL.of_eq_of.mpr ⟨(GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf (contra x.rep) _ _)).trans
    (GlobalTheory.ContraRefl.evEquiv (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x)).symm⟩

theorem dualCl_dualCl : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)),
    dualCl (dualCl x) = x := by
  intro k _ _ _ _ hA x
  exact dualCl_eq_of_eq_contra hA x _ (dualCl_eq_of hA x)

end GlobalTheory.CompanionTheory.Zcore

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_involutive : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), dualCl (dualCl x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | exact GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | (intros; apply GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.GKLocalProof

theorem invT_eq_invTranspose {A : Type} [CommRing A] (N : ℕ) :
    (invT : GL (Fin N) A →* GL (Fin N) A) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N A :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem gkLocal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  intro k _ _ _ _ hA N V _ _ π hs hi
  rw [invT_eq_invTranspose]
  exact GlobalTheory.GelfandKazhdan.equiv_contra k N V π (hA k N V π hs hi) hi

end GlobalTheory.CompanionTheory.GKLocalProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_of_irreducible_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GKLocalProof.gkLocal | exact GlobalTheory.CompanionTheory.GKLocalProof.gkLocal | (intros; apply GlobalTheory.CompanionTheory.GKLocalProof.gkLocal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer

theorem twKer_resM_derUnipM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + 1)) k) V),
    twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  intro k _ _ _ _ ψ m n V _ _ π
  unfold twKer
  congr 1
  ext w
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n) u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    refine ⟨(Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n)).symm u, v, ?_⟩
    simp [derCharM, resM]
    rfl

end GlobalTheory.CompanionTheory.BZMirDer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernelStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_mirabolic_twisted_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V), twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM | exact GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaW

def revMat (A : Type) [CommRing A] (N : ℕ) : Matrix (Fin N) (Fin N) A :=
  (1 : Matrix (Fin N) (Fin N) A).submatrix Fin.rev id

theorem revMat_mul {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    revMat A N * M = M.submatrix Fin.rev id := by
  ext i j
  simp [revMat, Matrix.mul_apply, Matrix.one_apply]

theorem mul_revMat {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    M * revMat A N = M.submatrix id Fin.rev := by
  ext i j
  simp only [revMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro b _ hb
    rw [if_neg, mul_zero]
    intro h
    exact hb (by rw [← h, Fin.rev_rev])
  · simp

theorem revMat_mul_self (A : Type) [CommRing A] (N : ℕ) : revMat A N * revMat A N = 1 := by
  rw [revMat_mul]
  ext i j
  simp [revMat, Matrix.one_apply]

def w₀ (A : Type) [CommRing A] (N : ℕ) : GL (Fin N) A :=
  ⟨revMat A N, revMat A N, revMat_mul_self A N, revMat_mul_self A N⟩

theorem thetaW_eq_conj (A : Type) [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N g = w₀ A N * invT g * (w₀ A N)⁻¹ := by
  apply Units.ext
  show _ = revMat A N * (invT g).1 * revMat A N
  rw [revMat_mul, mul_revMat]
  ext i j
  simp [thetaW, Matrix.reindexAlgEquiv_apply]

def compInvTEquiv {A : Type} [CommRing A] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) A) V) :
    Representation.Equiv (π.comp invT) (π.comp (thetaW A N)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (π (w₀ A N)) (π (w₀ A N)⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun g => LinearMap.ext fun v => by
      show π (w₀ A N) (π (invT g) v) = π (thetaW A N g) (π (w₀ A N) v)
      rw [thetaW_eq_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]

theorem comp_thetaW_equiv_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  intro k _ _ _ _ hGK N V _ _ π hs hi
  obtain ⟨e⟩ := hGK N π hs hi
  exact ⟨(compInvTEquiv π).symm.trans e⟩

end GlobalTheory.CompanionTheory.ThetaW

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredientStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_kazhdan_contragredient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | exact GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | (intros; apply GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotient
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Words

theorem wd_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (hπ : IsSmooth π) (h : IsSubquotient σ π) (w : List (IrrGL (k := k))) (hw : Wd σ w) : Wd π w := by
  obtain ⟨hd, hne⟩ := hw
  refine ⟨hd, ?_⟩
  exact jhMult_ne_zero_iff.2
    ((jhMult_ne_zero_iff.1 hne).trans (GlobalTheory.JacquetExact.isSubquotient_jac _ hπ h))

end GlobalTheory.CompanionTheory.Words
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_of_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → IsSubquotient σ π → ∀ w : List (IrrGL (k := k)), Wd σ w → Wd π w := by
  first | exact @GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient | exact GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      GlobalTheory.BZMir.eLast k n j :=
    fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
  have hblock : ∀ i j : Fin n,
      ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
        (1 : Matrix (Fin n) (Fin n) k) i j :=
    fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hy
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
  apply Units.ext
  ext i j
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
  rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
      GlobalTheory.BZMir.eLast]
  · simp [hrow, GlobalTheory.BZMir.eLast]

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

theorem mem_MirUin_iff_mem_derUnipM (k : Type) [Field k] (n : ℕ) (g : Mir k n) :
    g ∈ MirUin k n ↔ g ∈ derUnipM k n n := by
  rw [MirUin, derUnipM, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, derUnip, Subgroup.mem_inf]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i hi => ?_⟩
    · have hj : j ≠ Fin.last n := fun h => by
        subst h; exact absurd hji (not_lt.2 (Fin.le_last i))
      have hij : i ≠ j := (ne_of_lt hji).symm
      simp [unip, colMat, Matrix.one_apply, hj, hij]
    · by_cases hi : i = Fin.last n
      · subst hi; simp [unip, colMat]
      · simp [unip, colMat, hi]
    · have hi' : i ≠ Fin.last n := fun h => by subst h; simp at hi
      ext l
      simp [unip, colMat, hi', Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm]
  · rintro ⟨hB, hC⟩
    refine ⟨Multiplicative.ofAdd (fun i => (g : GL (Fin (n + 1)) k).val (Fin.castSucc i) (Fin.last n)), ?_⟩
    ext i j
    show (1 + colMat k n _) i j = _
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp [colMat, ((mem_unipB k).1 hB).2]
      | cast i => simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      have h := congrFun (hC (Fin.castSucc j) (by simp)) i
      rw [mulVec_single_one] at h
      simp only [Matrix.col_apply] at h
      rw [h]
      simp [colMat, Fin.castSucc_ne_last, Matrix.one_apply, Pi.single_apply]

theorem derCharM_self_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (x : derUnipM k n n) : derCharM k ψ n n x = 1 := by
  change Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
    (fun p : Fin (n + 1) × Fin (n + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), _)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  have h := (Finset.mem_filter.1 hp).2
  have := p.2.isLt
  omega

theorem twKer_MirUin_eq_derUnipM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) :
    twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).1 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).2 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]

end GlobalTheory.CompanionTheory.BZMir
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | exact GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mirProj (n : ℕ) : Continuous (mirabolicProjection k n) := by
  have hval : Continuous fun g : Mir k n =>
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp continuous_subtype_val
  have hblock : Continuous fun g : Mir k n =>
      ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
  have hinv : Continuous fun g : Mir k n => g⁻¹ := by
    exact continuous_inv
  refine Units.continuous_iff.2 ⟨hblock, ?_⟩
  have : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    funext g
    rw [map_inv]
  show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
  rw [this]
  exact hblock.comp hinv

end GlobalTheory.CompanionTheory.BZMirFun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.DualCusp

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem isSupercuspidal_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (hs : IsSupercuspidal π) :
    IsSupercuspidal (contra π) := by
  refine ⟨isSmooth_contra π, fun l Λ hΛ => ?_⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.ContraRefl.evMap_bijective hG hπ).2 ⟨Λ, hΛ⟩
  have hev : ∀ m : smoothPart π.dual, Λ m = (m : Module.Dual ℂ V) u := fun m =>
    (LinearMap.congr_fun (congrArg Subtype.val hu) m).symm
  obtain ⟨C, hC, hsupp⟩ := hs.2 u l l.2
  open scoped Pointwise in
    refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
    rw [hev, contra_apply] at hg
    obtain ⟨z, hz, c, hc, e⟩ := hsupp g⁻¹ hg
    refine ⟨z⁻¹, inv_mem hz, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
    have h1 : g = (z * c)⁻¹ := by rw [← e, inv_inv]
    rw [h1, mul_inv_rev]
    exact (Subgroup.mem_center_iff.1 (inv_mem hz) c⁻¹)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_isCusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) :
    (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  have hadm : IsAdmissible x.rep := hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k x.1
  have hirr : (contra x.rep).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG hadm x.2.rep.irr
  have hd : dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) hirr := dif_pos hirr
  rw [hd]
  refine ⟨IrrGL.isCusp_of.2 ⟨hx.1, ?_⟩, rfl⟩
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k x.1 _ _
    (isSupercuspidal_contra hG hadm (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k x.1 _ _ hx.2))

end GlobalTheory.CompanionTheory.DualCusp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidalStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), x.IsCusp → (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | exact GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | (intros; apply GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CosocleContra

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isIrreducible_quot_of_isCoatom {L : Subrepresentation π} (hL : IsCoatom L) :
    (ProjLine.quot L).IsIrreducible := by
  have h1 : L.toSubmodule ≠ ⊤ := fun e => hL.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (ProjLine.quot L)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π :=
    ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hLT : L ≤ T' := fun v hv => by
    have h0 : L.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
    show L.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [h0]
    exact zero_mem _
  rcases eq_or_lt_of_le hLT with e | e
  · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := hy
    rw [← e] at hv
    exact (Submodule.Quotient.mk_eq_zero _).2 hv
  · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := (hL.2 _ e) ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    exact hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullContra (S : Subrepresentation π) : (contra (ProjLine.quot S)).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show (ProjLine.quot S).dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v =>
          LinearMap.congr_fun (show (ProjLine.quot S).dual g l.1 = l.1 from hg) (S.toSubmodule.mkQ v))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem pullContra_injective (S : Subrepresentation π) : Function.Injective (pullContra S) := fun a b h =>
  Subtype.ext (LinearMap.ext fun y => by
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem pullContra_apply_eq_zero (S : Subrepresentation π) (l : smoothPart (ProjLine.quot S).dual) {v : V}
    (hv : v ∈ S) : (pullContra S l).1 v = 0 := by
  have h0 : S.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
  show l.1 (S.toSubmodule.mkQ v) = 0
  rw [h0, map_zero]

theorem eq_of_isCoatom_of_mem_range {S S' : Subrepresentation π} (hS : IsCoatom S) (hS' : IsCoatom S')
    {w : smoothPart π.dual} (hw : w ≠ 0) (h : w ∈ (pullContra S).range) (h' : w ∈ (pullContra S').range) :
    S = S' := by
  by_contra hne
  have top := hS.sup_eq_top_of_ne hS' hne
  obtain ⟨l, rfl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  refine hw (Subtype.ext (LinearMap.ext fun v => ?_))
  have hv : v ∈ (S ⊔ S').toSubmodule := by
    rw [top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have h1 := pullContra_apply_eq_zero S l ha
  have h2 := pullContra_apply_eq_zero S' l' hb
  have h3 : (pullContra S l).1 b = 0 := (congrArg (fun y : smoothPart π.dual => y.1 b) hl').symm.trans h2
  show (pullContra S l).1 (a + b) = 0
  rw [map_add (f := _), h1, h3, add_zero]

end General

theorem isCosocle_of_isSocle_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  intro k _ _ _ _ hA N V _ _ π hπ hfl τ' hτ
  obtain ⟨hi, f, hf, hat⟩ := hτ
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis (k := k) N
  have hat0 : IsAtom f.range := isAtom_range hi f hf
  have hsm : ∀ S : Subrepresentation π, IsSmooth (ProjLine.quot S) := fun S =>
    (IsSubquotient.of_surjective (ProjLine.quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, IsCoatom S → (pullContra S).range = f.range := fun S hS => by
    have hirr := isIrreducible_quot_of_isCoatom hS
    exact hat _ (isAtom_range (GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (hsm S) hirr) hirr) _
      (pullContra_injective S))
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    refine hat0.1 (eq_bot_iff.2 ?_)
    rintro _ ⟨x, rfl⟩
    exact (h x).symm ▸ zero_mem (⊥ : Subrepresentation (contra π)).toSubmodule
  haveI : WellFoundedGT (Subrepresentation π) := ((hasFiniteLength_iff_wellFounded π).1 hfl).1
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := fun e => hx (Subtype.ext (LinearMap.ext fun v => by
    have hv : v ∈ (⊥ : Subrepresentation π) := e ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
    rw [hv0, map_zero]
    rfl))
  obtain ⟨L, hL, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation π)).resolve_left hbt
  have huniq : ∀ S : Subrepresentation π, IsCoatom S → S = L := fun S hS =>
    eq_of_isCoatom_of_mem_range hS hL hx ((key S hS).symm ▸ ⟨x, rfl⟩) ((key L hL).symm ▸ ⟨x, rfl⟩)
  have hall : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤ := fun S => by
    rcases eq_top_or_exists_le_coatom S with h | ⟨M, hM, hSM⟩
    · exact Or.inr h
    · exact Or.inl (huniq M hM ▸ hSM)
  have hc := ProjLine.isCosocle_quot hL.1 hall
  exact ⟨⟨_, ProjLine.quot L, hsm L, hc.1⟩, hc⟩

end GlobalTheory.CompanionTheory.CosocleContra

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosocle_of_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  first | exact @GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | exact GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | (intros; apply GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaAd

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a r : ℕ} (x : BlockIx a r → R) :
    GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM (fun p => f (x p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r s : ℕ)
    (m : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map f (lev R r s m) =
      lev S r s (GeneralLinearGroup.map f m.1, GeneralLinearGroup.map f m.2) := by
  apply Units.ext
  ext i j
  change f (((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) i j) = ((lev S r s _ : GL (Fin (r + s)) S) : Matrix _ _ S) i j
  have val_emb (T : Type) [CommRing T] (g : GL (Fin r) T × GL (Fin s) T) :
      (GlobalTheory.SmGL.emb₂ T (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g : Matrix _ _ T) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
          (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
        GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply]
  rw [lev, lev, val_emb, val_emb]
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Subgroup (GL (Fin n) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin n) (Af E)))) :
    ∃ T : Finset (GL (Fin n) (Af E)), ∀ c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n,
      ∃ t ∈ T, ∃ l ∈ L, c = t * l := by
  obtain ⟨T, hT⟩ := (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).elim_finite_subcover
    (fun t : GL (Fin n) (Af E) => (fun z => t⁻¹ * z) ⁻¹' (L : Set (GL (Fin n) (Af E))))
    (fun t => hL.preimage (continuous_const.mul continuous_id))
    (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [L.one_mem]⟩)
  refine ⟨T, fun c hc => ?_⟩
  obtain ⟨t, ht, hl⟩ := Set.mem_iUnion₂.1 (hT hc)
  exact ⟨t, ht, t⁻¹ * c, hl, by group⟩

theorem iwasawa_finite_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  intro E _ _ _ r s L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E (r + s) L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) g)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, rfl⟩ := hT c hc
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add (f := _), show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add (f := _), show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), t, k, l, ht, hl, ga_ext ?_ ?_⟩
  · simp only [map_mul, map_unip, map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [map_mul, map_unip, map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.IwaAd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.DerWhit

private theorem twKer_congr' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {H H' : Subgroup G} (h : H = H') (θ : H →* ℂˣ) (θ' : H' →* ℂˣ)
    (hθ : ∀ (x : G) (hx : x ∈ H), θ' ⟨x, h ▸ hx⟩ = θ ⟨x, hx⟩) :
    GlobalTheory.PRep.twKer ρ H θ = GlobalTheory.PRep.twKer ρ H' θ' := by
  subst h
  obtain rfl : θ' = θ := MonoidHom.ext fun x => hθ x x.2
  rfl

theorem colFix_zero (k : Type) [Field k] (N : ℕ) : colFix k N 0 = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  exact fun i hi => absurd hi (Nat.not_lt_zero _)

theorem mem_derUnip_zero (k : Type) [Field k] (N : ℕ) {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N)) :
    g ∈ derUnip k N 0 := by
  unfold GlobalTheory.BZMir.derUnip
  exact Subgroup.mem_inf.2 ⟨hg, GlobalTheory.CompanionTheory.DerWhit.colFix_zero k N ▸ Subgroup.mem_top g⟩

theorem whitCharFrom_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (u : unipB k (Fin N)) :
    whitCharFrom k ψ N 0 u = whitChar ψ N u := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar]
  | (simp only [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar, MonoidHom.coe_mk,
        OneHom.coe_mk]
     congr 2
     exact Finset.sum_congr (by ext p; simp) fun _ _ => rfl)

theorem twKer_derUnip_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  have hU : GlobalTheory.BZMir.derUnip k N 0 = GlobalTheory.SmGL.unipB k (Fin N) :=
    le_antisymm (GlobalTheory.BZMir.derUnip_le_unipB k N 0)
      fun g hg => GlobalTheory.CompanionTheory.DerWhit.mem_derUnip_zero k N hg
  refine twKer_congr' π hU _ _ fun x hx => ?_
  exact (GlobalTheory.CompanionTheory.DerWhit.whitCharFrom_zero ψ N ⟨x, hU ▸ hx⟩).symm

end GlobalTheory.CompanionTheory.DerWhit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernelStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_zero_whittaker_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | exact GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | (intros; apply GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.RatDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

theorem ratCent_le (d : GL (Fin n) E) : ratCent d ≤ adCent d := by
  rintro _ ⟨g, hg, rfl⟩
  have h : twConj (thetaE E n) g d = d := hg
  change twConj (thetaA E n) (ratGL E n g) (ratGL E n d) = ratGL E n d
  rw [twConj, thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h

theorem discrete_ratIn (d : GL (Fin n) E) : DiscreteTopology (ratIn d) := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := n)
  have hmem : ∀ x : ratIn d, (x.1.1 : GA E n) ∈ (ratGL E n).range := fun x => by
    obtain ⟨g, -, hg⟩ := (Subgroup.mem_subgroupOf.1 x.2)
    exact ⟨g, hg⟩
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : ratIn d => (⟨x.1.1, hmem x⟩ : (ratGL E n).range)) ?_ ?_
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    have h' : (x.1.1 : GA E n) = y.1.1 := congrArg (fun z : (ratGL E n).range => (z : GA E n)) h
    exact Subtype.ext (Subtype.ext h')

theorem isClosed_adCent (d : GL (Fin n) E) : IsClosed (adCent d : Set (GA E n)) := by
  haveI : T2Space (GA E n) := by
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
    exact Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous fun g : GA E n => twConj (thetaA E n) g (ratGL E n d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA
  exact isClosed_eq hc continuous_const

theorem measurable_sdot {m : ℕ} (e : Fin m → SignType) :
    Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => sdot e p.2 := by
  unfold sdot
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_snd).const_mul _

theorem measurable_gam (m : ℕ) :
    Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => gam p.1 p.2 := by
  classical
  unfold gam gamOn
  refine Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.const_mul (Finset.measurable_prod _ fun e _ => ?_) _
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt ((measurable_pi_apply e).comp measurable_fst) (measurable_sdot e)

theorem ratDisc : PositivityTheory.Rg.BcB.D4.RatDisc :=
  ⟨fun _ _ _ _ _ d => ⟨ratCent_le d, discrete_ratIn d, isClosed_adCent d⟩, measurable_gam⟩

end GlobalTheory.CompanionTheory.RatDisc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem mirChar_eq_thetaA_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.BZMir.Fun.MirCharEq k := by
  intro ψ n
  have h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1) := by
    ext v
    simp [chrV, chrA]
  rw [mirChar, thetaA, h]

end GlobalTheory.CompanionTheory.BZMir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEqStatement
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_character_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.MirCharEq k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | exact GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | (intros; apply GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

theorem wtW_isCusp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k) :
    ∀ c ∈ wtW Δ, c.IsCusp := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hcl
  exact Segment.isCusp_term _ _

end GlobalTheory.CompanionTheory.ZcWords
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_word_letters_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k), ∀ c ∈ wtW Δ, c.IsCusp := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | exact GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | (intros; apply GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp <;> assumption)
end
end

module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolic
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem wGL_conj_apply (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * g * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e1 : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  have e2 : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2]
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (x : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) x) = ePG i t x := by
  simp [wPerm]

theorem mem_HPG_iff_conj_mem_parab (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)) :
    p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  show (p : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t) ↔ _
  rw [mem_parab_iff, mem_parab_iff]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun x => forall_congr' fun y => ?_
  rw [wGL_conj_apply, wPerm_two, wPerm_two]

end GlobalTheory.CompanionTheory.BZRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolicStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_HPG_iff_conjugate_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)), p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab | exact GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab | (intros; apply GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacter
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hpg_wGL_conj_apply {i t : ℕ} (h : (i + 1) + t = i + t + 1) (G : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * G * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (G : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  have e' : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  rw [Units.val_mul, Units.val_mul, e, e']
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem hpg_wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) y) = ePG i t y := by
  simp [wPerm]

theorem hpg_leviProj_wGL_conj {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : HPG k i t)
    (hq : wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (x : Bool) :
    leviProj k (two (stdSum h)) ⟨_, hq⟩ x = leviProj k (ePG i t) (hpgIncl k i t g) x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [leviProj_apply, leviProj_apply]
  show ((wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) _ _ = _
  rw [hpg_wGL_conj_apply, hpg_wPerm_two, hpg_wPerm_two]
  rfl

theorem open_orbit_twist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  intro k _ _ _ _ V W _ _ _ _ i j h π₁ π₂ g hq v
  have hf : leviProj k (two (stdSum h)) ⟨_, hq⟩ false = ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) :=
    hpg_leviProj_wGL_conj h g hq false
  have ht : leviProj k (two (stdSum h)) ⟨_, hq⟩ true = (pgProj k i (j + 1) g).2 :=
    hpg_leviProj_wGL_conj h g hq true
  have hδ : (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) =
      (absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) *
      (absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) := by
    have e := deltaHalf_two (k := k) (a := Fin (i + 1)) (b := Fin (j + 1))
      (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true)
    have e2 : leviTwo k (Fin (i + 1)) (Fin (j + 1))
        (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true) =
        leviProj k (two (stdSum h)) ⟨_, hq⟩ := by
      funext x
      cases x <;> rfl
    rw [e2, hf, ht] at e
    rw [e, Units.val_mul]
    simp only [Fintype.card_fin]
    push_cast
    rfl
  have key : ∀ x : ∀ b, TwoT V W b, ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
        (tE V W (PiTensorProduct.tprod ℂ x)) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have hr : tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
          (π₁ (leviProj k (two (stdSum h)) ⟨_, hq⟩ false) (x false) ⊗ₜ[ℂ]
            π₂ (leviProj k (two (stdSum h)) ⟨_, hq⟩ true) (x true)) := by
      show tE V W ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
        piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum h)) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [piTensor_tprod, map_smul, Exponents.boolTensorEquiv_tprod]
      rfl
    rw [hr, hf, ht, hδ, Exponents.boolTensorEquiv_tprod]
    refine (extTensor_tmul _ _ _ (x false) (x true)).trans ?_
    show ((absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) •
        π₁ ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) (x false)) ⊗ₜ[ℂ]
      ((absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) •
        π₂ (pgProj k i (j + 1) g).2 (x true)) = _
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]
  let A : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W := ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
  have hlin : A ∘ₗ (tE V W).toLinearMap = (tE V W).toLinearMap ∘ₗ sQ h π₁ π₂ ⟨_, hq⟩ :=
    PiTensorProduct.ext (MultilinearMap.ext fun x => key x)
  exact LinearMap.congr_fun hlin v

end GlobalTheory.CompanionTheory.BZRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacterStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_inducing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.open_orbit_twist | exact GlobalTheory.CompanionTheory.BZRes.open_orbit_twist | (intros; apply GlobalTheory.CompanionTheory.BZRes.open_orbit_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosed
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.MirClosed

theorem isClosed_mirabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
      IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  intro k _ _ _ _ n
  haveI : T2Space k := GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField (k := k)
  have e : (Mir k n : Set (GL (Fin (n + 1)) k)) =
      ⋂ j : Fin (n + 1), {g : GL (Fin (n + 1)) k |
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = eLast k n j} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rw [mem_Mir_iff k g]
    exact funext_iff
  rw [e]
  have hval : Continuous fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val
  refine isClosed_iInter fun j => ?_
  exact isClosed_eq ((continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hval))
    continuous_const

end GlobalTheory.CompanionTheory.BZRes.MirClosed
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosedStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic | exact GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic | (intros; apply GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellInducingCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellInducingCharacter
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem hgp_twist_tE {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j n : ℕ} (h : (i + 1) + j = n)
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HGPg k h)
    (hq : (1 : GL (Fin (n + 1)) k) * ((g : Mir k n) : GL (Fin (n + 1)) k) * (1 : GL (Fin (n + 1)) k)⁻¹ ∈
      parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g (tE V W v) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  have hL : leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩ =
      leviTwo k (Fin (i + 1)) (Fin (j + 1)) ((gpProjg k h g).1, ((gpProjg k h g).2 : GL (Fin (j + 1)) k)) := by
    have e : (⟨_, hq⟩ : parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1)))) = hgpInclg k h g :=
      Subtype.ext (by simp [hgpInclg])
    rw [e]
    funext x
    cases x <;> rfl
  have key : ∀ x : ∀ b, TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    set g₁ : GL (Fin (i + 1)) k := (gpProjg k h g).1 with hg₁
    set g₂ : Mir k j := (gpProjg k h g).2 with hg₂
    have hl : ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
        ((GlobalTheory.SmGL.twist π₁ (dpow (i + 1) (((j + 1 : ℕ) : ℝ) / 2)) g₁ (x false) : V) ⊗ₜ[ℂ]
          (GlobalTheory.SmGL.twist (π₂.comp (Mir k j).subtype) (dpowM j (-((i + 1 : ℕ) : ℝ) / 2)) g₂ (x true) : W) : V ⊗[ℂ] W) :=
      (congrArg _ (Exponents.boolTensorEquiv_tprod x)).trans (extTensor_tmul _ _ _ _ _)
    have hr : tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviTwo k (Fin (i + 1)) (Fin (j + 1)) (g₁, (g₂ : GL (Fin (j + 1)) k))) : ℂˣ) : ℂ) •
          ((π₁ g₁ (x false) : V) ⊗ₜ[ℂ] (π₂ (g₂ : GL (Fin (j + 1)) k) (x true) : W) : V ⊗[ℂ] W) := by
      show tE V W (GlobalTheory.SmGL.twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))))
        (leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [hL, twist_apply, piTensor_tprod, map_smul]
      exact congrArg _ (Exponents.boolTensorEquiv_tprod _)
    rw [hl, hr, deltaHalf_two]
    simp only [twist_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, MonoidHom.comp_apply,
      Units.val_mul, dpow, dpowM, detChar_apply]
    have c₁ : ((((j + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = (Fintype.card (Fin (j + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    have c₂ : ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = -(Fintype.card (Fin (i + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    rw [c₁, c₂, mul_comm]
    rfl
  have := LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext key) :
    ((((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g) ∘ₗ (tE V W).toLinearMap) =
      (tE V W).toLinearMap ∘ₗ (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩)) v
  exact this

end GlobalTheory.CompanionTheory.BZRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellInducingCharacterStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_cell_inducing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j n : ℕ} (h : (i + 1) + j = n) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HGPg k h) (hq : (1 : GL (Fin (n + 1)) k) * ((g : Mir k n) : GL (Fin (n + 1)) k) * (1 : GL (Fin (n + 1)) k)⁻¹ ∈ parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1)))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g (tE V W v) = tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.hgp_twist_tE | exact GlobalTheory.CompanionTheory.BZRes.hgp_twist_tE | (intros; apply GlobalTheory.CompanionTheory.BZRes.hgp_twist_tE <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDoubleCosetCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDoubleCosetCriterion
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

theorem eLast_vecMul {k : Type} [Field k] (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    vecMul (eLast k n) M = M (Fin.last n) := by
  ext j
  simp [eLast, vecMul, dotProduct, Pi.single_apply]

theorem mem_two_iff {k : Type} [Field k] {r t N : ℕ} (h : r + t = N) (g : GL (Fin N) k) :
    g ∈ parab k (two (stdSum h)) ↔
      ∀ a b : Fin N, r ≤ (a : ℕ) → (b : ℕ) < r → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hg a b ha hb
    have hlt : (a : ℕ) - r < t := by have := a.isLt; omega
    have ea : stdSum h (Sum.inr ⟨(a : ℕ) - r, hlt⟩) = a := Fin.ext (by rw [stdSum_inr]; simp only []; omega)
    have eb : stdSum h (Sum.inl ⟨(b : ℕ), hb⟩) = b := Fin.ext (by rw [stdSum_inl])
    have := mem_parab_iff.1 hg true false (⟨(a : ℕ) - r, hlt⟩ : Fin t) (⟨(b : ℕ), hb⟩ : Fin r) (by decide)
    rw [two_true, two_false, ea, eb] at this
    exact this
  · intro hg
    refine mem_parab_iff.2 ?_
    intro x y u v hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
    refine hg _ _ ?_ ?_
    · show r ≤ ((stdSum h (Sum.inr u) : Fin N) : ℕ)
      rw [stdSum_inr]; omega
    · show ((stdSum h (Sum.inl v) : Fin N) : ℕ) < r
      rw [stdSum_inl]; exact v.isLt

theorem mem_dcos_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ↔
      ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0 := by
  intro k _ _ _ _ i t h ht g
  have hlast : i + 1 ≤ ((Fin.last (i + t) : Fin (i + t + 1)) : ℕ) := by
    rw [Fin.val_last]; omega
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩ a
    have hpi : p⁻¹ ∈ Mir k (i + t) := inv_mem hp
    have hpi' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        eLast k (i + t) := hpi
    have e : (q * 1 * p)⁻¹ = p⁻¹ * q⁻¹ := by simp
    have h1 : vecMul (eLast k (i + t)) ((p⁻¹ * q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        vecMul (eLast k (i + t)) ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
      rw [Units.val_mul, ← vecMul_vecMul, hpi']
    have hrow := (eLast_vecMul (i + t) _).symm.trans (h1.trans (eLast_vecMul (i + t) _))
    rw [e]
    refine (congrFun hrow _).trans ((mem_two_iff h _).1 (inv_mem hq) _ _ hlast ?_)
    rw [stdSum_inl]; exact a.isLt
  · intro hy
    classical
    let y : Fin (i + t + 1) → k :=
      ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t))
    have hyg : vecMul y (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
      have : y = vecMul (eLast k (i + t))
          ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := (eLast_vecMul _ _).symm
      rw [this, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
    have hfirst : ∀ c : Fin (i + t + 1), (c : ℕ) < i + 1 → y c = 0 := by
      intro c hc
      have e : stdSum h (Sum.inl ⟨(c : ℕ), hc⟩) = c := Fin.ext (by rw [stdSum_inl])
      have := hy ⟨(c : ℕ), hc⟩
      rw [e] at this
      exact this
    obtain ⟨a₀, ha₀⟩ : ∃ c, y c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : y = 0 := funext hcon
      rw [h0, zero_vecMul] at hyg
      have := congrFun hyg (Fin.last (i + t))
      simp [eLast] at this
    have hblock : i + 1 ≤ (a₀ : ℕ) := by
      by_contra hlt
      exact ha₀ (hfirst a₀ (by omega))
    let σ : Equiv.Perm (Fin (i + t + 1)) := Equiv.swap a₀ (Fin.last (i + t))
    have hσ : ∀ r : Fin (i + t + 1), i + 1 ≤ (r : ℕ) → i + 1 ≤ (σ r : ℕ) := by
      intro r hr
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · exact hlast
      · exact hblock
      · exact hr
    let B : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
      ((1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).updateRow a₀ y).submatrix σ id
    have hdet : B.det ≠ 0 := by
      simp only [B]
      rw [Matrix.det_permute, det_updateRow_one]
      refine mul_ne_zero ?_ ha₀
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    let b : GL (Fin (i + t + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet
    have hb : (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = B := rfl
    have hbQ : b ∈ parab k (two (stdSum h)) := by
      refine (mem_two_iff h b).2 fun r c hr hc => ?_
      rw [hb]
      simp only [B, submatrix_apply, id]
      by_cases e : σ r = a₀
      · rw [e, updateRow_self]
        exact hfirst c hc
      · rw [updateRow_ne e, one_apply_ne]
        intro e2
        have := hσ r hr
        rw [e2] at this
        omega
    refine ⟨b⁻¹, inv_mem hbQ, b * g, ?_, by simp⟩
    show vecMul (eLast k (i + t)) ((b * g : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)
    have hB : B (Fin.last (i + t)) = y := by
      funext c
      simp [B, σ]
    rw [Units.val_mul, ← vecMul_vecMul, eLast_vecMul, hb, hB]
    exact hyg

end GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDoubleCosetCriterionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_double_coset_criterion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k, g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ↔ ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.ClosedOrbit.mem_dcos_iff | exact GlobalTheory.CompanionTheory.BZRes.ClosedOrbit.mem_dcos_iff | (intros; apply GlobalTheory.CompanionTheory.BZRes.ClosedOrbit.mem_dcos_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProduct
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZRes

theorem isSmooth_sQ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N)
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  unfold GlobalTheory.CompanionTheory.BZRes.sQ
  refine GlobalTheory.SmGL.isSmooth_comp ?_ _
    (GlobalTheory.SmGL.ProdIrr.continuous_leviProj _)
  refine GlobalTheory.SmGL.isSmooth_twist ?_
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)
  refine GlobalTheory.SmGL.isSmooth_piTensor ?_
  intro x
  cases x
  · exact h₁
  · exact h₂

end GlobalTheory.CompanionTheory.BZRes
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProductStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_parabolic_induction_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), IsSmooth π₁ → IsSmooth π₂ → IsSmooth (sQ h π₁ π₂) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | exact GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | (intros; apply GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterion
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.OpenOrbit

section Perm

variable {k : Type} [Field k]

def permGL {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k where
  val := (1 : Matrix _ _ k).submatrix σ id
  inv := (1 : Matrix _ _ k).submatrix id σ
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv σ
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ σ _ σ.bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

theorem permGL_mul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (B : Matrix (Fin N) (Fin N) k) (a c : Fin N) :
    (((permGL σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) * B) a c = B (σ a) c := by
  show (((1 : Matrix (Fin N) (Fin N) k).submatrix σ id) * B) a c = _
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem vecMul_single_one {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (a : Fin N) :
    vecMul (Pi.single a 1) M = M a := by
  ext c
  simp [vecMul, dotProduct, Pi.single_apply]

end Perm

section Orbit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inr_ne_inl {r t N : ℕ} (h : r + t = N) (j : Fin t) (l : Fin r) :
    stdSum h (Sum.inr j) ≠ stdSum h (Sum.inl l) := fun e => by
  simpa using (stdSum h).injective e

theorem wPerm_first {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e]
  exact ePG_false_last i t

theorem lastRow_wInv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) 1 := by
  rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  ext c
  show (1 : Matrix _ _ k).submatrix id (wPerm h) (Fin.last (i + t)) c = _
  rw [← wPerm_first h]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem lastRow_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hp : p ∈ Mir k (i + t)) :
    vecMul (eLast k (i + t)) (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (stdSum h (Sum.inl (Fin.last i))) := by
  have hp' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t) :=
    (Mir k (i + t)).inv_mem hp
  rw [show (q * wGL k h * p)⁻¹ = p⁻¹ * (wGL k h)⁻¹ * q⁻¹ by simp [mul_assoc], Units.val_mul, Units.val_mul,
    ← vecMul_vecMul, ← vecMul_vecMul, hp', lastRow_wInv, vecMul_single_one]

theorem exists_ne_of_mem {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hq : q ∈ parab k (two (stdSum h))) (hp : p ∈ Mir k (i + t)) :
    ∃ a : Fin (i + 1), (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  let r : parab k (two (stdSum h)) := ⟨q⁻¹, inv_mem hq⟩
  let M : GL (Fin (i + 1)) k := leviProj k (two (stdSum h)) r false
  have hrow : ∀ a, (M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) (Fin.last i) a = 0 := fun a => by
    have e := congrFun (lastRow_inv h q p hp) (stdSum h (Sum.inl a))
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one, hc a] at e
    exact e.symm
  have h1 : ((M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) *
      ((M⁻¹ : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)) (Fin.last i) (Fin.last i) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  rw [Matrix.mul_apply] at h1
  simp [hrow] at h1

theorem exists_parab_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Fin (i + t + 1) → k) (a : Fin (i + 1))
    (ha : y (stdSum h (Sum.inl a)) ≠ 0) :
    ∃ b ∈ parab k (two (stdSum h)),
      (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (stdSum h (Sum.inl (Fin.last i))) = y := by
  obtain ⟨b, -, -, hb⟩ := exists_rowSec (k := k) (stdSum h (Sum.inl a))
  have hb0 := hb y ha
  have hbQ : b y ∈ parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · rw [hb0, two_true, two_false, Matrix.updateRow_ne (stdSum_inr_ne_inl h l a),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  have hmQ : (permGL (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i)))) : GL (Fin (i + t + 1)) k) ∈
      parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i))) (stdSum h (Sum.inr l)))
        (stdSum h (Sum.inl j)) = 0
      rw [Equiv.swap_apply_of_ne_of_ne (stdSum_inr_ne_inl h l a) (stdSum_inr_ne_inl h l _),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  refine ⟨_, mul_mem hmQ hbQ, ?_⟩
  funext c
  rw [Units.val_mul, permGL_mul_apply, Equiv.swap_apply_right, hb0, Matrix.updateRow_self]

theorem mem_of_ne {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a : Fin (i + 1))
    (ha : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0) :
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  obtain ⟨b, hbQ, hrow⟩ := exists_parab_row h _ a ha
  refine ⟨b⁻¹, inv_mem hbQ, (wGL k h)⁻¹ * b * g, ?_, by group⟩
  show vecMul (eLast k (i + t)) (((wGL k h)⁻¹ * b * g : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t)
  have e : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      vecMul (eLast k (i + t)) ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) := by
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, lastRow_wInv, vecMul_single_one, hrow, e,
    vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]

end Orbit

end GlobalTheory.CompanionTheory.BZRes.OpenOrbit

namespace GlobalTheory.CompanionTheory.BZRes

theorem mem_dcos_wGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔
      ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  intro k _ _ _ _ i t h _ g
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩
    exact OpenOrbit.exists_ne_of_mem h q p hq hp
  · rintro ⟨a, ha⟩
    exact OpenOrbit.mem_of_ne h g a ha

end GlobalTheory.CompanionTheory.BZRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_double_coset_criterion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k, g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔ ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff | exact GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff | (intros; apply GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

section AbstractL

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W₀ W₁ W₂ : Type} [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

def stabSub {A X : Type} [Group A] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ A X) (v : X) : Subgroup A where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem exists_lift [NonarchimedeanGroup G] {Q P : Subgroup G} {x : G} (hLS : LocSec Q P x)
    (σ : Representation ℂ Q W₁) (hσ : IsSmooth σ) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v))
    (Y : Set G) (hY : IsOpen Y) (hxY : ∀ p : P, x * (p : G) ∈ Y) (φ : cIndSpace H τ) :
    ∃ f : smoothPart (ind Q σ), resInd σ H hH τ E hE f = φ.1 ∧ ∀ g, f.1.1 g ≠ 0 → ∃ q ∈ Q, q * g ∈ Y := by
  obtain ⟨C, hC, hsup⟩ := φ.2
  let φ' : P → W₁ := fun p => E.symm (φ.1.1.1 p)
  have hopen : IsOpen ((stabSub (ind H τ) φ.1.1 : Subgroup P) : Set P) := φ.1.2
  have hφ' : ∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ' p' = σ q (φ' p) := by
    intro q p p' e
    have e1 : x * ((p' * p⁻¹ : P) : G) * x⁻¹ = (q : G) := by
      have : x * (p' : G) = (q : G) * x * (p : G) := e.symm
      push_cast
      rw [← mul_assoc, this]
      group
    have hh : p' * p⁻¹ ∈ H := (hH _).2 (e1 ▸ q.2)
    have e2 : φ.1.1.1 (((⟨_, hh⟩ : H) : P) * p) = τ ⟨_, hh⟩ (φ.1.1.1 p) := φ.1.1.2 ⟨_, hh⟩ p
    have e3 : ((⟨_, hh⟩ : H) : P) * p = p' := by simp
    rw [e3] at e2
    have e4 : φ.1.1.1 p = E (φ' p) := by simp [φ']
    have hq' : x * (((⟨_, hh⟩ : H) : P) : G) * x⁻¹ ∈ Q := (hH _).1 hh
    have e5 : (⟨_, hq'⟩ : Q) = q := Subtype.ext e1
    show E.symm (φ.1.1.1 p') = _
    rw [e2, e4, hE ⟨_, hh⟩ hq', e5, LinearEquiv.symm_apply_apply]
  have hinv : ∀ (p : P), ∀ κ ∈ stabSub (ind H τ) φ.1.1, φ' (p * κ) = φ' p := by
    intro p κ hκ
    have : (ind H τ κ φ.1.1).1 p = φ.1.1.1 p := congrArg (fun F : indSpace H τ => F.1 p) hκ
    exact congrArg E.symm this
  have hsupp : ∀ p : P, φ' p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G) := by
    intro p hp
    have hp' : φ.1.1.1 p ≠ 0 := fun h => hp (by simp [φ', h])
    obtain ⟨h, hh, c, hc, e⟩ := hsup p hp'
    refine ⟨c, hc, ⟨_, (hH h).1 hh⟩, ?_⟩
    rw [e]
    push_cast
    group
  obtain ⟨K, hK, hKY, hWD⟩ := GlobalTheory.T.section_constructed_from_double_coset hLS σ hσ φ' hφ' _ hopen hinv C hC Y hY (fun c _ => hxY c)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.T.induced_function_from_compact_data σ φ' C K hWD hsupp
  refine ⟨⟨⟨f, fun h g => h1 h g⟩, ?_⟩, ?_, ?_⟩
  · refine mem_smoothPart_of_nhds ?_
    filter_upwards [hK.mem_nhds (one_mem K)] with κ hκ
    exact Subtype.ext (funext fun y => h2 y κ hκ)
  · refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    show E (f (x * (p : G))) = _
    rw [h3]
    simp [φ']
  · intro g hg
    obtain ⟨q, c, hc, κ, hκ, e⟩ := h4 g hg
    refine ⟨(q : G)⁻¹, inv_mem q.2, ?_⟩
    have := hKY c hc κ hκ
    rw [e]
    convert this using 1
    group

theorem resInd_mem_cInd {Q P : Subgroup G} {x : G} (hLS : LocSec Q P x) (hP : IsClosed (P : Set G))
    (B₀ : Set G) (hB : IsCompact B₀) (hB1 : B₀ ∈ 𝓝 (1 : G))
    (K₀ : Set G) (hK₀ : IsCompact K₀) (hIw : ∀ g : G, ∃ q ∈ Q, ∃ c ∈ K₀, g = q * c)
    (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v))
    (f : smoothPart (ind Q σ)) (T : Set G) (hT : IsClosed T) (hTs : T ⊆ dcos Q P x)
    (hTQ : ∀ q ∈ Q, ∀ g ∈ T, q * g ∈ T) (hfT : ∀ p : P, f.1.1 (x * (p : G)) ≠ 0 → x * (p : G) ∈ T) :
    resInd σ H hH τ E hE f ∈ cIndSpace H τ := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.compact_transversal_double_coset hLS hP B₀ hB hB1 (K₀ ∩ T) (hK₀.inter_right hT) (fun g hg => hTs hg.2)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hp' : f.1.1 (x * (p : G)) ≠ 0 := fun h => hp (by
    show E _ = 0
    rw [h, map_zero])
  obtain ⟨q, hq, c, hc, e⟩ := hIw (x * (p : G))
  have hcT : c ∈ T := by
    have := hTQ _ (inv_mem hq) _ (hfT p hp')
    rwa [e, inv_mul_cancel_left] at this
  obtain ⟨q', hq', c', hc', e'⟩ := hD c ⟨hc, hcT⟩
  refine ⟨p * c'⁻¹, (hH _).2 ?_, c', hc', by group⟩
  have e1 : x * ((p * c'⁻¹ : P) : G) * x⁻¹ = q * q' := by
    push_cast
    rw [← mul_assoc, e, e']
    group
  rw [e1]
  exact mul_mem hq hq'

theorem two_orbits [NonarchimedeanGroup G] {Q P : Subgroup G} {w : G}
    (h1 : LocSec Q P 1) (hw : LocSec Q P w) (hP : IsClosed (P : Set G))
    (B₀ : Set G) (hB : IsCompact B₀) (hB1 : B₀ ∈ 𝓝 (1 : G))
    (K₀ : Set G) (hK₀ : IsCompact K₀) (hIw : ∀ g : G, ∃ q ∈ Q, ∃ c ∈ K₀, g = q * c)
    (hcov : ∀ g : G, g ∈ dcos Q P 1 ∨ g ∈ dcos Q P w) (hcl : IsClosed (dcos Q P 1))
    (hdis : Disjoint (dcos Q P 1) (dcos Q P w))
    (σ : Representation ℂ Q W₀) (hσ : IsSmooth σ)
    (H₁ : Subgroup P) (hH₁ : ∀ p : P, p ∈ H₁ ↔ (1 : G) * (p : G) * (1 : G)⁻¹ ∈ Q)
    (τ₁ : Representation ℂ H₁ W₁) (E₁ : W₀ ≃ₗ[ℂ] W₁)
    (hE₁ : ∀ (h : H₁) (hq : (1 : G) * ((h : P) : G) * (1 : G)⁻¹ ∈ Q) (v : W₀), τ₁ h (E₁ v) = E₁ (σ ⟨_, hq⟩ v))
    (H₂ : Subgroup P) (hH₂ : ∀ p : P, p ∈ H₂ ↔ w * (p : G) * w⁻¹ ∈ Q)
    (τ₂ : Representation ℂ H₂ W₂) (E₂ : W₀ ≃ₗ[ℂ] W₂)
    (hE₂ : ∀ (h : H₂) (hq : w * ((h : P) : G) * w⁻¹ ∈ Q) (v : W₀), τ₂ h (E₂ v) = E₂ (σ ⟨_, hq⟩ v)) :
    ∃ S : Subrepresentation ((smInd Q σ).comp P.subtype),
      Nonempty ((subQuot S ⊥).Equiv (cInd H₂ τ₂)) ∧ Nonempty ((subQuot ⊤ S).Equiv (cInd H₁ τ₁)) := by
  have hQinv : ∀ q ∈ Q, ∀ g ∈ dcos Q P 1, q * g ∈ dcos Q P 1 := by
    rintro q hq _ ⟨q', hq', p, hp, rfl⟩
    exact ⟨q * q', mul_mem hq hq', p, hp, by group⟩
  have mem1 : ∀ f, resInd σ H₁ hH₁ τ₁ E₁ hE₁ f ∈ cIndSpace H₁ τ₁ := fun f =>
    resInd_mem_cInd h1 hP B₀ hB hB1 K₀ hK₀ hIw σ H₁ hH₁ τ₁ E₁ hE₁ f _ hcl subset_rfl hQinv
      (fun p _ => ⟨1, one_mem _, p, p.2, by simp⟩)
  let R : Representation.IntertwiningMap ((smInd Q σ).comp P.subtype : Representation ℂ P (smoothPart (ind Q σ))) (cInd H₁ τ₁) :=
    ⟨(resInd σ H₁ hH₁ τ₁ E₁ hE₁).codRestrict _ mem1, fun p => by
      ext f y
      show E₁ (f.1.1 ((1 : G) * (y : G) * (p : G))) = E₁ (f.1.1 ((1 : G) * ((y * p : P) : G)))
      simp [mul_assoc]⟩
  have hRs : Function.Surjective R := fun φ => by
    obtain ⟨f, hf, -⟩ := exists_lift h1 σ hσ H₁ hH₁ τ₁ E₁ hE₁ Set.univ isOpen_univ (fun _ => trivial) φ
    exact ⟨f, Subtype.ext hf⟩
  obtain ⟨S, hS, hq⟩ := GlobalTheory.T.surjective_intertwiner_quotient_equiv _ _ R hRs
  refine ⟨S, ?_, hq⟩
  have memS : ∀ f : smoothPart (ind Q σ), f ∈ S.toSubmodule ↔ ∀ p : P, f.1.1 (p : G) = 0 := by
    intro f
    rw [hS, LinearMap.mem_ker]
    constructor
    · intro h p
      have : (R f).1.1.1 p = 0 := by
        have e : R f = 0 := h
        rw [e]
        rfl
      have e2 : E₁ (f.1.1 ((1 : G) * (p : G))) = 0 := this
      rw [one_mul] at e2
      simpa using e2
    · intro h
      refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun p => ?_)))
      show E₁ (f.1.1 ((1 : G) * (p : G))) = 0
      rw [one_mul, h, map_zero]
  have vanish : ∀ f : S.toSubmodule, ∀ g ∈ dcos Q P 1, f.1.1.1 g = 0 := by
    rintro f _ ⟨q, hq, p, hp, rfl⟩
    have := (memS f.1).1 f.2 ⟨p, hp⟩
    have e := f.1.1.2 ⟨q, hq⟩ p
    rw [mul_one]
    show f.1.1.1 (((⟨q, hq⟩ : Q) : G) * p) = 0
    rw [e]
    simp only [] at this
    rw [this, map_zero]
  have mem2 : ∀ f : S.toSubmodule, resInd σ H₂ hH₂ τ₂ E₂ hE₂ f.1 ∈ cIndSpace H₂ τ₂ := fun f => by
    refine resInd_mem_cInd hw hP B₀ hB hB1 K₀ hK₀ hIw σ H₂ hH₂ τ₂ E₂ hE₂ f.1 {g | f.1.1.1 g ≠ 0}
      (GlobalTheory.T.support_induced_function_closed σ f.1) ?_ ?_ (fun p hp => hp)
    · intro g hg
      exact (hcov g).resolve_left fun h => hg (vanish f g h)
    · intro q hq g hg
      show f.1.1.1 (q * g) ≠ 0
      have e := f.1.1.2 ⟨q, hq⟩ g
      have e' : f.1.1.1 (q * g) = σ ⟨q, hq⟩ (f.1.1.1 g) := e
      rw [e']
      intro h0
      apply hg
      have := congrArg (σ (⟨q, hq⟩ : Q)⁻¹) h0
      rw [← Module.End.mul_apply, ← map_mul] at this
      simpa using this
  let O : S.toSubmodule →ₗ[ℂ] cIndSpace H₂ τ₂ :=
    ((resInd σ H₂ hH₂ τ₂ E₂ hE₂).comp S.toSubmodule.subtype).codRestrict _ mem2
  have hOinj : Function.Injective O := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    rcases hcov g with h | ⟨q, hq, p, hp, rfl⟩
    · exact vanish f g h
    · have e : (O f).1.1.1 ⟨p, hp⟩ = 0 := by rw [hf]; rfl
      have e2 : E₂ (f.1.1.1 (w * p)) = 0 := e
      have e3 : f.1.1.1 (w * p) = 0 := by simpa using e2
      have e4 : f.1.1.1 (((⟨q, hq⟩ : Q) : G) * (w * p)) = σ ⟨q, hq⟩ (f.1.1.1 (w * p)) := f.1.1.2 ⟨q, hq⟩ _
      show f.1.1.1 (q * w * p) = 0
      rw [mul_assoc, show f.1.1.1 (q * (w * p)) = _ from e4, e3, map_zero]
  have hOs : Function.Surjective O := fun φ => by
    have hY : IsOpen (dcos Q P 1)ᶜ := hcl.isOpen_compl
    obtain ⟨f, hf, hs⟩ := exists_lift hw σ hσ H₂ hH₂ τ₂ E₂ hE₂ _ hY (fun p h =>
      Set.disjoint_left.1 hdis h ⟨1, one_mem _, p, p.2, by simp⟩) φ
    have hfS : f ∈ S.toSubmodule := (memS f).2 fun p => by
      by_contra h
      obtain ⟨q, hq, hy⟩ := hs _ h
      exact hy ⟨q, hq, p, p.2, by simp⟩
    exact ⟨⟨f, hfS⟩, Subtype.ext hf⟩
  exact GlobalTheory.T.bijective_intertwiner_subrep_equiv _ _ S O ⟨hOinj, hOs⟩ (fun p f => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun y => ?_)))
    show E₂ (f.1.1.1 (w * (y : G) * (p : G))) = E₂ (f.1.1.1 (w * ((y * p : P) : G)))
    simp [mul_assoc])

end AbstractL

section ConcreteL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbit_cover {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) (g : GL (Fin (i + t + 1)) k) :
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ∨
      g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  by_cases hy : ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0
  · exact Or.inl ((GlobalTheory.T.closed_double_coset_criterion k h ht g).2 hy)
  · push_neg at hy
    exact Or.inr ((GlobalTheory.T.open_double_coset_criterion k h ht g).2 hy)

theorem isClosed_orbit {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    IsClosed (dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1) := by
  have e : dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 = ⋂ a : Fin (i + 1),
      {g : GL (Fin (i + t + 1)) k | ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0} := by
    ext g
    rw [Set.mem_iInter]
    exact GlobalTheory.T.closed_double_coset_criterion k h ht g
  rw [e]
  refine isClosed_iInter fun a => isClosed_eq ?_ continuous_const
  exact (Units.continuous_coe_inv (M := Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)).matrix_elem _ _

theorem orbits_disjoint {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    Disjoint (dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1)
      (dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h)) := by
  refine Set.disjoint_left.2 fun g h1 h2 => ?_
  obtain ⟨a, ha⟩ := (GlobalTheory.T.open_double_coset_criterion k h ht g).1 h2
  exact ha ((GlobalTheory.T.closed_double_coset_criterion k h ht g).1 h1 a)

end ConcreteL

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cast_prod {r t N : ℕ} (h : r + t = N) (π₁ : GRep k r) (π₂ : GRep k t) :
    (π₁.prod π₂).cast h = (⟨_, prod2 h π₁.ρ π₂.ρ⟩ : GRep k N) := by
  subst h; rfl

theorem mcast_prodGPn {m j n : ℕ} (h : m + j = n) (ρ : GRep k m) (τ : MRep k j) :
    mcast h (prodGPn ρ τ) = (⟨_, cInd (HGPg k h)
      ((extTensor (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw τ (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h))⟩ : MRep k n) := by
  subst h; rfl

theorem core0 (i j : ℕ) (h₀ : (i + 1) + (j + 1) = i + (j + 1) + 1) (h₁ : (i + 1) + j = i + (j + 1))
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) :
    ∃ S : Subrepresentation ((smInd (parab k (two (stdSum h₀))) (sQ h₀ π₁ π₂)).comp (Mir k (i + (j + 1))).subtype),
      Nonempty ((subQuot S ⊥).Equiv (cInd (HPG k i (j + 1))
        ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))))) ∧
      Nonempty ((subQuot ⊤ S).Equiv (cInd (HGPg k h₁)
        ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h₁)))) := by
  haveI := GlobalTheory.LocRankBig.nonarchimedeanGroup_GL (k := k) (i + (j + 1) + 1)
  have ho := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin (i + (j + 1) + 1))).mem_nhds (one_mem _)
  have ht : 0 < j + 1 := by omega
  refine two_orbits (Q := parab k (two (stdSum h₀))) (P := Mir k (i + (j + 1))) (w := wGL k h₀)
    (GlobalTheory.T.local_section_closed_cell k h₀ ht) (GlobalTheory.T.local_section_open_cell k h₀) (GlobalTheory.T.mirabolic_closed k _)
    _ GlobalTheory.SplitFlip.isCompact_KO ho
    _ GlobalTheory.SplitFlip.isCompact_KO (fun g => ?_)
    (orbit_cover k h₀ ht) (isClosed_orbit k h₀ ht) (orbits_disjoint k h₀ ht)
    (sQ h₀ π₁ π₂) (GlobalTheory.T.smooth_parabolic_induction_product h₀ _ _ s₁ s₂)
    (HGPg k h₁) (fun p => ?_) _ (tE V W) (GlobalTheory.T.closed_cell_inducing_character h₁ π₁ π₂)
    (HPG k i (j + 1)) (GlobalTheory.T.mem_HPG_iff_conjugate_parabolic k h₀) _ (tE V W) (GlobalTheory.T.open_cell_inducing_character h₀ π₁ π₂)
  · obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (stdSum h₀) g
    exact ⟨p, p.2, c, hc, e⟩
  · rw [one_mul, inv_one, mul_one]
    rfl

theorem core (i j : ℕ) (h₀ : (i + 1) + (j + 1) = i + (j + 1) + 1) (h₁ : (i + 1) + j = i + (j + 1))
    (π₁ : GRep k (i + 1)) (π₂ : GRep k (j + 1)) (s₁ : IsSmooth π₁.ρ) (s₂ : IsSmooth π₂.ρ) :
    MExt (prodPGn (gres π₁) π₂) (gres (⟨_, prod2 h₀ π₁.ρ π₂.ρ⟩ : GRep k (i + (j + 1) + 1)))
      (⟨_, cInd (HGPg k h₁)
      ((extTensor (π₁.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres π₂) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h₁))⟩) := by
  obtain ⟨V, ρ₁⟩ := π₁
  obtain ⟨W, ρ₂⟩ := π₂
  have c0 := core0 i j h₀ h₁ ρ₁ ρ₂ s₁ s₂
  unfold MExt
  exact c0

end Main

theorem resSeq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  intro k _ _ _ _ i j n hn π₁ π₂ s₁ s₂
  subst hn
  have h₀ : (i + 1) + (j + 1) = i + (j + 1) + 1 := by omega
  have h₁ : (i + 1) + j = i + (j + 1) := by omega
  have c := core i j h₀ h₁ π₁ π₂ s₁ s₂
  rw [cast_prod, mcast_prodGPn]
  exact c

end GlobalTheory.CompanionTheory.BZRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHoldsStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_sequence_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.resSeq | exact GlobalTheory.CompanionTheory.BZRes.resSeq | (intros; apply GlobalTheory.CompanionTheory.BZRes.resSeq <;> assumption)
end

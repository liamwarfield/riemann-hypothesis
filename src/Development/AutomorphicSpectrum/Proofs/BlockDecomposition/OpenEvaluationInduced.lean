module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviAction
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (x : τ.V) : (phiN ψ τ).V :=
  (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ x

theorem phiN_cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (a : Mir k i) (x : τ.V) :
    (phiN ψ τ).ρ a (cls ψ τ x) = ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) • cls ψ τ (τ.ρ (sEmb k i a) x) :=
  twist_apply _ _ _ _

theorem dpowM_half (i : ℕ) (a : Mir k i) :
    ((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) = 1 := by
  have h : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = dpow (i + 1) (1 / 2) * dpow (i + 1) (-1 / 2) :=
    GlobalTheory.CompanionTheory.LeibPhi.dpow_add k (i + 1) _ _
  have h0 : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = 1 := by
    rw [show ((1 / 2 + -1 / 2 : ℝ)) = 0 by norm_num]
    ext g
    simp [dpow, detChar, absPow]
  have h1 := congrArg (fun f => ((f (a : GL (Fin (i + 1)) k) : ℂˣ) : ℂ)) (h.symm.trans h0)
  simpa [dpowM] using h1

theorem dpow_step (i t : ℕ) (w : GL (Fin (t + 1)) k) :
    ((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) =
      ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) := by
  have e : (-((i + 1 + 1 : ℕ) : ℝ) / 2) = -1 / 2 + (-((i + 1 : ℕ) : ℝ) / 2) := by
    push_cast; ring
  rw [e, GlobalTheory.CompanionTheory.LeibPhi.dpow_add]
  simp

theorem smul_tmul_scal {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X) (q : Y)
    (c d e f f' g : ℂ) (h : c * d = e * (f * f' * g)) :
    (c • p) ⊗ₜ[ℂ] (d • q) = e • ((f • f' • p) ⊗ₜ[ℂ] (g • q)) := by
  rw [smul_smul f f' p]
  generalize f * f' = f at h
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
    smul_smul, smul_smul, smul_smul, mul_comm d c, h, mul_comm f g, mul_assoc]

theorem intertwine (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V) :
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  let L : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V := (qO τ σ ψ) ∘ₗ
    (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w))
  let R : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      ((extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w)) ∘ₗ (qO τ σ ψ))
  have hLR : L = R := by
    refine TensorProduct.ext' fun x y => ?_
    have hl : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • τ.ρ (sEmb k i a) x :=
      (twist_apply _ _ _ _).trans (by
        rw [show sEmb k i a = (levi k (i + 1)).comp (Mir k i).subtype a from rfl, GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_levi]
        rfl)
    have hr : ∀ s : ℝ, (σ.tw s).ρ w y = ((dpow (t + 1) s w : ℂˣ) : ℂ) • σ.ρ w y := fun s => twist_apply _ _ _ _
    have hm : (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • (phiN ψ τ).ρ a (cls ψ τ x) := twist_apply _ _ _ _
    have hc : ∀ (c : ℂ) (z : τ.V), cls ψ τ (c • z) = c • cls ψ τ z := fun c z => map_smul _ c z
    have eL : L (x ⊗ₜ[ℂ] y) = cls ψ τ ((mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x) ⊗ₜ[ℂ]
        (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ w y := rfl
    have eR : R (x ⊗ₜ[ℂ] y) = (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
        ((mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) ⊗ₜ[ℂ] (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ w y) := rfl
    rw [eL, eR, hl, hm, phiN_cls, hr, hr, hc, dpow_step]
    have hh := dpowM_half i a
    refine smul_tmul_scal (X := (phiN ψ τ).V) (Y := σ.V) _ _ _ _ _ _ _ _ ?_
    linear_combination (-(((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ))) * hh
  exact LinearMap.congr_fun hLR v

end GlobalTheory.CompanionTheory.BZPhiPG.Coinv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviActionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_coinvariant_levi_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine | exact GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniqueness
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniqueness
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Stab

section Perm

theorem piPerm_true_val (i t : ℕ) (x : Fin (t + 1)) (hx : i + x.val < (i + 1) + t + 1) :
    (piPerm i t ⟨i + x.val, hx⟩).val = i + 1 + x.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨i + x.val, hx⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨true, x⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]

theorem piPerm_false_val (i t : ℕ) (y : Fin i) (hy : y.val < (i + 1) + t + 1) :
    (piPerm i t ⟨y.val, hy⟩).val = y.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨y.val, hy⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨false, Fin.castSucc y⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  all_goals simp

end Perm

section Ent

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_symm_entry {a b : ℕ} (e : a = b) (r : Mir k b) (x y : ℕ) (hx : x < a + 1) (hy : y < a + 1)
    (hx' : x < b + 1) (hy' : y < b + 1) :
    (((castM k e).symm r : Mir k a) : GL (Fin (a + 1)) k).val ⟨x, hx⟩ ⟨y, hy⟩ =
      (r : GL (Fin (b + 1)) k).val ⟨x, hx'⟩ ⟨y, hy'⟩ := by
  subst e
  rfl

theorem mirProj_dEmb (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k _ (dEmb k i t d) = 1 := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem
  exact Subgroup.mem_subgroupOf.mpr
    (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem mirProj_wEl (i t : ℕ) : mirabolicProjection k _ (wEl k i t) = wGL k i t :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem mirProj_sEmb (n : ℕ) (r : Mir k n) : mirabolicProjection k _ (sEmb k n r) = (r : GL (Fin (n + 1)) k) :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem wGL_mul_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    ((wGL k i t).val * M) (piPerm i t a) b = M a b := by
  show (Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹ * M) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t a) b = M a b
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  simp

theorem mul_wGL_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    (M * (wGL k i t).val) a b = M a (piPerm i t b) := by
  show (M * Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹) a b = M a (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t b)
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  simp [Equiv.Perm.inv_def]

theorem entry_eq (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y =
      (h : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc (piPerm i t x)) (Fin.castSucc (piPerm i t y)) := by
  have key := congrArg (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t + 1)) e
  simp only [map_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_dEmb, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_wEl,
    GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_sEmb, _root_.one_mul, _root_.mul_one] at key
  have key' := congrArg (fun g : GL (Fin ((i + 1) + t + 1)) k =>
    (g : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x) y) key
  simp only [Units.val_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.wGL_mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mul_wGL_apply] at key'
  exact key'

theorem entry_zero (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (hh : h ∈ HPG k (i + 1) (t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) (hx : i < (piPerm i t x).val) (hy : (piPerm i t y).val ≤ i) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y = 0 := by
  rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_eq i t r d d' h e x y]
  have hc : (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ) < i + 1 := by omega
  have hz := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh
    (Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x))
    (by rw [Fin.coe_castSucc]; exact hx)
    (by rw [Fin.coe_castSucc]; exact Nat.ne_of_lt (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x).isLt)
    ⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩
  have e₂ : (Fin.castLE (by omega) (⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩ : Fin (i + 1)) :
      Fin ((i + 1) + t + 1 + 1)) = Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y) := Fin.ext rfl
  rw [e₂] at hz
  exact hz

end Ent

theorem mem_of_double_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  intro k _ _ _ _ i t r d d' h hh e
  have hab : i + (t + 1) = (i + 1) + t := by omega
  refine ⟨(GlobalTheory.CompanionTheory.BZPhiPG.castM k hab).symm r, ?_, MulEquiv.apply_symm_apply _ _⟩
  apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.mem_HPG_of
  · intro x y
    have hxl := x.isLt
    have hyl := y.isLt
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) y.val (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_false_val]; omega)
  · intro x
    have hxl := x.isLt
    have hcol : (Fin.last (i + (t + 1)) : Fin (i + (t + 1) + 1)) = ⟨(i + 1) + t, by omega⟩ :=
      Fin.ext (by rw [Fin.val_last, Fin.val_mk]; omega)
    rw [hcol]
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) ((i + 1) + t) (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (GlobalTheory.CompanionTheory.BZPhiPG.Cells.piPerm_last_val i t).le

end GlobalTheory.CompanionTheory.BZPhiPG.Stab

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniquenessStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_double_coset_uniqueness : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset | exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFactorizationCharacterTrivial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFactorizationCharacterTrivial
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Conj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unip_cc (n : ℕ) (v : Fin n → k) (r c : Fin n) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.castSucc r) (Fin.castSucc c) = (1 : Matrix (Fin n) (Fin n) k) r c := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem unip_lc (n : ℕ) (v : Fin n → k) (c : Fin n) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.last n) (Fin.castSucc c) = 0 := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem unip_ll (n : ℕ) (v : Fin n → k) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.last n) (Fin.last n) = 1 := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat]

theorem unip_mul_glEmb (n : ℕ) (g : GL (Fin n) k) (a b c : Fin n → k)
    (h : ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec a = b + c) :
    unip k n (Multiplicative.ofAdd a) * glEmb k n g =
      glEmb k n g * unip k n (Multiplicative.ofAdd b) * unip k n (Multiplicative.ofAdd c) := by
  rw [mul_assoc, ← map_mul, ← ofAdd_add, ← h, glEmb_mul_unip']
  simp only [toAdd_ofAdd]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem castM_val {a b : ℕ} (h : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k h m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst h
  rfl

def eps (i t : ℕ) : (Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) ≃ Fin ((i + 1) + t + 1) :=
  (ePG i (t + 1)).trans (finCongr (by omega))

theorem piPerm_eps (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (eps i t s) = eGP (i + 1) t s := by
  simp [piPerm, eps]

theorem blockIndex_true (i t : ℕ) (y : Fin (t + 1)) : eGP (i + 1) t ⟨true, y⟩ = Fin.natAdd (i + 1) y :=
  Fin.ext (by simp [eGP, two, stdSum])

theorem blockIndex_false (i t : ℕ) (a : Fin (i + 1)) : eGP (i + 1) t ⟨false, a⟩ = Fin.castAdd (t + 1) a :=
  Fin.ext (by simp [eGP, two, stdSum])

def gEl (i t : ℕ) (m : Mir k (i + (t + 1))) : GL (Fin ((i + 1) + t + 1)) k :=
  wGL k i t * ((castM k (by omega) m : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹

theorem gEl_inv (i t : ℕ) (m : Mir k (i + (t + 1))) : (gEl i t m)⁻¹ = gEl i t m⁻¹ := by
  simp [gEl, mul_assoc, map_inv]

theorem wGL_conj_mulVec (i t : ℕ) (M : GL (Fin ((i + 1) + t + 1)) k) (u : Fin ((i + 1) + t + 1) → k)
    (a : Fin ((i + 1) + t + 1)) :
    ((wGL k i t * M * (wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val.mulVec u) (piPerm i t a) =
      (M.val.mulVec (u ∘ piPerm i t)) a := by
  show ((Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * M.val * Equiv.Perm.permMatrix k (piPerm i t)).mulVec u) (piPerm i t a) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec]
  simp [Function.comp]

theorem gEl_mulVec (i t : ℕ) (m : Mir k (i + (t + 1))) (u : Fin ((i + 1) + t + 1) → k)
    (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    ((gEl i t m).val.mulVec u) (eGP (i + 1) t s) =
      (∑ x : Fin (i + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨false, x⟩) *
        u (eGP (i + 1) t ⟨false, x⟩)) +
      ∑ y : Fin (t + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨true, y⟩) *
        u (eGP (i + 1) t ⟨true, y⟩) := by
  rw [← piPerm_eps, gEl, wGL_conj_mulVec]
  show (∑ b : Fin ((i + 1) + t + 1), (_ : k)) = _
  rw [← Equiv.sum_comp (eps i t), Fintype.sum_sigma, Fintype.sum_bool, add_comm]
  simp only [Function.comp, piPerm_eps]
  congr 1
  all_goals exact Finset.sum_congr rfl fun x _ => by rw [castM_val]; rfl

theorem ePG_true_ne_last (i t : ℕ) (y : Fin (t + 1)) : ePG i (t + 1) ⟨true, y⟩ ≠ Fin.last (i + (t + 1)) := by
  intro e
  have h1 := congrArg Fin.val e
  rw [Cells.ePG_true_val] at h1
  have := y.2
  simp only [Fin.val_last] at h1
  change y.1 < t + 1 at this
  omega

theorem ePG_false_castSucc' (i t : ℕ) (y : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc y⟩ = Fin.castSucc (Fin.castAdd (t + 1) y) :=
  Fin.ext (by simpa using Cells.ePG_false_val (i + 1) (t + 1) y)

theorem ePG_true' (i t : ℕ) (y : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, y⟩ = Fin.castSucc (Fin.natAdd (i + 1) y) :=
  Fin.ext (by simpa using Cells.ePG_true_val (i + 1) (t + 1) y)

abbrev uD (i t : ℕ) (d : Fin (t + 1) → k) : Fin ((i + 1) + t + 1) → k := @Fin.append (i + 1) (t + 1) k 0 d

theorem gEl_uD (i t : ℕ) (m : Mir k (i + (t + 1))) (d : Fin (t + 1) → k)
    (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    ((gEl i t m).val.mulVec (uD i t d)) (eGP (i + 1) t s) =
      ∑ y : Fin (t + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨true, y⟩) * d y := by
  rw [gEl_mulVec, Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [blockIndex_true]
    congr 1
    exact Fin.append_right _ _ y
  · intro x _
    rw [blockIndex_false]
    have : uD i t d (Fin.castAdd (t + 1) x) = 0 := Fin.append_left _ _ x
    rw [this, mul_zero]

theorem vec_last (i t : ℕ) (m : Mir k (i + (t + 1))) (d : Fin (t + 1) → k) :
    ((gEl i t m).val.mulVec (uD i t d)) (Fin.castAdd (t + 1) (Fin.last i)) = 0 := by
  have h := gEl_uD i t m d ⟨false, Fin.last i⟩
  rw [blockIndex_false, ePG_false_last] at h
  refine h.trans (Finset.sum_eq_zero fun y _ => ?_)
  have hm := (mem_Mir_iff k (m : GL (Fin (i + (t + 1) + 1)) k)).1 m.2
  rw [hm]
  simp [eLast, Pi.single_apply, ePG_true_ne_last]

theorem vec_true (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k) (y : Fin (t + 1)) :
    ((gEl i t (h : Mir k (i + (t + 1)))⁻¹).val.mulVec (uD i t d)) (Fin.natAdd (i + 1) y) =
      ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) y := by
  have h1 := gEl_uD i t (h : Mir k (i + (t + 1)))⁻¹ d ⟨true, y⟩
  rw [blockIndex_true] at h1
  refine h1.trans ?_
  have e : ((pgProj k i (t + 1) h).2)⁻¹ = (pgProj k i (t + 1) h⁻¹).2 := by
    rw [map_inv]; rfl
  rw [e]
  rfl

def cEl (i t : ℕ) (x : Fin (i + 1) → k) : Mir k ((i + 1) + (t + 1)) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k))), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem cEl_mem (i t : ℕ) (x : Fin (i + 1) → k) : cEl i t x ∈ HPG k (i + 1) (t + 1) := by
  refine Cells.mem_HPG_of (I := i + 1) (T := t + 1) (cEl i t x) ?_ ?_
  · intro a b
    refine Cells.unip_castSucc_castSucc _ _ _ _ ?_
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega
  · intro a
    refine (unip_apply_castSucc_last k _ _ _).trans ?_
    show Fin.append x (0 : Fin (t + 1) → k) (Fin.natAdd (i + 1) a) = 0
    simp

def uEl (i : ℕ) (x : Fin (i + 1) → k) : MirUin k (i + 1) :=
  ⟨⟨unip k (i + 1) (Multiplicative.ofAdd x), MirU_le_Mir k _ ⟨_, rfl⟩⟩, ⟨_, rfl⟩⟩

theorem pgProj_cEl (i t : ℕ) (x : Fin (i + 1) → k) :
    pgProj k (i + 1) (t + 1) ⟨cEl i t x, cEl_mem i t x⟩ = ((uEl i x : Mir k (i + 1)), 1) := by
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k)))).val
      (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
      (unip k (i + 1) (Multiplicative.ofAdd x)).val a b
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, unip_ll, unip_ll]
      | cast b => rw [ePG_false_castSucc', unip_lc, unip_lc]
    | cast a =>
      rw [ePG_false_castSucc']
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, unip_apply_castSucc_last, unip_apply_castSucc_last]
        simp
      | cast b =>
        rw [ePG_false_castSucc', unip_cc, unip_cc]
        simp [Matrix.one_apply]
  · apply Units.ext
    ext a b
    show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k)))).val
      (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
    rw [ePG_true', ePG_true', unip_cc]
    simp [Matrix.one_apply]

theorem conj_eq_levi (i t : ℕ) (m : Mir k (i + (t + 1))) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) * (wEl k i t)⁻¹ = levi k _ (gEl i t m) := by
  rw [gEl, map_mul, map_mul, map_inv]
  rfl

theorem dEmb_conj :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k),
  ∃ (c : HPG k (i + 1) (t + 1)) (u : MirUin k (i + 1)),
    pgProj k (i + 1) (t + 1) c = ((u : Mir k (i + 1)), 1) ∧ mirChar k ψ i u = 1 ∧
    dEmb k i t d * (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) =
      (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) * (c : Mir k ((i + 1) + (t + 1))) *
        dEmb k i t ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := by
  intro k _ _ _ _ ψ i t h d
  let v : Fin ((i + 1) + t + 1) → k := (gEl i t (h : Mir k (i + (t + 1)))⁻¹).val.mulVec (uD i t d)
  let x : Fin (i + 1) → k := fun a => v (Fin.castAdd (t + 1) a)
  refine ⟨⟨cEl i t x, cEl_mem i t x⟩, uEl i x, pgProj_cEl i t x, ?_, ?_⟩
  · rw [mirChar_eq k ψ i (uEl i x) (Multiplicative.ofAdd x) rfl]
    have hx : x (Fin.last i) = 0 := vec_last i t _ d
    simp [hx]
  · rw [conj_eq_levi]
    apply Subtype.ext
    refine unip_mul_glEmb ((i + 1) + t + 1) (gEl i t (h : Mir k (i + (t + 1)))) _ _ _ ?_
    rw [gEl_inv]
    have key : ∀ z : Fin ((i + 1) + (t + 1)), v z = @Fin.append (i + 1) (t + 1) k x 0 z +
        @Fin.append (i + 1) (t + 1) k 0 ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) z := by
      intro z
      induction z using Fin.addCases with
      | left a => rw [Fin.append_left, Fin.append_left, Pi.zero_apply, add_zero]
      | right y =>
        rw [Fin.append_right, Fin.append_right, Pi.zero_apply, zero_add]
        exact vec_true i t h d y
    exact funext key

end GlobalTheory.CompanionTheory.BZPhiPG.Conj

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFactorizationCharacterTrivialStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_factorization_character_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k),
  ∃ (c : HPG k (i + 1) (t + 1)) (u : MirUin k (i + 1)),
    pgProj k (i + 1) (t + 1) c = ((u : Mir k (i + 1)), 1) ∧ mirChar k ψ i u = 1 ∧
    dEmb k i t d * (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) =
      (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) * (c : Mir k ((i + 1) + (t + 1))) *
        dEmb k i t ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj | exact GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulus
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulus
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Scale

theorem smInt_subst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
    IsLocallyConstant F → HasCompactSupport F →
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
      ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  intro k _ _ _ _ n W _ _ w F l c
  exact smInt_mulVec k n W w F l c

end GlobalTheory.CompanionTheory.BZPhiPG.Scale

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulusStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mulVec_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
  IsLocallyConstant F → HasCompactSupport F →
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
    ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportCompactModParabolicOffClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportCompactModParabolicOffClosed
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.SuppOff

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

theorem isClosed_support (H : Subgroup G) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    IsClosed {c : G | f.1.1 c ≠ 0} := by
  have hopen : IsOpen {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1} := f.2
  have htrans : ∀ g x : G, GlobalTheory.PRep.ind H σ g f.1 = f.1 → f.1.1 (x * g) = f.1.1 x := by
    intro g x hg
    exact congrArg (fun φ : GlobalTheory.PRep.indSpace H σ => (φ : G → W) x) hg
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro c hc
  have hc0 : f.1.1 c = 0 := by simpa using hc
  have h1 : c⁻¹ * c ∈ {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1} := by
    show GlobalTheory.PRep.ind H σ (c⁻¹ * c) f.1 = f.1
    rw [inv_mul_cancel, map_one]
    rfl
  refine Filter.mem_of_superset
    ((continuous_const_mul c⁻¹).continuousAt.preimage_mem_nhds (hopen.mem_nhds h1)) ?_
  intro x hx
  have hx' : GlobalTheory.PRep.ind H σ (c⁻¹ * x) f.1 = f.1 := hx
  have hfx : f.1.1 x = 0 := by
    calc f.1.1 x = f.1.1 (c * (c⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = f.1.1 c := htrans _ _ hx'
      _ = 0 := hc0
  simpa using hfx

theorem exists_compact_off (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) (T : Set G)
    (hf : ∀ x ∈ T, (f : smoothPart (ind H σ)).1.1 x = 0) :
    ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧
      ∀ g, (f : smoothPart (ind H σ)).1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c := by
  have key : ∀ F : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ),
      (∃ C : Set G, IsCompact C ∧ ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c) →
      (∀ x ∈ T, F.1.1 x = 0) →
      ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧
        ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c := by
    rintro F ⟨C, hC, hsupp⟩ hF
    have hequiv : ∀ (h : H) (g : G), F.1.1 (h * g) = σ h (F.1.1 g) := F.1.2
    refine ⟨C ∩ {c | F.1.1 c ≠ 0}, hC.inter_right (GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.isClosed_support H σ F), ?_, ?_⟩
    · rintro c ⟨-, hc⟩ hcT
      exact hc (hF c hcT)
    · intro g hg
      obtain ⟨h, hH, c, hcC, rfl⟩ := hsupp g hg
      refine ⟨h, hH, c, ⟨hcC, ?_⟩, rfl⟩
      intro hc0
      apply hg
      have e : F.1.1 (h * c) = σ ⟨h, hH⟩ (F.1.1 c) := hequiv ⟨h, hH⟩ c
      rw [e]
      have hc0' : F.1.1 c = 0 := by simpa using hc0
      rw [hc0', map_zero]
  exact key _ f.2 hf

end Abstract

theorem exists_compact_off_Cl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k ((i + 1) + t + 1)), IsCompact C ∧ (∀ c ∈ C, c ∉ Cl k i t) ∧
      ∀ g, evX f g ≠ 0 → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ c ∈ C, g = h * c :=
  GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off (GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1))
    (GlobalTheory.CompanionTheory.BZPhiPG.sigX τ σ) f _ hf

end GlobalTheory.CompanionTheory.BZPhiPG.SuppOff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportCompactModParabolicOffClosedStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_compact_mod_parabolic_off_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ C : Set (Mir k ((i + 1) + t + 1)), IsCompact C ∧ (∀ c ∈ C, c ∉ Cl k i t) ∧
    ∀ g, evX f g ≠ 0 → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ c ∈ C, g = h * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl | exact GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOne
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.DetPG

def sumSig (a b : Type) : a ⊕ b ≃ Σ x, Two a b x where
  toFun y := match y with
    | Sum.inl i => ⟨false, i⟩
    | Sum.inr j => ⟨true, j⟩
  invFun x := match x with
    | ⟨false, i⟩ => Sum.inl i
    | ⟨true, j⟩ => Sum.inr j
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_hpg (i T : ℕ) (h : HPG k i T) :
    GeneralLinearGroup.det ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
      GeneralLinearGroup.det ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
        GeneralLinearGroup.det (pgProj k i T h).2 := by
  ext
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_det_apply]
  let φ : Fin (i + 1) ⊕ Fin T ≃ Fin (i + T + 1) := (sumSig _ _).trans (ePG i T)
  have hz : ∀ (b : Fin T) (a : Fin (i + 1)),
      (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) : Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k)
        (ePG i T ⟨true, b⟩) (ePG i T ⟨false, a⟩) = 0 := fun b a =>
    mem_parab_iff.1 h.2 true false b a (by decide)
  have hb : (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
        Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k).submatrix φ φ =
      fromBlocks (((pgProj k i T h).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)
        (Matrix.of fun a b => (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
          Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k) (φ (Sum.inl a)) (φ (Sum.inr b))) 0
        ((pgProj k i T h).2 : Matrix (Fin T) (Fin T) k) := by
    ext x y
    rcases x with a | b <;> rcases y with c | d
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) false a c).symm
    · rfl
    · exact hz b c
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) true b d).symm
  rw [← det_submatrix_equiv_self φ, hb]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem dpowM_hpg (i T : ℕ) (s : ℝ) (h : HPG k i T) :
    dpowM (i + T) s (h : Mir k (i + T)) = dpowM i s (pgProj k i T h).1 * dpow T s (pgProj k i T h).2 := by
  show detChar (Fin (i + T + 1)) (absPow k (s : ℂ)) ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
    detChar (Fin (i + 1)) (absPow k (s : ℂ)) ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
      detChar (Fin T) (absPow k (s : ℂ)) (pgProj k i T h).2
  rw [detChar_apply, detChar_apply, detChar_apply, det_hpg, map_mul]

theorem dpow_add' (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem dpow_zero' (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow, absPow_zero]

theorem dpowM_add' (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n s * dpowM n t := by
  ext g
  simp [dpowM, dpow_add']

theorem dpowM_zero' (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero']

theorem complex_units_mul_eq_one_of_mul_eq_one (A B X Y Z : ℂˣ) (h₁ : A * B = 1) (h₂ : X * Y * Z = 1) : A * X * Y * (B * Z) = 1 := by
  have : A * X * Y * (B * Z) = (A * B) * (X * Y * Z) := by ac_rfl
  rw [this, h₁, h₂, one_mul]

theorem exponents_cancel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (h : HPG k i (t + 1)) :
    ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
      (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  have e1 : dpowM (k := k) i (-1 / 2) (pgProj k i (t + 1) h).1 * dpowM i (1 / 2) (pgProj k i (t + 1) h).1 = 1 := by
    have : dpowM (k := k) i (-1 / 2 + 1 / 2) = dpowM i (-1 / 2) * dpowM i (1 / 2) := dpowM_add' _ _ _
    rw [show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpowM_zero'] at this
    rw [← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e2 : dpow (k := k) (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 = 1 := by
    have : dpow (k := k) (t + 1) (-1 / 2 + 1 + -1 / 2) = dpow (t + 1) (-1 / 2) * dpow (t + 1) 1 * dpow (t + 1) (-1 / 2) := by
      rw [dpow_add', dpow_add']
    rw [show (-1 / 2 + 1 + -1 / 2 : ℝ) = 0 by norm_num, dpow_zero'] at this
    rw [← MonoidHom.mul_apply, ← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e : dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      (dpowM i (1 / 2) (pgProj k i (t + 1) h).1 * dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2) = 1 := by
    rw [dpowM_hpg]
    exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ e1 e2
  have := congrArg (Units.val) e
  simpa only [Units.val_mul, Units.val_one] using this

end GlobalTheory.CompanionTheory.BZPhiPG.DetPG

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOneStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_characters_product_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
    (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel | exact GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInduced
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.MemO

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_cont {a b : ℕ} (e : a = b) : Continuous (castM k e) ∧ Continuous (castM k e).symm := by
  subst e
  exact ⟨continuous_id, continuous_id⟩

theorem exists_compact_cell (i t : ℕ) (C : Set (Mir k ((i + 1) + t + 1))) (hC : IsCompact C) (hCl : ∀ c ∈ C, c ∉ Cl k i t) :
    ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ C, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k), ∃ m ∈ N,
      c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m := by
  refine hC.induction_on (p := fun S => ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ S, ∃ h ∈ HPG k (i + 1) (t + 1),
    ∃ (d : Fin (t + 1) → k), ∃ m ∈ N, c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, by simp⟩
  · rintro s t' hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun c hc => h c (hst hc)⟩
  · rintro s t' ⟨N, hN, h⟩ ⟨N', hN', h'⟩
    refine ⟨N ∪ N', hN.union hN', ?_⟩
    rintro c (hc | hc)
    · obtain ⟨a, ha, d, m, hm, e⟩ := h c hc
      exact ⟨a, ha, d, m, Or.inl hm, e⟩
    · obtain ⟨a, ha, d, m, hm, e⟩ := h' c hc
      exact ⟨a, ha, d, m, Or.inr hm, e⟩
  · intro x hx
    obtain ⟨V, hV, μ, hμ, hs⟩ := GlobalTheory.T.exists_continuous_local_section_of_not_mem_Cl k i t x (hCl x hx)
    obtain ⟨V', hV', hcl, hsub⟩ := exists_mem_nhds_isClosed_subset hV
    refine ⟨C ∩ V', Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV'), μ '' (C ∩ V'), ?_, ?_⟩
    · exact (hC.inter_right hcl).image_of_continuousOn (hμ.mono (fun y hy => hsub hy.2))
    · intro c hc
      obtain ⟨a, ha, d, e⟩ := hs c (hsub hc.2)
      exact ⟨a, ha, d, μ c, ⟨c, hc, rfl⟩, e⟩
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_fin (n : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin n → k) (borel _) _ (muD k n) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem smInt_lin {n : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') {F : (Fin n → k) → W} (l : IsLocallyConstant F) (c : HasCompactSupport F) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (T ∘ F) = T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI := muD_fin (k := k) n
  exact GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear _ T l c

theorem smInt_zero' {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun _ => (0 : W)) = 0 := by
  unfold GlobalTheory.CompanionTheory.Rodier.smInt
  refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have : (fun _ : Fin n → k => (0 : W)) ⁻¹' {v} = ∅ := by
      ext x
      simp [Ne.symm hv]
    rw [this]
    simp

variable {i t : ℕ}

theorem eO_equiv (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (h : HPG k i (t + 1)) (m : Mir k (i + (t + 1))) :
    eO ψ f ((h : Mir k (i + (t + 1))) * m) = sigO τ σ ψ h (eO ψ f m) := by
  obtain ⟨hη, hproj⟩ := GlobalTheory.T.weyl_conj_parabolic_proj k i t h
  set a' := (pgProj k i (t + 1) h).1 with ha'
  set w' := (pgProj k i (t + 1) h).2 with hw'
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) with hy
  set η := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ with hηd
  have e1 : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) ((h : Mir k (i + (t + 1))) * m)) = η * y := by
    rw [map_mul, map_mul, hηd, hy]
    group
  let Tm : (phiN ψ τ).V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a', w')
  let sc : ℂ := ((dpowM i (1 / 2) a' : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w' : ℂˣ) : ℂ)
  let G : (Fin (t + 1) → k) → (phiN ψ τ).V ⊗[ℂ] σ.V := fun d => qO τ σ ψ (evX f (dEmb k i t d * y))
  have hpt : ∀ d, qO τ σ ψ (evX f (dEmb k i t d * (η * y))) = (sc • Tm) (G ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
    intro d
    obtain ⟨c, u, hc, hu, he⟩ := GlobalTheory.T.unipotent_factorization_character_trivial k ψ i t h d
    have e2 : dEmb k i t d * (η * y) =
        ((⟨η, hη⟩ : HPG k (i + 1) (t + 1)) : Mir k ((i + 1) + (t + 1))) * ((c : Mir k ((i + 1) + (t + 1))) *
          (dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) * y)) := by
      have he' : dEmb k i t d * η = η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := he
      calc dEmb k i t d * (η * y) = (dEmb k i t d * η) * y := (mul_assoc _ _ _).symm
        _ = (η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) * y := by rw [he']
        _ = _ := by rw [mul_assoc, mul_assoc]
    have e3 : ∀ (hh : HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + (t + 1))),
        evX f ((hh : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ hh (evX f x) := fun hh x =>
      (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 hh x
    rw [e2, e3, e3]
    have e4 : ∀ (hh : HPG k (i + 1) (t + 1)) (v), sigX τ σ hh v =
        extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) hh) v := fun _ _ => rfl
    rw [e4, hproj, GlobalTheory.T.twisted_coinvariant_levi_action, e4, hc, GlobalTheory.T.coinvariant_unipotent_character_trivial k i t ψ τ σ u hu]
    rfl
  have hl := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y
  have hl2 := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f (η * y)
  have hG : IsLocallyConstant G := hl.1.comp (qO τ σ ψ)
  have hGc : HasCompactSupport G := hl.2.comp_left (map_zero (qO τ σ ψ))
  have key : qO τ σ ψ (intO f (η * y)) =
      ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) • (sc • Tm) (qO τ σ ψ (intO f y)) := by
    have s1 : qO τ σ ψ (intO f (η * y)) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
        (fun d => ((sc • Tm) ∘ G) ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl2.1 hl2.2]
      congr 1
      funext d
      exact hpt d
    have s2 : qO τ σ ψ (intO f y) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) G := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl.1 hl.2]
      rfl
    rw [s1, GlobalTheory.T.integral_mulVec_change_modulus k (t + 1) _ w' ((sc • Tm) ∘ G) (hG.comp _) (hGc.comp_left (map_zero _)),
      smInt_lin (sc • Tm) hG hGc, s2]
  have e5 : sigO τ σ ψ h = Tm := rfl
  unfold eO
  rw [e1, ← hy, key, e5, map_smul, map_mul]
  have h6 : ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) * sc = 1 := GlobalTheory.T.modulus_characters_product_one k i t h
  rw [LinearMap.smul_apply, smul_smul, smul_smul, Units.val_mul]
  congr 1
  linear_combination ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) * h6

theorem eO_supp (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k (i + (t + 1))), IsCompact C ∧
      ∀ g, eO ψ f g ≠ 0 → ∃ h ∈ HPG k i (t + 1), ∃ c ∈ C, g = h * c := by
  have ee : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨C, hC, hCl, hsupp⟩ := GlobalTheory.T.support_compact_mod_parabolic_off_closed k i t τ σ f hf
  obtain ⟨N, hN, hcell⟩ := exists_compact_cell i t C hC hCl
  refine ⟨(castM k ee).symm '' N, hN.image (castM_cont ee).2, fun g hg => ?_⟩
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) with hy
  have hne : intO f y ≠ 0 := fun h0 => hg (by
    unfold eO
    rw [show wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) g) = y from rfl, h0, map_zero, smul_zero])
  obtain ⟨d, hd⟩ : ∃ d, evX f (dEmb k i t d * y) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold intO
    rw [show (fun d => evX f (dEmb k i t d * y)) = fun _ => 0 from funext hcon]
    exact smInt_zero'
  obtain ⟨h1, hh1, c, hc, e1⟩ := hsupp _ hd
  obtain ⟨h2, hh2, d2, m2, hm2, e2⟩ := hcell c hc
  have e3 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g * m2⁻¹) =
      (h1 * h2) * dEmb k i t d2 * wEl k i t := by
    have e4 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) =
        h1 * (h2 * dEmb k i t d2 * wEl k i t * sEmb k ((i + 1) + t) m2) := by
      rw [← e2, ← e1, hy, mul_assoc]
    rw [map_mul, map_inv, ← mul_assoc, e4]
    group
  obtain ⟨h', hh', e5⟩ := GlobalTheory.T.open_cell_double_coset_uniqueness k i t _ d d2 (h1 * h2) (mul_mem hh1 hh2) e3
  refine ⟨h', hh', (castM k ee).symm m2, ⟨m2, hm2, rfl⟩, ?_⟩
  apply (castM k ee).injective
  rw [map_mul, MulEquiv.apply_symm_apply, e5]
  group

theorem memOAlt (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  let F : indSpace (HPG k i (t + 1)) (sigO τ σ ψ) := ⟨eO ψ f, fun h g => eO_equiv ψ τ σ f h g⟩
  have hF : F ∈ smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ)) := by
    show IsOpen {g | ind (HPG k i (t + 1)) (sigO τ σ ψ) g F = F}
    convert GlobalTheory.T.isOpen_right_invariance_orbit_coefficient k i t ψ τ σ f using 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h m
      exact congrFun (congrArg Subtype.val h) m
    · intro h
      exact Subtype.ext (funext h)
  obtain ⟨C, hC, hs⟩ := eO_supp ψ τ σ f hf
  exact ⟨⟨⟨F, hF⟩, C, hC, hs⟩, rfl⟩
end

theorem eO_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ f hf
  exact memOAlt i t ψ τ σ f hf

end GlobalTheory.CompanionTheory.BZPhiPG.MemO

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInducedStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_induced : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem | exact GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem <;> assumption)
end

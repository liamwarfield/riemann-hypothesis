module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.DerivTw

section gen

variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem equiv_of_eq {ρ σ : Representation ℂ G V} (h : ρ = σ) : Nonempty (ρ.Equiv σ) :=
  h ▸ ⟨Representation.Equiv.refl _⟩

theorem twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (e : ρ.Equiv σ) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let f := twMap ρ σ N θ e.toLinearEquiv.toLinearMap (fun g v => eint e g v)
  let f' := twMap σ ρ N θ e.symm.toLinearEquiv.toLinearMap (fun g v => eint e.symm g v)
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear f f' ?_ ?_) fun x => ?_⟩
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (e.symm v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e.symm (e v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (ρ (s x) v)) = Submodule.Quotient.mk (σ (s x) (e v))
    rw [eint e]

theorem twKer_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ) (hN : ∀ n : N, χ n = 1) :
    twKer (GlobalTheory.SmGL.twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [GlobalTheory.SmGL.twist_apply, hN, Units.val_one, one_smul, Set.mem_setOf_eq]

theorem twAct_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (χ : G →* ℂˣ) (χ' : M →* ℂˣ)
    (hN : ∀ n : N, χ n = 1) (hχ : ∀ m, χ (s m) = χ' m) :
    Nonempty ((twAct (GlobalTheory.SmGL.twist ρ χ) N θ s hs).Equiv (GlobalTheory.SmGL.twist (twAct ρ N θ s hs) χ')) := by
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq (twKer (GlobalTheory.SmGL.twist ρ χ) N θ) (twKer ρ N θ) (twKer_twist ρ N θ χ hN)) fun x => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.Quotient.mk (p := twKer ρ N θ) ((χ (s x) : ℂ) • ρ (s x) v) =
    (χ' x : ℂ) • Submodule.Quotient.mk (p := twKer ρ N θ) (ρ (s x) v)
  rw [hχ]
  rfl

end gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_of_last {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (h : A (Fin.last n) = eLast k n) :
    A.det = (blockMat k n A).det := by
  have h0 : ∀ j : Fin n, A (Fin.last n) (Fin.castSucc j) = 0 := fun j => by
    rw [h]; simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  have h1 : A (Fin.last n) (Fin.last n) = 1 := by
    rw [h]; simp [eLast]
  rw [Matrix.det_succ_row A (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, h1, Fin.succAbove_last]
  simp [blockMat, ← two_mul, Matrix.submatrix]
  rfl

theorem det_uin {n : ℕ} (u : MirUin k n) :
    Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hb : blockMat k n (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 := by
    rw [show ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v from hv.symm]
    ext i j
    show (1 + colMat k n v.toAdd) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_of_last _ ((mem_Mir_iff k _).1 (u : Mir k n).2), hb]
  simp

theorem det_levi {n : ℕ} (m : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det m := by
  have hb : blockMat k n (((levi k n m : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (m : Matrix (Fin n) (Fin n) k) := by
    ext i j
    show glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [glEmbMat]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    det_of_last _ ((mem_Mir_iff k _).1 (levi k n m : Mir k n).2), hb]

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n t * dpow n s := by
  ext g
  simp only [dpow, detChar_apply, MonoidHom.mul_apply, Complex.ofReal_add, absPow_add, Units.val_mul]
  exact mul_comm _ _

theorem dpow_zero (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow]

theorem dpowM_add (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n t * dpowM n s := by
  ext g
  simp [dpowM, dpow_add]

theorem dpowM_zero (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero]

theorem dpowM_uin {n : ℕ} (s : ℝ) (u : MirUin k n) : dpowM n s (u : Mir k n) = 1 := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [detChar_apply, det_uin, map_one]

theorem dpowM_levi {n : ℕ} (s : ℝ) (m : GL (Fin n) k) : dpowM n s (levi k n m) = dpow n s m := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = _
  rw [detChar_apply, det_levi]
  rfl

theorem tw_tw {n : ℕ} (π : GRep k n) (s t : ℝ) : GIso ((π.tw s).tw t) (π.tw (s + t)) := by
  show Nonempty ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist π.ρ (dpow n s)) (dpow n t)).Equiv (GlobalTheory.SmGL.twist π.ρ (dpow n (s + t))))
  exact equiv_of_eq (by rw [GlobalTheory.SmGL.twist_twist, dpow_add])

theorem tw_zero {n : ℕ} (π : GRep k n) : GIso (π.tw 0) π := by
  show Nonempty ((GlobalTheory.SmGL.twist π.ρ (dpow n 0)).Equiv π.ρ)
  exact equiv_of_eq (by rw [dpow_zero, GlobalTheory.SmGL.twist_one])

theorem mtw_mtw {n : ℕ} (τ : MRep k n) (s t : ℝ) : MIso (mtw (mtw τ s) t) (mtw τ (s + t)) := by
  show Nonempty ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist τ.ρ (dpowM n s)) (dpowM n t)).Equiv (GlobalTheory.SmGL.twist τ.ρ (dpowM n (s + t))))
  exact equiv_of_eq (by rw [GlobalTheory.SmGL.twist_twist, dpowM_add])

theorem mtw_zero {n : ℕ} (τ : MRep k n) : MIso (mtw τ 0) τ := by
  show Nonempty ((GlobalTheory.SmGL.twist τ.ρ (dpowM n 0)).Equiv τ.ρ)
  exact equiv_of_eq (by rw [dpowM_zero, GlobalTheory.SmGL.twist_one])

theorem miso_mtw {n : ℕ} {A B : MRep k n} (s : ℝ) (h : MIso A B) : MIso (mtw A s) (mtw B s) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun x => by
    ext v
    show e (((dpowM n s x : ℂˣ) : ℂ) • A.ρ x v) = ((dpowM n s x : ℂˣ) : ℂ) • B.ρ x (e v)
    rw [map_smul]
    exact congrArg _ (eint e x v)⟩

def psiG {n : ℕ} (τ : MRep k n) : GRep k n := ⟨_, psiMinus k τ.ρ⟩

theorem miso_phiM (ψ : AddChar k Circle) {n : ℕ} {A B : MRep k (n + 1)} (h : MIso A B) :
    MIso (MRep.phiM k ψ A) (MRep.phiM k ψ B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_stab ψ n) e

theorem giso_psiG {n : ℕ} {A B : MRep k n} (h : MIso A B) : GIso (psiG A) (psiG B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_normalises n) e

theorem phiM_mtw (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) (s : ℝ) :
    MIso (MRep.phiM k ψ (mtw τ s)) (mtw (MRep.phiM k ψ τ) s) :=
  twAct_twist τ.ρ _ _ _ (levi_stab ψ n) (dpowM (n + 1) s) (dpowM n s) (dpowM_uin s) fun m => by
    show dpowM (n + 1) s (levi k (n + 1) (m : GL (Fin (n + 1)) k)) = _
    rw [dpowM_levi]
    rfl

theorem psiG_mtw {n : ℕ} (τ : MRep k n) (s : ℝ) : GIso (psiG (mtw τ s)) ((psiG τ).tw s) :=
  twAct_twist τ.ρ _ _ _ (levi_normalises n) (dpowM n s) (dpow n s) (dpowM_uin s) (dpowM_levi s)

theorem miso_iterPhi (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) {A B : MRep k (n + j)}, MIso A B →
    MIso (iterPhi k ψ j A) (iterPhi k ψ j B)
  | 0, _, _, h => h
  | j + 1, _, _, h => miso_iterPhi ψ j (miso_phiM ψ h)

theorem iterPhi_mtw (ψ : AddChar k Circle) {n : ℕ} (s : ℝ) : ∀ (j : ℕ) (X : MRep k (n + j)),
    MIso (iterPhi k ψ j (mtw X s)) (mtw (iterPhi k ψ j X) s)
  | 0, _ => miso_refl _
  | j + 1, X => miso_trans (miso_iterPhi ψ j (phiM_mtw ψ X s)) (iterPhi_mtw ψ s j (MRep.phiM k ψ X))

theorem iterN_iso (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)),
    MIso (iterN ψ j τ) (mtw (iterPhi k ψ j τ) (-(j : ℝ) / 2))
  | 0, τ => by
    rw [show -((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact miso_symm (mtw_zero τ)
  | j + 1, τ => by
    have h1 := iterN_iso ψ j (phiN ψ τ)
    have h2 := iterPhi_mtw ψ (-1 / 2) j (MRep.phiM k ψ τ)
    have h3 := mtw_mtw (iterPhi k ψ j (MRep.phiM k ψ τ)) (-1 / 2) (-(j : ℝ) / 2)
    rw [show (-1 / 2 : ℝ) + -(j : ℝ) / 2 = -((j + 1 : ℕ) : ℝ) / 2 by push_cast; ring] at h3
    exact miso_trans h1 (miso_trans (miso_mtw _ h2) h3)

theorem derivB_iso_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  intro k _ _ _ _ ψ j n π
  cases j with
  | zero =>
    rw [show ((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact giso_symm (tw_zero π)
  | succ j =>
    have h1 : MIso (iterN ψ j (gres π)) (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2)) := iterN_iso ψ j (gres π)
    have h2 : GIso (psiN (iterN ψ j (gres π))) ((psiG (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))).tw (-1 / 2)) :=
      giso_tw _ (giso_psiG h1)
    have h3 := giso_tw (-1 / 2) (psiG_mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))
    have h4 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2) (-1 / 2)
    have h5 : GIso ((dG ψ (j + 1) π).tw (((j + 1 : ℕ) : ℝ) / 2))
        (((psiG (iterPhi k ψ j (resM k π.ρ))).tw (-(j : ℝ) / 2 + -1 / 2)).tw (((j + 1 : ℕ) : ℝ) / 2)) :=
      giso_tw _ (giso_trans h2 (giso_trans h3 h4))
    have h6 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2 + -1 / 2) (((j + 1 : ℕ) : ℝ) / 2)
    rw [show -(j : ℝ) / 2 + -1 / 2 + ((j + 1 : ℕ) : ℝ) / 2 = 0 by push_cast; ring] at h6
    exact giso_symm (giso_trans h5 (giso_trans h6 (tw_zero _)))

end GlobalTheory.CompanionTheory.LeibOrd.DerivTw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIsoStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_twisted_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | exact GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZDeriv

theorem isSmooth_resM {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V)
    (hπ : IsSmooth π) : IsSmooth (resM k π).ρ := by
  intro v
  exact (hπ v).preimage continuous_subtype_val

theorem isGenericFor_of_isCuspidal_of
    (hNZ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V →
      ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)))
    (hRes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (m + 1)) k) V),
      twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n))
    (hVan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤)
    (hW0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V),
      twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N)) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  intro k _ _ _ _ ψ hψc hψ1 N V _ _ π hπ hV
  have hV' : Nontrivial (resM k π).V := hV
  obtain ⟨n, hn, hnt⟩ := hNZ k ψ hψc hψ1 N (resM k π).V (resM k π).ρ (isSmooth_resM π hπ.1) hV'
  rw [Submodule.Quotient.nontrivial_iff, hRes k ψ N n V π] at hnt
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [hW0 k ψ (N + 1) V π] at hnt
    exact Submodule.Quotient.nontrivial_iff.2 hnt
  · exact absurd (hVan k ψ (N + 1) n V π hπ hpos (Nat.lt_succ_of_le hn)) hnt

theorem isGenericFor_of_isCuspidal :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  isGenericFor_of_isCuspidal_of GlobalTheory.T.exists_nontrivial_derivative (fun k _ _ _ _ ψ m n V _ _ π =>
    GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) GlobalTheory.T.cuspidal_twisted_kernel_top
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)

end GlobalTheory.CompanionTheory.BZDeriv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGenericStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_is_generic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  first | exact @GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhiTw

variable {k : Type} [Field k]

theorem twKer_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ)
    (h : ∀ n : N, χ (n : G) = 1) : twKer (GlobalTheory.SmGL.twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, GlobalTheory.SmGL.twist_apply, h, Units.val_one, one_smul]

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin n, glEmbMat k n A (Fin.last n) (Fin.castSucc i) = 0 := fun i => by
    simp [glEmbMat]
  have h1 : glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by simp [glEmbMat]
  have h2 : (glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [glEmbMat]
  simp only [h0, h1, h2]
  simp [← two_mul, pow_mul]

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have e : ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + colMat k n v.toAdd := rfl
  rw [e, Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    induction i using Fin.lastCases with
    | last => simp [colMat]
    | cast i => simp [colMat, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := (ne_of_lt hij').symm
    have hj : j ≠ Fin.last n := (lt_of_lt_of_le hij' (Fin.le_last i)).ne
    simp [colMat, hj, hne]

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpowM_unip (n : ℕ) (t : ℝ) (u : MirUin k n) : dpowM n t (u : Mir k n) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hd : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext1
    rw [hv']
    exact det_unip n v
  show dpow (n + 1) t ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [dpow, detChar_apply, hd, map_one]

theorem dpowM_levi (n : ℕ) (t : ℝ) (p : Mir k n) :
    dpowM (n + 1) t ((levi k (n + 1)).comp (Mir k n).subtype p) = dpowM n t p := by
  have hd : Matrix.GeneralLinearGroup.det (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) =
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) := by
    ext1
    exact det_glEmbMat (n + 1) _
  show dpow (n + 2) t (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) = dpow (n + 1) t (p : GL (Fin (n + 1)) k)
  rw [dpow, dpow, detChar_apply, detChar_apply, hd]

theorem phiMinus_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (GlobalTheory.SmGL.twist τ (dpowM (j + 1) t))).Equiv (GlobalTheory.SmGL.twist (phiMinus k ψ τ) (dpowM j t))) := by
  intro k _ _ _ _ ψ j W _ _ τ t
  have hK := twKer_twist τ (MirUin k (j + 1)) (mirChar k ψ j) (dpowM (j + 1) t) (dpowM_unip (j + 1) t)
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq _ _ hK) fun p => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  show Submodule.Quotient.mk ((GlobalTheory.SmGL.twist τ (dpowM (j + 1) t)) ((levi k (j + 1)).comp (Mir k j).subtype p) v) =
    GlobalTheory.SmGL.twist (phiMinus k ψ τ) (dpowM j t) p (Submodule.Quotient.mk v)
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.twist_apply, dpowM_levi]
  rfl

end Local

end GlobalTheory.CompanionTheory.LeibPhiTw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquivStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_functor_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (GlobalTheory.SmGL.twist τ (dpowM (j + 1) t))).Equiv (GlobalTheory.SmGL.twist (phiMinus k ψ τ) (dpowM j t))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv | exact GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv | (intros; apply GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField

namespace GlobalTheory.CompanionTheory.StdCharQ

end GlobalTheory.CompanionTheory.StdCharQ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNorm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ResCardAbsNorm

theorem resCard_completion_eq_absNorm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (resCard (w.adicCompletion E) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ w
  exact_mod_cast GlobalTheory.LFun.SatBoundGL.resCard_completion w

end GlobalTheory.CompanionTheory.ResCardAbsNorm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNormStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_card_eq_abs_norm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (resCard (w.adicCompletion E) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm | exact GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm | (intros; apply GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_glEmbMat_comp {k X : Type} [Field k] [TopologicalSpace k] [TopologicalSpace X] (m : ℕ)
    {f : X → Matrix (Fin m) (Fin m) k} (hf : Continuous f) :
    Continuous fun x => glEmbMat k m (f x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc] <;>
    first
    | exact continuous_const
    | exact hf.matrix_elem _ _

theorem continuous_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  intro k _ _ _ _ n
  have hemb : Continuous (GlobalTheory.BZMir.glEmb k (n + 1)) :=
    Continuous.units_map _ (GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp (n + 1) continuous_id)
  exact continuous_induced_rng.2 (hemb.comp continuous_subtype_val)

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbeddingStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mirabolic_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHolds
open PositivityTheory.Rg.BcB.F.Eig

namespace GlobalTheory.CompanionTheory.BlockScalars

theorem diagOp_apply {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ)
    (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    (diagOp blk c x) j = c (blk j) * x j := by
  simp [diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem diagAlg : DiagAlg := by
  intro ι d blk c c' z
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x j
    simp [diagOp_apply, ContinuousLinearMap.mul_def, mul_assoc]
  · ext x j
    simp [diagOp_apply, add_mul]
  · ext x j
    simp [diagOp_apply]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [PiLp.inner_apply, diagOp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [RCLike.inner_apply]
    ring

end GlobalTheory.CompanionTheory.BlockScalars
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHoldsStatement
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_algebra_holds : DiagAlg := by
  first | exact @GlobalTheory.CompanionTheory.BlockScalars.diagAlg | exact GlobalTheory.CompanionTheory.BlockScalars.diagAlg | (intros; apply GlobalTheory.CompanionTheory.BlockScalars.diagAlg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentity
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

private theorem continuous_leviProj_hpgIncl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (b : Bool) :
    Continuous (fun h : HPG k i t => (leviProj k (ePG i t) (hpgIncl k i t h)) b) := by
  have h0 : Continuous (fun h : HPG k i t =>
      (((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    (h0.matrix_submatrix (fun j => (ePG i t) ⟨b, j⟩) (fun j => (ePG i t) ⟨b, j⟩)).congr (fun _ => rfl)
  rw [Units.continuous_iff]
  refine ⟨hv, ?_⟩
  have hinv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h⁻¹)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    hv.comp continuous_inv
  refine hinv.congr (fun h => ?_)
  simp only [map_inv, Pi.inv_apply]

theorem continuous_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) : Continuous (pgProj k i t) := by
  have h1 : Continuous (fun h : HPG k i t => (pgProj k i t h).1) :=
    continuous_induced_rng.2 ((continuous_leviProj_hpgIncl k i t false).congr (fun _ => rfl))
  have h2 : Continuous (fun h : HPG k i t => (pgProj k i t h).2) :=
    (continuous_leviProj_hpgIncl k i t true).congr (fun _ => rfl)
  exact (h1.prodMk h2).congr (fun _ => rfl)

theorem isSmooth_sigX {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) : IsSmooth (sigX τ σ) := by
  have hd : ∀ (n : ℕ) (s : ℂ), IsSmoothChar (detChar (Fin n) (absPow k s)) :=
    fun n s => IsSmoothChar.detChar (isSmoothChar_of_isUnram (isUnram_absPow k s))
  have h1 : IsSmooth (mtw τ (↑(t + 1) / 2)).ρ := by
    refine isSmooth_twist hτ ?_
    unfold dpowM dpow
    unfold IsSmoothChar
    rw [← MonoidHom.comap_ker]
    exact IsOpen.preimage continuous_subtype_val (hd _ _)
  have h2 : IsSmooth (σ.tw (-↑(i + 1 + 1) / 2)).ρ := by
    unfold GRep.tw
    exact isSmooth_twist hσ (by unfold dpow; exact hd _ _)
  intro v
  exact (isSmooth_extTensor h1 h2 v).preimage (continuous_pgProj k (i + 1) (t + 1))

theorem sigX_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  intro k _ _ _ _ i t τ σ hτ hσ w
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (isSmooth_sigX τ σ hτ hσ w)
  have h1 : (1 : HPG k (i + 1) (t + 1)) ∈ Subtype.val ⁻¹' O := by
    rw [hOeq]
    simp
  refine ⟨O, hO.mem_nhds h1, fun h hh => ?_⟩
  have hh' : h ∈ Subtype.val ⁻¹' O := hh
  rw [hOeq] at hh'
  exact hh'

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentityStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinear
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinear
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Lin

open GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_add {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) {φ₁ φ₂ : (Fin n → k) → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    @smInt _ _ (borel _) _ _ (muD k n) (φ₁ + φ₂) =
      @smInt _ _ (borel _) _ _ (muD k n) φ₁ + @smInt _ _ (borel _) _ _ (muD k n) φ₂ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  exact smInt_add (muD k n) l₁ c₁ l₂ c₂

theorem muD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) (c : ℂ) {φ : (Fin n → k) → W}
    (l : IsLocallyConstant φ) (h : HasCompactSupport φ) :
    @smInt _ _ (borel _) _ _ (muD k n) (c • φ) = c • @smInt _ _ (borel _) _ _ (muD k n) φ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  have e : (⇑(c • LinearMap.id : W →ₗ[ℂ] W) ∘ φ) = c • φ := rfl
  rw [← e, smInt_linear (muD k n) (c • LinearMap.id : W →ₗ[ℂ] W) l h]
  rfl

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def tw (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V :=
  fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)

theorem tw_add (ψ : AddChar k Circle) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (f + g) y = tw ψ f y + tw ψ g y :=
  funext fun _ => smul_add _ _ _

theorem tw_smul (ψ : AddChar k Circle) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (c • f) y = c • tw ψ f y :=
  funext fun d => by
    show (_ : ℂ) • (c • evX f _) = c • ((_ : ℂ) • evX f _)
    exact smul_comm _ _ _

theorem tw_lc (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (tw ψ f y) := by
  have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
    (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
  have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
      (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
    h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
  exact IsLocallyConstant.comp₂ h2 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (fun a b => a • b)

theorem tw_cs (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    HasCompactSupport (tw ψ f y) := by
  refine (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2.mono fun d hd h0 => hd ?_
  have h0' : evX f (dEmb k i t d * y) = 0 := h0
  show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
  rw [h0', smul_zero]

theorem intO_add (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (f + g) y = intO f y + intO g y :=
  muD_add (t + 1) (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2
    (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).2

theorem intO_smul (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (c • f) y = c • intO f y :=
  muD_smul (t + 1) c (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2

theorem intC_add (ψ : AddChar k Circle) (hψ : Continuous ψ) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (f + g) y = intC ψ f y + intC ψ g y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_add ψ f g y)).trans
    (muD_add (t + 1) (tw_lc ψ hψ f y) (tw_cs ψ f y) (tw_lc ψ hψ g y) (tw_cs ψ g y))

theorem intC_smul (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (c • f) y = c • intC ψ f y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_smul ψ c f y)).trans
    (muD_smul (t + 1) c (tw_lc ψ hψ f y) (tw_cs ψ f y))

theorem scaled_add {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u : ℂ)
    {a b c : A} (h : a = b + c) : u • T a = u • T b + u • T c := by
  rw [h, map_add (f := _), smul_add]

theorem scaled_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u c : ℂ)
    {a b : A} (h : a = c • b) : u • T a = c • u • T b := by
  rw [h, map_smul, smul_comm]

theorem eC_eO_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
    eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f g c
  refine ⟨funext fun m => ?_, funext fun m => ?_, funext fun m => ?_, funext fun m => ?_⟩
  · exact scaled_add (qC τ σ) _ (intC_add ψ hψ f g _)
  · exact scaled_smul (qC τ σ) _ c (intC_smul ψ hψ c f _)
  · exact scaled_add (qO τ σ ψ) _ (intO_add f g _)
  · exact scaled_smul (qO τ σ ψ) _ c (intO_smul c f _)

end GlobalTheory.CompanionTheory.BZPhiPG.Lin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinearStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_maps_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
  eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear | exact GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactIwasawa
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.SiegelAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}


variable (F E) in
abbrev phiInf : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)


variable (F E) in
abbrev phiFin : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)


omit [NumberField E] in
theorem tens_ext {z z' : AF F ⊗[F] E} (h₁ : phiInf F E z = phiInf F E z') (h₂ : phiFin F E z = phiFin F E z') :
    z = z' := by
  obtain ⟨y, hy⟩ : ∃ y : AF F ⊗[F] E, y = z - z' + 1 := ⟨_, rfl⟩
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1)
    (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiInf F E y = 1
      rw [hy, map_add (f := _), map_sub, h₁, sub_self, zero_add, map_one])
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiFin F E y = 1
      rw [hy, map_add (f := _), map_sub, h₂, sub_self, zero_add, map_one])
  have h3 : z - z' + 1 = 1 := hy.symm.trans (congrFun (congrFun this 0) 0)
  exact sub_eq_zero.1 (add_right_cancel (h3.trans (zero_add 1).symm))

omit [NumberField E] in
theorem matrix_tens_ext {a b : Type} {P Q : Matrix a b (AF F ⊗[F] E)} (h₁ : P.map (phiInf F E) = Q.map (phiInf F E))
    (h₂ : P.map (phiFin F E) = Q.map (phiFin F E)) : P = Q :=
  Matrix.ext fun i j => tens_ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

omit [NumberField E] in
theorem mat_projInf (g : GAd σ J) : (matHom _ σ J (projInf σ J g)).1 = (matHom _ σ J g).1.map (phiInf F E) := rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = (matHom _ σ J g).1.map (phiFin F E) := rfl

theorem mem_minPar_of_parts {p q : GAd σ J} (hp : p ∈ minPar σ J X) (h₁ : projInf σ J q = projInf σ J p)
    (h₂ : projFin σ J q = 1) : q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  let e₀ : AF F ⊗[F] E := (((1 : Ainf F), (0 : Af F)) : AF F) ⊗ₜ[F] (1 : E)
  have e₁ : phiInf F E e₀ = 1 := rfl
  have e₂ : phiFin F E e₀ = 0 := TensorProduct.zero_tmul _ _
  let B' : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
    Matrix.of fun i j => (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j +
      e₀ * (B i j - (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j)
  have b₁ : B'.map (phiInf F E) = B.map (phiInf F E) := Matrix.ext fun i j => by
    simp [B', e₁]
  have b₂ : B'.map (phiFin F E) = 1 := Matrix.ext fun i j => by
    by_cases hij : i = j
    · subst hij; simp [B', e₂]
    · simp [B', e₂, Matrix.one_apply_ne hij]
  refine ⟨B', fun i j hij => ?_, matrix_tens_ext ?_ ?_⟩
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    simp [B', hB hij, Matrix.one_apply_ne hne]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projInf, h₁, mat_projInf, b₁, ← Matrix.map_mul, e, Matrix.map_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projFin, h₂, b₂]
    simp

theorem commute_of_mem {a b : GAd σ J} (ha : a ∈ infPts σ J) (hb : b ∈ finPts σ J) : Commute a b := by
  have ha' : a ∈ (ofInf σ J).range := by rw [range_ofInf]; exact ha
  have hb' : b ∈ (ofFin σ J).range := by rw [range_ofFin]; exact hb
  obtain ⟨x, rfl⟩ := ha'
  obtain ⟨y, rfl⟩ := hb'
  exact commute_ofInf_ofFin σ J x y

theorem mul_mem_leviMin {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

def prodSub (K₁ K₂ : Subgroup (GAd σ J)) (h₁ : K₁ ≤ infPts σ J) (h₂ : K₂ ≤ finPts σ J) : Subgroup (GAd σ J) where
  carrier := (K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))
  one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
    have c : b * a' = a' * b := ((commute_of_mem (h₁ ha') (h₂ hb)).eq).symm
    change a * a' * (b * b') = a * b * (a' * b')
    rw [mul_assoc a b, ← mul_assoc b, c, mul_assoc a', mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
    change a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact ((commute_of_mem (h₁ (K₁.inv_mem ha)) (h₂ (K₂.inv_mem hb))).eq)

end GlobalTheory.CompanionTheory.SiegelAssemble


open GlobalTheory.CompanionTheory.SiegelAssemble in
theorem GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K₁ K₂ : Subgroup (GAd σ J), K₁ ≤ infPts σ J → K₂ ≤ finPts σ J → IsCompact (K₁ : Set (GAd σ J)) → IsCompact (K₂ : Set (GAd σ J)) → (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K₁, g = p * k) → (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K₂, g = p * k) → (∀ p ∈ minPar σ J X, p ∈ K₁ → p ∈ leviMin σ J X Y) → GoodPosition σ J X Y K₂ → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ hlev hgood
  refine ⟨prodSub K₁ K₂ h₁ h₂, (show IsCompact ((K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))) from c₁.mul c₂), fun g => ?_, ?_⟩
  · obtain ⟨p₁, hp₁, hp₁', k₁, hk₁, e₁⟩ := iw₁ (ofInf σ J (projInf σ J g)) (mem_infPts.2 (by simp))
    obtain ⟨p₂, hp₂, hp₂', k₂, hk₂, e₂⟩ := iw₂ (ofFin σ J (projFin σ J g)) (mem_finPts.2 (by simp))
    refine ⟨p₁ * p₂, mul_mem_minimal_parabolic hp₁ hp₂, k₁ * k₂, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, ?_⟩
    have c : k₁ * p₂ = p₂ * k₁ := (commute_of_mem (h₁ hk₁) hp₂').eq
    calc g = ofInf σ J (projInf σ J g) * ofFin σ J (projFin σ J g) := (ofInf_projInf_mul_ofFin_projFin σ J g).symm
      _ = p₁ * (k₁ * p₂) * k₂ := by rw [e₁, e₂]; simp only [mul_assoc]
      _ = p₁ * p₂ * (k₁ * k₂) := by rw [c]; simp only [mul_assoc]
  · rintro _ hp ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have i₁ : projFin σ J k₁ = 1 := mem_infPts.1 (h₁ hk₁)
    have i₂ : projInf σ J k₂ = 1 := mem_finPts.1 (h₂ hk₂)
    have m₁ : k₁ ∈ minPar σ J X := mem_minPar_of_parts hp (by simp [i₂]) i₁
    have m₂ : k₂ ∈ minPar σ J X := by
      have := mul_mem_minimal_parabolic (inv_mem_minimal_parabolic h hJ hW m₁) hp
      simpa using this
    obtain ⟨m, hm, hmK, u, hu, huK, rfl⟩ := hgood k₂ m₂ hk₂
    exact ⟨k₁ * m, mul_mem_leviMin (hlev k₁ m₁ hk₁) hm, ⟨k₁, hk₁, m, hmK, rfl⟩, u, hu,
      ⟨1, K₁.one_mem, u, huK, one_mul u⟩, by simp only [mul_assoc]⟩

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProj
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProj
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_gpProj_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) :=
  GlobalTheory.CompanionTheory.BZMir.continuous_gpProj

end GlobalTheory.CompanionTheory.LeibPhi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProjStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi <;> assumption)
end
end

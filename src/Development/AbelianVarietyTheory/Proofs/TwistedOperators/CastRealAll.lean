module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DualWeylTensor

open MvPolynomial

def domOf {n : ℕ} (w : ℕ → ℤ) (h : ∀ a : ℕ, a + 1 < n → w (a + 1) ≤ w a) : Formalism.BasicNotions.DomWeight n where
  w i := w i
  anti := by
    intro i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only [Fin.mk_le_mk] at hij
    show w j ≤ w i
    have key : ∀ k, i ≤ k → k < n → w k ≤ w i := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hik ih => intro hk1; exact (h k hk1).trans (ih (by omega))
    exact key j hij hj

theorem rev_cast {n : ℕ} (i : Fin n) : ((Fin.rev i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℕ) := by
  have := i.2
  rw [Fin.val_rev, Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast; ring

theorem lam_eq {n : ℕ} (lamH : Fin n → ℝ) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i)) (i : Fin n) :
    (lam i : ℝ) = -lamH (Fin.rev i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  rw [hl i, GlobalTheory.ConjTypeW.lowK_allPos, rev_cast]; ring

theorem step {n : ℕ} (lamH : Fin n → ℝ) (hH : StrictAnti lamH) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i))
    (a : ℕ) (ha : a + 1 < n) : lam (a + 1) ≤ lam a := by
  have h1 := lam_eq lamH lam hl ⟨a, by omega⟩
  have h2 := lam_eq lamH lam hl ⟨a + 1, ha⟩
  have h3 : lamH (Fin.rev ⟨a, by omega⟩) < lamH (Fin.rev ⟨a + 1, ha⟩) :=
    hH (by rw [Fin.rev_lt_rev]; simp [Fin.lt_def])
  simp only [Fin.val_mk] at h1 h2
  have h4 : ((lam (a + 1) : ℤ) : ℝ) < (lam a : ℝ) + 1 := by rw [h1, h2]; push_cast; linarith
  have h5 : lam (a + 1) < lam a + 1 := by exact_mod_cast h4
  omega

theorem rho_cond {n : ℕ} (lamH : Fin n → ℝ) (hH : StrictAnti lamH) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i)) (i : Fin n) :
    -lamH (Fin.rev i) = ((domOf (n := n) lam (step lamH hH lam hl)).w (Fin.cast rfl i) : ℝ) +
      ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ) := by
  show -lamH (Fin.rev i) = ((lam (Fin.cast rfl i : ℕ) : ℤ) : ℝ) + _
  rw [Fin.val_cast, lam_eq lamH lam hl i, Formalism.BasicNotions.rhoVec]
  push_cast; ring

theorem forms_ten_eq {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.ten f = Formalism.L2.DIV.ten f := rfl

theorem polyAction_ten' {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n)
    (h : ι → GL (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.DIV.actP lam h (Formalism.L2.DIV.ten f) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.sqAct ℂ n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => ((h τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)).1
  simp only [Formalism.L2.DIV.actP, Formalism.L2.DIV.ten, Formalism.L2.DIV.detTwK, Formalism.L2.DIV.trAct, Formalism.BasicNotions.sqAct, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem sqAct_invTr {n : ℕ} (lam : Formalism.BasicNotions.DomWeight n) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.BasicNotions.sqAct ℂ n lam (Formalism.BasicNotions.inside₂ ℂ n (GlobalTheory.Branching.unitaryIncl n u)) f =
      ((u : Matrix (Fin n) (Fin n) ℂ).det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ (u : Matrix (Fin n) (Fin n) ℂ)ᴴ f := by
  have hm : ((Formalism.BasicNotions.inside₂ ℂ n (GlobalTheory.Branching.unitaryIncl n u) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((u : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ := by
    show (((GlobalTheory.Branching.unitaryIncl n u)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = _
    rw [← map_inv, GlobalTheory.Branching.unitaryIncl_coe]
    rfl
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) * (u : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).1 u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hd : (u : Matrix (Fin n) (Fin n) ℂ)ᴴ.det = ((u : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    have h1 : (u : Matrix (Fin n) (Fin n) ℂ).det * (u : Matrix (Fin n) (Fin n) ℂ)ᴴ.det = 1 := by
      rw [← Matrix.det_mul, hu, Matrix.det_one]
    exact (eq_inv_of_mul_eq_one_right h1)
  unfold Formalism.BasicNotions.sqAct Formalism.BasicNotions.detPow
  rw [hm, Matrix.transpose_transpose, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hm,
    Matrix.det_transpose, hd, inv_zpow', zpow_neg]

theorem main : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, FiniteDimensional ℂ (H τ)] (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (lamH : ι → Fin n → ℝ) (lam : ι → ℕ → ℤ), (∀ τ, StrictAnti (lamH τ)) → (∀ τ, Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) (σ τ)) → (∀ τ, Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) (σ τ) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) ⊤) → (∀ τ (i : Fin n), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) (Fin.rev i)) → ∃ Φ : Module.Dual ℂ (weylSub n lam) ≃ₗ[ℂ] ⨂[ℂ] τ, H τ, ∀ (u : UG ι n) (φ : Module.Dual ℂ (weylSub n lam)), Φ ((weylRep n lam).dual u φ) = PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) (Φ φ) := by
  intro ι _ _ n H _ _ _ σ lamH lam hH hU hK hl
  classical
  let lam' : ι → Formalism.BasicNotions.DomWeight n := fun τ => domOf (lam τ) (step (lamH τ) (hH τ) (lam τ) (hl τ))
  have hlw : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i := fun _ _ => rfl
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam') := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam')
  have hj := fun τ => GlobalTheory.DualWeylType.dual_weyl_type n n rfl (lam' τ) (H τ) (σ τ) (lamH τ) (hU τ) (hK τ)
    (rho_cond (lamH τ) (hH τ) (lam τ) (hl τ))
  choose j d b hin hon hortho heq using hj
  obtain ⟨Jt, hinj, hrange, hpure⟩ := GlobalTheory.TenInj.main ι n lam' H j d b hin hon hortho
  have hR : LinearMap.range Jt = Formalism.L2.DIV.VV ℂ lam' := hrange.trans (GlobalTheory.TrueBranch.cSpan_eq_VV lam')
  let E : (⨂[ℂ] τ, H τ) ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam' :=
    (LinearEquiv.ofInjective Jt hinj).trans (LinearEquiv.ofEq _ _ hR)
  have hE : ∀ x, (E x : Formalism.L2.DIV.Pol ℂ ι n) = Jt x := fun _ => rfl
  let U : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n → (ι → GL (Fin n) ℂ) := fun u τ => GlobalTheory.Branching.unitaryIncl n (u τ)
  have hEq : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n) x,
      E (PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) x) =
        Formalism.L2.DIV.rhoK lam' (Formalism.L2.DIV.invTrK (U u)) (E x) := by
    intro u x
    apply Subtype.ext
    rw [hE]
    show Jt _ = Formalism.L2.DIV.actP lam' _ (Jt x)
    have hlin : Jt ∘ₗ PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) =
        Formalism.L2.DIV.actP lam' (Formalism.L2.DIV.invTrK (U u)) ∘ₗ Jt := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, hpure]
      rw [forms_ten_eq, forms_ten_eq, polyAction_ten']
      congr 1
      funext τ
      have hs : ((u τ : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.cast rfl) (Fin.cast rfl) =
          (u τ : Matrix (Fin n) (Fin n) ℂ) := by ext; simp
      have h1 := heq τ (u τ) (u τ).2 (y τ)
      rw [hs] at h1
      rw [ContinuousLinearMap.coe_coe, h1]
      exact (sqAct_invTr (lam' τ) (u τ) _).symm
    exact LinearMap.congr_fun hlin x
  obtain ⟨A, hA⟩ := GlobalTheory.CoefPsi.exists_equiv n lam lam' hlw
  refine ⟨(A.symm.dualMap.trans (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).symm).trans E.symm, fun u φ => ?_⟩
  have hU' : (fun τ => GlobalTheory.Branching.unitaryIncl n ((u⁻¹ : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n) τ)) = (U u)⁻¹ := by
    funext τ
    simp [U, Pi.inv_apply, map_inv]
  have key : ∀ ℓ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), weylRep n lam u⁻¹ (A.symm ℓ) =
      A.symm (ℓ ∘ₗ Formalism.L2.DIV.rhoK lam' (Formalism.L2.DIV.invTrK (U u))) := by
    intro ℓ
    apply A.injective
    rw [hA, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hU',
      map_inv (Formalism.L2.DIV.invTrK (K := ℂ) (ι := ι) (n := n)), inv_inv]
  obtain ⟨v, hvv⟩ : ∃ v, (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).symm (A.symm.dualMap φ) = v := ⟨_, rfl⟩
  have hv : ∀ ℓ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), ℓ v = φ (A.symm ℓ) := by
    intro ℓ
    have h2 := congrArg (fun X => X ℓ) ((Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).apply_symm_apply (A.symm.dualMap φ))
    rw [hvv] at h2
    simpa [Module.evalEquiv_apply] using h2
  apply E.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hvv, hEq, LinearEquiv.apply_symm_apply]
  apply (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).injective
  rw [LinearEquiv.apply_symm_apply]
  ext ℓ
  rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearEquiv.dualMap_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, key, ← hv]
  rfl

end GlobalTheory.DualWeylTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, FiniteDimensional ℂ (H τ)] (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (lamH : ι → Fin n → ℝ) (lam : ι → ℕ → ℤ), (∀ τ, StrictAnti (lamH τ)) → (∀ τ, Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) (σ τ)) → (∀ τ, Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) (σ τ) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) ⊤) → (∀ τ (i : Fin n), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) (Fin.rev i)) → ∃ Φ : Module.Dual ℂ (weylSub n lam) ≃ₗ[ℂ] ⨂[ℂ] τ, H τ, ∀ (u : UG ι n) (φ : Module.Dual ℂ (weylSub n lam)), Φ ((weylRep n lam).dual u φ) = PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) (Φ φ) := by
  first | exact @GlobalTheory.DualWeylTensor.main | exact GlobalTheory.DualWeylTensor.main | (intros; apply GlobalTheory.DualWeylTensor.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefPairTens

open GlobalTheory.DefLift GlobalTheory.DefiniteMult Formalism.IndefR.Mult

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem sigma_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1

theorem sigma_mul (hp : AllPlus M) (τ : D.what₂.Tau) (a b : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    M.σ τ ((a : Matrix (Fin V.rank) (Fin V.rank) ℂ) * b) = (M.σ τ a).comp (M.σ τ b) := by
  have hm : ∀ x : Matrix.unitaryGroup (Fin V.rank) ℂ,
      (x : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * Formalism.REAL.Jm (M.ε τ) * x = Formalism.REAL.Jm (M.ε τ) := fun x => by
    rw [hp.jm τ, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff'.1 x.2
  exact (M.ds τ).2.2.1.1.2 _ (hm a) _ (hm b)

theorem sigma_comp_inv (hp : AllPlus M) (τ : D.what₂.Tau) (v : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ
      ((M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show M.σ τ v (M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) x) = x
  rw [← ContinuousLinearMap.comp_apply, ← sigma_mul hp, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    sigma_one]
  rfl

theorem unfr_one (M : DSModel V S) (τ : D.what₂.Tau) : unfr M τ 1 = 1 := by
  unfold unfr
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem pairEquiv_realAll : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  intro D V S M θ c pr hθ hp hc hpr
  classical
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨-, inj, π, hπ, -⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (m τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  let E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ) := (LinearEquiv.ofBijective pr hb).trans e.symm.dualMap
  have hE : ∀ w y, E w y = pr w (e.symm y) := fun w y => rfl
  let F : ∀ τ, Matrix.unitaryGroup (Fin V.rank) ℂ → (M.H τ →ₗ[ℂ] M.H τ) := fun τ v =>
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)
  have hact : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ), actT M τ (unfr M τ v) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v)) := by
    intro τ v
    unfold actT
    rw [rep_unfr]
  have hπe : ∀ τ v x, π τ v x = e.symm (actT M τ (unfr M τ v) (e x)) := fun τ v x => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, he, hπ]
  have hinv : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) x, π τ v (π τ v⁻¹ x) = x := by
    intro τ v x
    rw [hπe, hπe, LinearEquiv.apply_symm_apply, hact, hact, ← LinearMap.comp_apply (PiTensorProduct.map _),
      ← PiTensorProduct.map_comp]
    have : (fun ρ => Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v) ρ ∘ₗ
        Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹) ρ) = fun ρ => LinearMap.id := by
      funext ρ
      by_cases h : ρ = τ
      · subst h
        simp only [Function.update_self]
        exact GlobalTheory.CoefPairTens.sigma_comp_inv hp ρ v
      · simp only [Function.update_of_ne h, LinearMap.id_comp]
    rw [this, PiTensorProduct.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  have one : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) w,
      E (c.ρ (atTau θ V τ (unfr M τ v)) w) =
        E w ∘ₗ PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹)) := by
    intro τ v w
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearMap.comp_apply, hE, hE, ← hact, ← hπe, LinearEquiv.symm_apply_apply]
    have h1 := key τ v (c.ρ (atTau θ V τ (unfr M τ v)) w) (π τ v⁻¹ x)
    rw [hinv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    exact h1
  refine ⟨E, fun u w => ?_⟩
  let us : Finset D.what₂.Tau → UG D.what₂.Tau V.rank := fun s ρ => if ρ ∈ s then u ρ else 1
  have hM : ∀ (s : Finset D.what₂.Tau) ρ, unfr M ρ (us s ρ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun s ρ =>
    hp.unfr_mem ρ _
  have ind : ∀ s : Finset D.what₂.Tau, ∀ w, E (c.ρ (realAll θ V (fun ρ => unfr M ρ (us s ρ))) w) =
      E w ∘ₗ PiTensorProduct.map (fun ρ => F ρ (us s ρ)⁻¹) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w
      have h0 : (fun ρ => unfr M ρ (us ∅ ρ)) = 1 := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        rw [this, OneMemClass.coe_one, Pi.one_apply]
        exact GlobalTheory.CoefPairTens.unfr_one M ρ
      have h1 : (fun ρ => F ρ (us ∅ ρ)⁻¹) = fun ρ => LinearMap.id := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        show ((M.σ ρ ((us ∅ ρ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) = _
        rw [this, inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      rw [h0, realAll_one hθ, map_one, Module.End.one_apply, h1, PiTensorProduct.map_id, LinearMap.comp_id]
    | insert τ s hτ ih =>
      intro w
      have hs : us s τ = 1 := if_neg hτ
      have h3 : us (insert τ s) τ = u τ := if_pos (Finset.mem_insert_self τ s)
      have h4 : ∀ ρ, ρ ≠ τ → us (insert τ s) ρ = us s ρ := fun ρ h => by
        simp only [us, Finset.mem_insert, h, false_or]
      rw [realAll_eq_atTau_mul hθ (hM (insert τ s)) τ]
      have h2 : Function.update (fun ρ => unfr M ρ (us (insert τ s) ρ)) τ 1 = fun ρ => unfr M ρ (us s ρ) := by
        funext ρ
        by_cases h : ρ = τ
        · rw [h, Function.update_self, hs, OneMemClass.coe_one, GlobalTheory.CoefPairTens.unfr_one]
        · rw [Function.update_of_ne h, h4 ρ h]
      rw [h2, map_mul, Module.End.mul_apply, h3, one, ih, LinearMap.comp_assoc, ← PiTensorProduct.map_comp]
      congr 2
      funext ρ
      by_cases h : ρ = τ
      · subst h
        rw [Function.update_self, hs, h3]
        show ((M.σ ρ ((1 : Matrix.unitaryGroup (Fin V.rank) ℂ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
          M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) ∘ₗ F ρ (u ρ)⁻¹ = F ρ (u ρ)⁻¹
        rw [inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      · rw [Function.update_of_ne h, h4 ρ h, LinearMap.comp_id]
  have huniv : us Finset.univ = u := funext fun ρ => if_pos (Finset.mem_univ ρ)
  have := ind Finset.univ w
  rw [huniv] at this
  exact this

end GlobalTheory.CoefPairTens

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  first | exact @GlobalTheory.CoefPairTens.pairEquiv_realAll | exact GlobalTheory.CoefPairTens.pairEquiv_realAll | (intros; apply GlobalTheory.CoefPairTens.pairEquiv_realAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal.BaseWeights

theorem mem_tparBlock {c x : ℚ} {n : ℕ} (h : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n) : x ∈ TPar.block c n := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact Finset.mem_image.2 ⟨a, Finset.mem_range.2 (List.mem_range.1 ha), rfl⟩

theorem basePar_sublist {S : Sizes} (P : Entries S) : P.basePar.Sublist P.orderList := by
  have h1 : ∀ l : List (Fin (S.k - 1)),
      (l.map fun i => (P.v i : ℚ)).Sublist (l.flatMap fun i => [(P.v i : ℚ), P.u i]) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      exact (ih.cons _).cons₂ _
  unfold Entries.basePar Entries.orderList
  exact List.Sublist.append ((h1 _).trans (List.sublist_append_right _ _)) (List.Sublist.refl _)

theorem base_mem_Dpar (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    ∀ x ∈ (rowEntries D C τ).basePar, ∃ s, (x, s) ∈ (Ptw D).Dpar D.R.m τ := by
  have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.2 D.R.m_even
  obtain ⟨hv, hb, he⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  intro x hx
  simp only [Entries.basePar, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_finRange,
    true_and] at hx
  unfold TPar.Dpar
  rcases hx with ⟨i, rfl⟩ | ⟨j, h | h⟩
  · refine ⟨true, Finset.mem_image.2 ⟨((Ptw D).v τ i, true), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · simp only [hodd, if_false, add_zero]
      exact Prod.ext (hv i) rfl
  · refine ⟨decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m)), Finset.mem_image.2 ⟨(-(Ptw D).b τ j, decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m))), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · simp only [hodd, if_false, add_zero]
      refine Prod.ext ?_ rfl
      rw [h]
      show -(D.hc τ).b j = _
      rw [hb j]; rfl
  · refine ⟨true, Finset.mem_image.2 ⟨(x, true), ?_, ?_⟩⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨x, ?_, rfl⟩
      have hx' := mem_tparBlock h
      have : (-(Ptw D).e τ j) = -(((rowEntries D C τ).e j : ℤ) : ℚ) := by
        show -(D.hc τ).e j = _
        rw [he j]; rfl
      rw [this]
      exact hx'
    · simp only [hodd, if_false, add_zero]

end GlobalTheory.RowReal.BaseWeights

namespace GlobalTheory.RowReal

open GlobalTheory.RowReal.BaseWeights

theorem hw_basePar_eq_neg_lowK : ∀ (D : D7) (C : ℝ)
    (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau)
    (i : Fin D.sp.X'.rank),
    (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  intro D C M τ i
  have hlen : (rowEntries D C τ).basePar.length = D.sp.X'.rank := by
    rw [length_base, D.sp.X'_rank]
    simp [Sizes.nC, rowSizes, Ranks.rankX', Ranks.r]
  have hε : M.ε τ = Formalism.MainNotions.S.allPos _ := funext fun a => GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) M τ a
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hqa : StrictAnti q := fun a b h => by
    have := hanti h
    rw [hq, hq] at this
    exact_mod_cast this
  have hinj : Function.Injective fun a => -q a := fun a b h => hqa.injective (neg_injective h)
  have hE : (Finset.univ.image fun a => -q a).card = D.sp.X'.rank := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hpw := (rowEntries_good D C τ).order.sublist (basePar_sublist (rowEntries D C τ))
  let f : Fin D.sp.X'.rank → ℚ := fun j => (rowEntries D C τ).basePar[(j : ℕ)]'(by rw [hlen]; exact j.2)
  have hf : StrictAnti f := fun a b hab => List.pairwise_iff_getElem.1 hpw _ _ _ _ hab
  have hfm : ∀ j, f j ∈ Finset.univ.image fun a => -q a := by
    intro j
    obtain ⟨s, hs⟩ := base_mem_Dpar D C τ _ (List.getElem_mem (by rw [hlen]; exact j.2))
    have h2 : (-(f j), s) ∈ Formalism.IndefR.Mult.parB (Ptw D) D.R.m τ := Finset.mem_image.2 ⟨_, hs, rfl⟩
    rw [hS] at h2
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h2
    refine Finset.mem_image.2 ⟨a, Finset.mem_univ _, ?_⟩
    have h3 := congrArg Prod.fst ha
    simp only at h3
    rw [h3, neg_neg]
  let g : Fin D.sp.X'.rank → ℚ := fun j => -q j.rev
  have hg : StrictAnti g := fun a b hab => by
    simp only [g, neg_lt_neg_iff]
    exact hqa (Fin.rev_lt_rev.2 hab)
  have hgm : ∀ j, g j ∈ Finset.univ.image fun a => -q a := fun j => Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hfg : f = g := (GlobalTheory.SignedHC.descEnum_unique hE hf hfm).symm.trans (GlobalTheory.SignedHC.descEnum_unique hE hg hgm)
  have hi : (i : ℕ) < (rowEntries D C τ).basePar.length := by rw [hlen]; exact i.2
  have key : (rowEntries D C τ).basePar[(i : ℕ)] = -q i.rev := congrFun hfg i
  have h1 := hw_base _ i hi
  have hl : (((rowEntries D C τ).basePar.length : ℕ) : ℚ) = (D.sp.X'.rank : ℚ) := by rw [hlen]
  rw [hl, key] at h1
  rw [hε, GlobalTheory.ConjTypeW.lowK_allPos, hq]
  have h4 : (hw (rowEntries D C τ).basePar i : ℝ) = (((hw (rowEntries D C τ).basePar i : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h4, h1, Fin.val_rev]
  have h5 : (i : ℕ) + 1 ≤ D.sp.X'.rank := i.2
  rw [Nat.cast_sub h5]
  push_cast
  ring

end GlobalTheory.RowReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType : ∀ (D : D7) (C : ℝ) (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank), (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  first | exact @GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | exact GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | (intros; apply GlobalTheory.RowReal.hw_basePar_eq_neg_lowK <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowReal
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefBase

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem rank_X (ch : Choice R) : (rowSizes D).nC (0 : Fin ((rowSizes D).m + 1)) = D.sp.X'.rank := by
  have h1 := rank_gridM ch.G (i := 0) (Nat.zero_le _)
  have h2 : (ch.G.V (.grid 0 D.R.m)) = (columnBlock R.toLevCh D.R.m).sp := rfl
  rw [h2, colY_m] at h1
  exact h1.symm

def xPt (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : GA D D.sp.X' :=
  cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0)

theorem cast_realAll (θ : InfFam D) (n0 : ℕ) (hn : n0 = D.sp.X'.rank) (v : UG D.what₂.Tau n0) :
    ∀ (X : LSp D) (h : X = ⟨D.sp.X', R.toLevCh.ΛX⟩) (O : D.what₂.Tau → Matrix (Fin X.sp.rank) (Fin X.sp.rank) ℂ)
      (hO : HEq O (onb R.MX)) (e1 : n0 = X.sp.rank),
      cast (congrArg (fun X : LSp D => GA D X.sp) h)
        (realAll θ X.sp (fun τ => O τ * ((castU e1 (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) * (O τ)⁻¹)) =
      realAll θ D.sp.X' (fun τ => onb R.MX τ * ((castU hn (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        (onb R.MX τ)⁻¹) := by
  intro X h
  subst h
  intro O hO e1
  cases eq_of_heq hO
  rfl

theorem xPt_eq (ch : Choice R) (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) (g : Gc D.what₂.Tau (rowSizes D)) :
    xPt ch g = realAll R.θ D.sp.X' (fun τ => GlobalTheory.DefLift.unfr R.MX τ
      ((castU (rank_X ch) (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)) := by
  unfold xPt
  have hk : ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      realAll ch.W.θ (columnBlock R.toLevCh D.R.m).sp (fun τ => ch.W.onb (.grid 0 D.R.m) τ *
        ((castU (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
          (ch.W.onb (.grid 0 D.R.m) τ)⁻¹) := by
    exact vtxPt_eq h0 (colU ch.G 0 g)
  rw [hk]
  have e := cast_realAll (R := R) ch.W.θ _ (rank_X ch) (g.2 0) (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh)
    (ch.W.onb (.grid 0 D.R.m)) hO.onbX (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm
  refine e.trans ?_
  rw [hO.θ]
  congr 1
  funext τ
  unfold GlobalTheory.DefLift.unfr onb
  rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.DefLift.fr_det R.MX τ)]

end GlobalTheory.CoefBase

namespace GlobalTheory.CoefBase

section Core

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

end Core

section Core2

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

theorem core (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (hθ : IsInfFam θ) (hp : GlobalTheory.DefLift.AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) (lam : D.what₂.Tau → ℕ → ℤ)
    (hl : ∀ τ (i : Fin V.rank), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i)) :
    ∃ A : c.W ≃ₗ[ℂ] weylSub V.rank lam, ∀ (u : UG D.what₂.Tau V.rank) (w : c.W),
      A (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = weylRep V.rank lam u (A w) := by
  have hε : ∀ τ, M.ε τ = Formalism.MainNotions.S.allPos V.rank := fun τ => funext fun a => hp τ a
  have m := fun τ => GlobalTheory.CompactModel.model_allPos D V S M τ (hε τ)
  haveI : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (m τ).1
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel D V S M θ c pr hθ hp hc hpr
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan D.what₂.Tau V.rank M.H M.σ M.lam lam (fun τ => (M.enum τ).1) (fun τ => (m τ).2.2.1) (fun τ => (m τ).2.2.2)
    (fun τ i => by rw [hl τ i, hε τ])
  haveI : FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := inferInstance
  haveI : FiniteDimensional ℂ (Module.Dual ℂ (weylSub V.rank lam)) := Module.Finite.equiv Φ.symm
  haveI : FiniteDimensional ℂ (weylSub V.rank lam) := (Module.finite_dual_iff ℂ).1 this
  let ev := Module.evalEquiv ℂ (weylSub V.rank lam)
  refine ⟨(E.trans Φ.dualMap).trans ev.symm, fun u w => ?_⟩
  apply ev.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext φ
  rw [LinearEquiv.dualMap_apply, hE, LinearMap.comp_apply]
  have key : (PiTensorProduct.map fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
      M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) (Φ φ) = Φ ((weylRep V.rank lam).dual u⁻¹ φ) := (hΦ u⁻¹ φ).symm
  rw [key]
  obtain ⟨y, hy⟩ := ev.surjective (Φ.dualMap (E w))
  rw [← hy, LinearEquiv.symm_apply_apply]
  have h2 : E w (Φ ((weylRep V.rank lam).dual u⁻¹ φ)) = ev y ((weylRep V.rank lam).dual u⁻¹ φ) := by
    rw [hy]; rfl
  rw [h2]
  show ((weylRep V.rank lam).dual u⁻¹ φ) y = φ (weylRep V.rank lam u y)
  rw [Representation.dual_apply, inv_inv]
  rfl

end Core2

theorem weyl_cast {ι : Type} [Fintype ι] [DecidableEq ι] (n n' : ℕ) (h : n = n') (lam : ι → ℕ → ℤ) :
    ∃ e : weylSub (ι := ι) n lam ≃ₗ[ℂ] weylSub n' lam, ∀ u F,
      e (weylRep n lam u F) = weylRep n' lam (fun τ => castU h (u τ)) (e F) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cast_inv : ∀ (X Y : LSp D) (h : X = Y) (a : GA D X.sp),
    cast (congrArg (fun X : LSp D => GA D X.sp) h) a⁻¹ = (cast (congrArg (fun X : LSp D => GA D X.sp) h) a)⁻¹ := by
  intro X Y h a
  subst h
  rfl

theorem xPt_inv (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : xPt ch g⁻¹ = (xPt ch g)⁻¹ := by
  have hk : ((kappa ch.W g⁻¹).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp)⁻¹ :=
    congrArg (fun x => x.2 0) (map_inv (kappa ch.W) g)
  exact (congrArg (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh))) hk).trans
    (cast_inv (columnBlock R.toLevCh D.R.m) _ (colY_m R.toLevCh) ((kappa ch.W g).2 0))

theorem coefBase [DecidableEq D.what₂.Tau] (ch : Choice R) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX)
    (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) :
    ∃ B : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
        Module.Dual ℂ R.cX.W,
      ∀ g φ, B ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
        B φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹ := by
  obtain ⟨A0, hA0⟩ := core R.MX R.θ R.cX R.prX hθ (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hc hpr
    (baseWt (rowEntries D ch.sc.cGap)) (fun τ i => GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType D ch.sc.cGap R.MX τ i)
  obtain ⟨e, he⟩ := weyl_cast (ι := D.what₂.Tau) _ _ (rank_X ch) (baseWt (rowEntries D ch.sc.cGap))
  refine ⟨(A0.trans e.symm).dualMap, fun g φ => ?_⟩
  ext w
  show ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) (e.symm (A0 w)) = φ (e.symm (A0 (R.cX.ρ (xPt ch g)⁻¹ w)))
  rw [← xPt_inv, xPt_eq ch hO h0, hA0, Representation.dual_apply]
  have h1 := he (g⁻¹.2 0) (e.symm (A0 w))
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.CoefBase

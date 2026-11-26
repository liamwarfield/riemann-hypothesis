module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.ReadLaws

theorem isInv_of_isUni {ι : Type} {n : ℕ} {u : ι → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) : IsInv u := by
  intro τ
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp (hu τ))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

def trFr {ι : Type} {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : IsInv g)
    (y : Frames G) : Frames G :=
  ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩

theorem continuous_valC {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {lam : ι → DomWeight n}
    {Φ : Frames G → ℂ} (hΦ : Φ ∈ ValC G lam) {X : Type} [TopologicalSpace X] {f : X → ι → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hi : ∀ x τ, IsUnit (f x τ).det) : Continuous fun x => Φ ⟨f x, hi x⟩ := by
  obtain ⟨P, -, rfl⟩ := hΦ
  have e : (fun x => fnOf G (shiftOf lam) 1 P (⟨f x, hi x⟩ : Frames G)) =
      fun x => (∏ τ, (f x τ).det ^ shiftOf lam τ) * GlobalTheory.KJInf.evalAt (f x) P :=
    funext fun x => GlobalTheory.KJInf.ValPol.fnOf_one_apply _ P _
  rw [e]
  simp only [GlobalTheory.KJInf.ValPol.evalAt_eq]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => ?_) ?_
  · exact (((continuous_apply τ).comp hf).matrix_det).zpow₀ _ fun x => Or.inl (hi x τ).ne_zero
  · exact (MvPolynomial.continuous_eval P).comp
      (continuous_pi fun v => ((continuous_apply v.1).comp hf).matrix_elem v.2.1 v.2.2)

end GlobalTheory.SeeSaw.ReadLaws


open GlobalTheory.SeeSaw.ReadLaws in
theorem GlobalTheory.SeeSaw.scalarForm_laws : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → ρ.Is → A.Forms → ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β, (∀ y, IsContAut (c.X j) (t.rd j β ψ y)) ∧ (∀ y g (κ : A.U j β), t.rd j β ψ y (g * κ.1) = (A.chi j β κ : ℂ) * t.rd j β ψ y g) ∧ (∀ y y' g, ∀ k ∈ GinfC (c.X j), IsTr (ρ.r j hj k) (ρ.fr j y) (ρ.fr j y') → t.rd j β ψ y (g * k) = t.rd j β ψ y' g) ∧ ∀ g, (fun z => t.rd j β ψ ((ρ.fr j).symm z) g) ∈ ValC _ (ρ.lam j) := by
  intro D c t ρ A _hc hρ hA j hj ψ hψ β
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.X j)
  have hr := hρ.uni j hj
  have hinv : ∀ k : GinfC (c.X j), IsInv (ρ.r j hj k.1) := fun k => isInv_of_isUni (hr.uni k)
  have hR := hA.reps j hj β
  have hrd : ∀ y γ, γ ∈ GQ (c.X j) → ∀ a k (hk : k ∈ GinfC (c.X j)) (κ : A.U j β),
      t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) =
        (A.chi j β κ : ℂ) * A.val j β ψ a (trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y)) :=
    fun y γ hγ a k hk κ => hA.rd j hj ψ hψ β y γ hγ a k hk κ _ (fun τ => rfl)
  have hcomm : ∀ k ∈ GinfC (c.X j), ∀ κ ∈ GfC (c.X j), k * κ = κ * k := fun k hk κ hκ =>
    (GlobalTheory.AutMult.commute_inf_fin (V := c.X j) ⟨k, hk⟩ ⟨κ, hκ⟩).eq
  refine ⟨fun y => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ' hγ' g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ' * (γ * (A.h j β a * k) * κ) = (γ' * γ) * (A.h j β a * k) * (⟨κ, hκ⟩ : A.U j β).1 := by
      simp only [mul_assoc]
    rw [e, hrd y _ (mul_mem hγ' hγ) a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩]
  · rw [continuous_iff_continuousAt]
    intro g0
    obtain ⟨γ, hγ, a, k0, hk0, κ0, hκ0, rfl⟩ := hR.dec g0
    set q : GA D (c.X j) → GA D (c.X j) := fun g => (γ * A.h j β a)⁻¹ * g with hqdef
    have hq : Continuous q := continuous_const.mul continuous_id
    set W : Set (GA D (c.X j)) :=
      {g | ((GlobalTheory.AutMult.toFin (c.X j) (q g) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β} with hWdef
    have hW : IsOpen W := hR.opn.preimage ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp hq)
    have h0 : GlobalTheory.AutMult.toFin (c.X j) (q (γ * (A.h j β a * k0) * κ0)) = ⟨κ0, hR.le hκ0⟩ := by
      have e : q (γ * (A.h j β a * k0) * κ0) =
          ((⟨k0, hk0⟩ : GinfC (c.X j)) : GA D (c.X j)) * ((⟨κ0, hR.le hκ0⟩ : GfC (c.X j)) : GA D (c.X j)) := by
        show (γ * A.h j β a)⁻¹ * (γ * (A.h j β a * k0) * κ0) = k0 * κ0
        group
      rw [e, map_mul, GlobalTheory.AutMult.toFin_coe_inf, GlobalTheory.AutMult.toFin_coe, one_mul]
    have hg0 : γ * (A.h j β a * k0) * κ0 ∈ W := by
      show ((GlobalTheory.AutMult.toFin (c.X j) (q _) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β
      rw [h0]
      exact hκ0
    refine ContinuousOn.continuousAt ?_ (hW.mem_nhds hg0)
    rw [continuousOn_iff_continuous_restrict]
    have hU : ∀ g : W, ((GlobalTheory.AutMult.toFin (c.X j) (q g.1) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β := fun g => g.2
    show Continuous fun g : W => t.rd j β ψ y g.1
    have key : (fun g : W => t.rd j β ψ y g.1) = fun g : W => (A.chi j β ⟨_, hU g⟩ : ℂ) *
        A.val j β ψ a (trFr (ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) (hinv _) (ρ.fr j y)) := by
      funext g
      have e : g.1 = γ * (A.h j β a * (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) * (⟨_, hU g⟩ : A.U j β).1 := by
        have h1 := GlobalTheory.AutMult.toInf_mul_toFin (q g.1)
        calc g.1 = (γ * A.h j β a) * q g.1 := by
              show g.1 = (γ * A.h j β a) * ((γ * A.h j β a)⁻¹ * g.1)
              group
          _ = _ := by
              conv_lhs => rw [← h1]
              simp only [mul_assoc]
      exact (congrArg (t.rd j β ψ y) e).trans (hrd y γ hγ a _ (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).2 _)
    rw [key]
    refine Continuous.mul ?_ ?_
    · have hc : Continuous fun g : W => (⟨_, hU g⟩ : A.U j β) :=
        Continuous.subtype_mk (continuous_subtype_val.comp
          ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp (hq.comp continuous_subtype_val))) _
      exact (hA.chi j hj β).comp hc
    · have hk : Continuous fun g : W => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 :=
        hr.cont.comp ((GlobalTheory.AutMult.continuous_toInf (c.X j)).comp (hq.comp continuous_subtype_val))
      exact continuous_valC (f := fun g : W => fun τ => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 τ * (ρ.fr j y).1 τ)
        (hA.valC j hj ψ hψ β a) (continuous_pi fun τ => ((continuous_apply τ).comp hk).matrix_mul continuous_const) _
  · intro y g κ'
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * κ'.1 = γ * (A.h j β a * k) * ((⟨κ, hκ⟩ : A.U j β) * κ').1 := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, hrd y γ hγ a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩, map_mul, Units.val_mul]
    ring
  · intro y y' g k' hk' htr
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * k' = γ * (A.h j β a * (k * k')) * (⟨κ, hκ⟩ : A.U j β).1 := by
      rw [mul_assoc _ κ k', ← hcomm k' hk' κ (hR.le hκ)]
      simp only [mul_assoc]
    rw [e, hrd y γ hγ a _ (mul_mem hk hk'), hrd y' γ hγ a k hk ⟨κ, hκ⟩]
    have hY : trFr (ρ.r j hj (k * k')) (hinv ⟨k * k', mul_mem hk hk'⟩) (ρ.fr j y) =
        trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y') := by
      apply Subtype.ext
      funext τ
      have hm : ρ.r j hj (k * k') τ = ρ.r j hj k τ * ρ.r j hj k' τ := hr.mul ⟨k, hk⟩ ⟨k', hk'⟩ τ
      show ρ.r j hj (k * k') τ * (ρ.fr j y).1 τ = ρ.r j hj k τ * (ρ.fr j y').1 τ
      rw [htr τ, hm, Matrix.mul_assoc]
    rw [hY]
  · intro g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have hv := hA.valC j hj ψ hψ β a
    refine (GlobalTheory.KJInf.valC_poly _ _ _ _).2.2.1 ((A.chi j β ⟨κ, hκ⟩ : ℂ) • A.val j β ψ a) (Submodule.smul_mem _ _ hv)
      (ρ.r j hj k) _ ?_ (hinv ⟨k, hk⟩)
    intro z z' hz
    rw [hA.rd j hj ψ hψ β _ γ hγ a k hk ⟨κ, hκ⟩ z' (by rwa [Equiv.apply_symm_apply])]
    rfl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → ρ.Is → A.Forms → ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β, (∀ y, IsContAut (c.X j) (t.rd j β ψ y)) ∧ (∀ y g (κ : A.U j β), t.rd j β ψ y (g * κ.1) = (A.chi j β κ : ℂ) * t.rd j β ψ y g) ∧ (∀ y y' g, ∀ k ∈ GinfC (c.X j), IsTr (ρ.r j hj k) (ρ.fr j y) (ρ.fr j y') → t.rd j β ψ y (g * k) = t.rd j β ψ y' g) ∧ ∀ g, (fun z => t.rd j β ψ ((ρ.fr j).symm z) g) ∈ ValC _ (ρ.lam j) := by
  first | exact @GlobalTheory.SeeSaw.scalarForm_laws | exact GlobalTheory.SeeSaw.scalarForm_laws | (intros; apply GlobalTheory.SeeSaw.scalarForm_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslatedEvaluationRowsConjLinearBijection
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapEqZeroOfTranslatedEvalAeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapEqZeroOfTranslatedEvalAeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  intro D X h θ S M J χ t v₀ _ hv₀ T hTm hae
  let T' : MMap M := PiTensorProduct.lift.symm T
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hTm
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ T').1 hT'm
  have hval : T' v₀ = T (PiTensorProduct.tprod ℂ v₀) := by
    simp [T', PiTensorProduct.lift_symm]
  have hf := (hT.aut v₀).cont
  have hleft := (hT.aut v₀).left
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => T' v₀ (ι.symm x * t)
  have hφ : ∀ x, φ x = T' v₀ (ι.symm (x * ι t)) := fun x => by
    simp only [φ, map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hφc : Continuous φ := by
    have e : φ = fun x => T' v₀ (ι.symm (x * ι t)) := funext hφ
    rw [e]
    exact hf.comp (ι.symm.continuous.comp (continuous_mul_const _))
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    show T' v₀ (ι.symm (γ * y) * t) = T' v₀ (ι.symm y * t)
    rw [map_mul, mul_assoc]
    exact hleft _ (hQ γ hγ) _
  have hae' : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have e : φ = evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
      funext x; simp only [φ, evS, hval]; rfl
    rw [e]; exact hae
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae'
  have hv : T' v₀ = 0 := by
    funext g
    have e := hz (ι (g * t⁻¹))
    simpa [φ] using e
  have hT0 : T' = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ hv
  have : T = PiTensorProduct.lift T' := (PiTensorProduct.lift.apply_symm_apply T).symm
  rw [this, hT0, map_zero]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapEqZeroOfTranslatedEvalAeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  first | exact @GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae | exact GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae | (intros; apply GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslatedEvaluationRowsConjLinearBijection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem star_comp_const_smul_eq_conj_smul {α : Type*} (a : ℂ) (F : α → ℂ) :
    (fun x => star ((a • F) x)) = (starRingEnd ℂ a) • (fun x => star (F x)) := by
  funext x
  simp [star_mul']

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi


set_option maxHeartbeats 2000000 in
theorem evalAll_rows : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  intro hDS hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
  have hnorm : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨c, -, hc⟩ := hConj
    have h1 := (X.low (X.pl.symm τ)).1
    rw [← (c τ).norm_map, hc τ]
    exact h1
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hfun := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hCusp D X h θ S M J χ t hθ hMat
  obtain ⟨f, hf⟩ : ∃ f : MultT θ M J χ → L2X X, ∀ T : MultT θ M J χ, ((f T : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) :=
    ⟨fun T => ((hfun T.1 T.2 (PiTensorProduct.tprod ℂ v₀)).2).toLp _, fun T => MemLp.coeFn_toLp _⟩
  have hmem : ∀ T : MultT θ M J χ, star (f T) ∈ HHX X := fun T =>
    GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj T.1 T.2 (f T) (hf T)
  have hstar : ∀ T : MultT θ M J χ, ((star (f T) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := fun T => by
    filter_upwards [Lp.coeFn_star (f T), hf T] with x h1 h2
    rw [h1, Pi.star_apply, h2]
  have e1 : ∀ T T' : MultT θ M J χ, (fun x => star (evS X h t ((T + T').1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) +
        (fun x => star (evS X h t (T'.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro T T'
    rw [Submodule.coe_add, LinearMap.add_apply]
    funext x
    exact star_add _ _
  have e2 : ∀ (a : ℂ) (T : MultT θ M J χ), (fun x => star (evS X h t ((a • T).1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (starRingEnd ℂ a) • (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro a T
    rw [Submodule.coe_smul, LinearMap.smul_apply]
    generalize T.1 (PiTensorProduct.tprod ℂ v₀) = F
    exact star_comp_const_smul_eq_conj_smul a (evS X h t F)
  let j : MultT θ M J χ →ₗ⋆[ℂ] HHX X :=
    { toFun := fun T => ⟨star (f T), hmem T⟩
      map_add' := fun T T' => by
        apply Subtype.ext
        show star (f (T + T')) = star (f T) + star (f T')
        apply Lp.ext
        refine (hstar (T + T')).trans ?_
        rw [e1]
        exact ((hstar T).add (hstar T')).symm.trans (Lp.coeFn_add _ _).symm
      map_smul' := fun a T => by
        apply Subtype.ext
        rw [Submodule.coe_smul]
        apply Lp.ext
        refine (hstar (a • T)).trans ?_
        rw [e2]
        exact ((hstar T).const_smul (starRingEnd ℂ a)).symm.trans (Lp.coeFn_smul _ _).symm }
  have hj : ∀ T, (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := hstar
  refine ⟨⟨j, ⟨?_, ?_⟩, hj⟩, hnorm⟩
  · rw [injective_iff_map_eq_zero]
    intro T hT
    have h0 : (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] 0 := by
      rw [hT]; exact Lp.coeFn_zero _ _ _
    have hev : evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 := by
      filter_upwards [hj T, h0] with x h1 h2
      rw [h2] at h1
      have h3 := congrArg star h1
      rw [star_star] at h3
      rw [← h3]
      exact star_zero _
    exact Subtype.ext (GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero D X h θ S M J χ t v₀ hθ hne T.1 T.2 hev)
  · intro ψ
    have hψ : star (star (ψ : L2X X)) ∈ HHX X := by rw [star_star]; exact ψ.2
    obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
      (star (ψ : L2X X)) hψ
    refine ⟨⟨T, hT⟩, ?_⟩
    apply Subtype.ext
    apply Lp.ext
    refine (hj ⟨T, hT⟩).trans ?_
    filter_upwards [Lp.coeFn_star (ψ : L2X X), hTe] with x h2 h3
    rw [h2, Pi.star_apply] at h3
    rw [← h3, star_star]

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslatedEvaluationRowsConjLinearBijectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  first | exact @GlobalTheory.Core.Mi.evalAll_rows | exact GlobalTheory.Core.Mi.evalAll_rows | (intros; apply GlobalTheory.Core.Mi.evalAll_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFiniteDatumIsSchwartzBruhatHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFiniteDatumIsSchwartzBruhatHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isSBHalf_stepDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  classical
  intro D S T ΛS ΛT βS βT L χ ξ Z e hS hT _ _ he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ L.Pg
    (fun y => omegaG L χ y * omegaQ ∅ L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' h,
        GlobalTheory.PlaceDatum.omegaQ_congr ∅ L.r ξ 1 y y' fun PP hP => absurd hP (Finset.notMem_empty PP)]

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFiniteDatumIsSchwartzBruhatHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  first | exact @GlobalTheory.ChainOnto.isSBHalf_stepDatum | exact GlobalTheory.ChainOnto.isSBHalf_stepDatum | (intros; apply GlobalTheory.ChainOnto.isSBHalf_stepDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalAtJetMap
open GlobalTheory.KJInf Formalism.L2.Forms Formalism.BasicNotions MvPolynomial

noncomputable section
namespace GlobalTheory.KJInf.ClsVal
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem evalAt_jetLin (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) :
    evalAt y' (Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) Q) =
      Λ (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) = c • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have h1 : Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) (monomial m c) =
        c • monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) := by
      rw [hm, map_smul]
      congr 1
      unfold Formalism.L2.Ker.jetLin
      have := (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ).constr_basis ℂ
        (fun m : ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) →₀ ℕ => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      simpa using this
    rw [h1, evalAt, smul_eval, eval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    have h2 : (∏ i : ι × Fin b × Fin a, (X i : FP ι a b) ^ m (Sum.inr i)) =
        monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, h2, ← map_pow, ← map_prod, algebraMap_eq]
    rw [show ∀ (u v : ℂ) (q : FP ι a b), C u * (C v * q) = (u * v) • q from fun u v q => by rw [smul_eq_C_mul, C_mul, mul_assoc], map_smul, smul_eq_mul]
    simp only [Finsupp.comapDomain_apply]
    ring
  | add p q hp hq => rw [map_add (f := _), evalAt, map_add (f := _), ← evalAt, ← evalAt, hp, hq, map_add (f := _), map_add (f := _)]

theorem evalAt_jetMap (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ) (k : ι → ℕ) (P : PY ι a) :
    evalAt y' (Formalism.L2.Ker.jetMap (fun m => Λ (monomial m 1)) k P) =
      Λ (subY hab y' (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ k τ)) := by
  rw [subY_eq_subD]
  exact evalAt_jetLin y' Λ _

theorem cSpan_eq_VV' {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

end GlobalTheory.KJInf.ClsVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSeminormSubTendstoZeroOfWordsUnif
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSeminormSubTendstoZeroOfWordsUnif
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem eLpNorm_sub_tendsto_of_unif {X : Type} [MeasurableSpace X] (ν : Measure X) (hν : ν Set.univ = 1)
    (g : ℕ → X → ℂ) (f : X → ℂ) (hm : ∀ j, AEStronglyMeasurable (g j - f) ν)
    (h : TendstoUniformly g f Filter.atTop) :
    Filter.Tendsto (fun j => eLpNorm (g j - f) 2 ν) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  filter_upwards [Metric.tendstoUniformly_iff.1 h δ hδ0'] with j hj
  have hb : ∀ᵐ x ∂ν, ‖(g j - f) x‖ ≤ δ := Filter.Eventually.of_forall fun x => by
    have := (hj x).le
    rwa [dist_comm, dist_eq_norm] at this
  refine (eLpNorm_le_of_ae_bound (hm j) hb).trans ?_
  simpa [hν] using hδ.le

theorem wordAct_heisDer_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f - g) =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f - GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih, GlobalTheory.Size.wordAct_cons, GlobalTheory.Size.wordAct_cons, sub_eq_add_neg, sub_eq_add_neg,
      ← neg_one_smul ℂ, ← neg_one_smul ℂ (GlobalTheory.Size.heisDer ψ θ a _)]
    simp only [GlobalTheory.Size.heisDer]
    rw [GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l hf)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Size.theta_word hψ hθ l hg)), GlobalTheory.Size.dRho_smul]

theorem sobO_sub_tendsto_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ u f hf hu hl d
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have key : ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), Filter.Tendsto
      (fun j => GlobalTheory.Size.l2O μ 𝓕 (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j - f))) Filter.atTop (nhds 0) := by
    intro l
    simp only [wordAct_heisDer_sub hψ hθ (hu _) hf l, GlobalTheory.Size.l2O]
    exact eLpNorm_sub_tendsto_of_unif _ (by rw [Measure.restrict_apply_univ]; exact hμ.2.2) _ _
      (fun j => ((GlobalTheory.Size.theta_word hψ hθ l (hu j)).cont.sub
        (GlobalTheory.Size.theta_word hψ hθ l hf).cont).aestronglyMeasurable) (hl l)
  have := tendsto_finsetSum (Finset.range (d + 1)) fun k _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => key (List.ofFn a)
  simp only [Finset.sum_const_zero] at this
  exact this

end GlobalTheory.ThetaDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSeminormSubTendstoZeroOfWordsUnifStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSobolevSeminorm_sub_tendsto_zero_of_words_unif : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  exact GlobalTheory.ThetaDens.sobO_sub_tendsto_zero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PostOnMemEEatOfCenter
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

set_option maxHeartbeats 800000

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

namespace GlobalTheory.MiTop.CentralShift

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem actL_rTr_of_center (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank) (g0 : G0 Ld.Pg Ld.r)
    {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    actL V β Ld g0 (rTr V z f) = rTr V z (actL V β Ld g0 f) := by
  funext x
  show actG0 V β Ld g0 (rTr V z f) x = actG0 V β Ld g0 f (x * z)
  unfold actG0
  split_ifs with hk
  · simp only [rTr]
    rw [mul_assoc x hk.choose z, mul_assoc x z hk.choose, Subgroup.mem_center_iff.mp hz hk.choose]
  · rfl

theorem gaL_rTr_of_center {G : Type} [Group G] [Fintype G] (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 Ld.Pg Ld.r) (c : G → ℂ) {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    gaL V β Ld eG c (rTr V z f) = rTr V z (gaL V β Ld eG c f) := by
  unfold gaL
  funext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, actL_rTr_of_center β Ld _ hz]
  simp [rTr, Finset.sum_apply]

theorem ipM_eq_of_iff (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {T T' U U' : MMap M}
    (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) : ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem map_mul_right_center (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) {z : GA D V}
    (hz : z ∈ Subgroup.center (GA D V)) : Measure.map (fun g => g * z) μ = μ := by
  have e : (fun g : GA D V => g * z) = fun g => z * g := funext fun g => Subgroup.mem_center_iff.mp hz g
  rw [e]
  exact map_mul_left_eq_self μ z

theorem lift_postOn (T : MMap M) (z : GA D V) (v : SmT M) :
    PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) v = rTr V z (PiTensorProduct.lift T v) := by
  have : PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) =
      GlobalTheory.FinTranslate.rTrL V z ∘ₗ PiTensorProduct.lift T := by
    apply PiTensorProduct.ext
    ext w
    simp [postOn, PiTensorProduct.lift.tprod]
  rw [this]
  rfl

end General

section Main

open GlobalTheory.MiTop.CentralShift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end Main

end GlobalTheory.MiTop.CentralShift

namespace GlobalTheory.MiTop

open GlobalTheory.MiTop.CentralShift

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCFrameLat
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.AbsConv

open Filter Set GlobalTheory.Eis

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem enorm_dblIntegrand {D : D7} {V : HSp D} (μ : (AE D)ˣ →* Circle) (E : GA D (dblSp V) → ℂ)
    (f₁ f₂ : GA D V → ℂ) (x : GA D V × GA D V) :
    ‖dblIntegrand V μ E f₁ f₂ x‖ₑ = ‖E (io V x)‖ₑ * (‖f₁ x.1‖ₑ * ‖f₂ x.2‖ₑ) := by
  simp only [dblIntegrand]
  simp_rw [← ofReal_norm_eq_enorm]
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one, Complex.norm_conj,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem dblConv_of_growth {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁)
    (h₂ : GlobalTheory.Grow.RapidDec V f₂) {E : GA D (dblSp V) → ℂ} (hE : LeftInv (GQ (dblSp V)) E) (hc : Continuous E)
    {C : ℝ} {N : ℕ} (hb : ∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) :
    DblConv V μ m E f₁ f₂ := by
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_dblIntegrand hμ hE h₁.1 h₂.1
  have hmeas : AEStronglyMeasurable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) := by
    have e' : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
      funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
    rw [e']
    exact ((continuous_dblIntegrand hμ hc h₁.continuous h₂.continuous).measurable.comp
      (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
  have i₁ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ h₁ N
  have i₂ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ h₂ N
  set K : ℝ := max C 0 * 4 ^ N with hK
  have hK0 : 0 ≤ K := mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨hli, ((i₁.mul_prod i₂).const_mul K).mono' hmeas (Eventually.of_forall fun q => ?_)⟩
  obtain ⟨γ₁, hγ₁, e₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, e₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
      4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
    refine (GlobalTheory.Cont.HeightIo.height_io_le_mul V _ _).trans ?_
    nlinarith
  have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤
      K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) := by
    rw [hinv]
    calc _ ≤ C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N := hb _
      _ ≤ max C 0 * (4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out)) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N)
            (le_max_right _ _)
      _ = _ := by rw [hK, mul_pow, mul_pow]; ring
  have hμ1 : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [dblIntegrandQ, dblIntegrand, norm_mul, hμ1, mul_one, Complex.norm_conj]
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

theorem absConv_unfolded : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle),
    IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s,
    GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V),
    m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ →
    (∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 m → ∑' q : GlobalTheory.Eis.SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) ∧
    GlobalTheory.Eis.DblConv V μ m (GlobalTheory.Eis.eis V φ) f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  have hsS : ∀ g, Summable fun q : SiegelCosets V =>
      ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := fun g => hconvS g
  have heS : ∀ g, ‖eis V (sph V a (s.re : ℂ)) g‖ =
      ∑' q : SiegelCosets V, ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := by
    intro g
    have e : eis V (sph V a (s.re : ℂ)) g = ((∑' q : SiegelCosets V,
        ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun q => by rw [hn]; exact h2 _
    rw [e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hφS : ∀ g, ‖φ g‖ ≤ max C 0 * ‖sph V a (s.re : ℂ) g‖ := fun g =>
    (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))
  have hsφ : ∀ y, Summable fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ :=
    fun y => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hφS _) ((hsS y).mul_left _)
  have hle : ∀ y, ∑' q : SiegelCosets V, ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ ≤
      max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ := fun y => by
    rw [heS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => hφS _) (hsφ y) ((hsS y).mul_left _)
  obtain ⟨B, A, hB⟩ := hgrow
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hSi : LeftInv (GQ (dblSp V)) (eis V (sph V a (s.re : ℂ))) := leftInv_eis (leftInv_of_mem h1 (sph_mem hI _))
  have hSc : Continuous (eis V (sph V a (s.re : ℂ))) := SphConv.continuous_eis hI (sph_mem hI _) hS hσ
  have hconv0 : DblConv V μ m (fun y => (((max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ : ℝ)) : ℂ)) f₁ f₂ := by
    refine dblConv_of_growth hμ hm h₁ h₂ (C := max C 0 * B) (N := A) (fun γ hγ g => ?_)
      (Complex.continuous_ofReal.comp (continuous_const.mul hSc.norm)) (fun g => ?_)
    · beta_reduce
      rw [hSi γ hγ g]
    · rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)
  refine ⟨fun 𝓕 h𝓕 => ?_, ?_⟩
  · have hint := (hconv0.dblInt_eq h𝓕).1
    have hφc : Continuous φ := hφ.2.1
    have hmeas : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
        ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
        ((m.prod m).restrict (𝓕 ×ˢ 𝓕)) := fun q =>
      (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
        h₂.continuous).measurable.enorm.aemeasurable
    rw [← lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top hint.2.ne (lintegral_mono fun x => ?_)
    simp only [enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    simp_rw [← ofReal_norm_eq_enorm]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)),
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsφ _)]
    exact ENNReal.ofReal_le_ofReal (hle _)
  · refine dblConv_of_growth hμ hm h₁ h₂ (leftInv_eis (leftInv_of_mem hμ hφ)) (SphConv.continuous_eis hI hφ hS hs)
      (C := max C 0 * B) (N := A) fun g => ?_
    refine (norm_tsum_le_tsum_norm (hsφ g)).trans ((hle g).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)

end GlobalTheory.Core.Rk.AbsConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEvalAtOfMem
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

section Transport

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}

theorem qdet_map (f : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet (fun a b => f (E a b)) u = f (Formalism.REAL.qdet E u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod,
    List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, apply_ite f, map_zero]

end Transport

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

end GlobalTheory.CapelliUniv
end
end

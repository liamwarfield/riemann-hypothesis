module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTarget

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox

variable {F : Type} [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_schr_negY (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ]
    (x y : κ → AdeleRing (𝓞 F) F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      star (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) (fun u => star (φ u)))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  unfold GlobalTheory.WeilM.thetaSum
  rw [Complex.star_def, Complex.conj_tsum]
  refine tsum_congr fun ξ => ?_
  generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
  simp only [GlobalTheory.WeilM.schr, map_mul, Complex.star_def, Complex.conj_conj, hc, dotProduct_neg, neg_add, mul_neg]

end GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox


open GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox in
theorem GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  intro D ψ hψ S T JA JB ξ hA κ _ co φ₁ h₁ φ₂ h₂
  funext w
  have he : (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co).e w =
      (Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).1 (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).1,
        Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).2
          (-(co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).2)) := rfl
  have hs : ∀ (v : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ v φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun v φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ v φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho]
  rw [he, DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.schr_boxFun_elim,
    DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂), thetaSum_schr_negY ψ hψ.1.2.1]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_doubledCoords_boxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun | exact GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun | (intros; apply GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestrictChar

open Formalism.IndefR.Datum


set_option maxHeartbeats 1000000 in
theorem dbl_diag_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd _ h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ωB, hB⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.ChiGrid.negSp T) χS χT⁻¹
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv hω.hecT) hω.resS
    (resEta_inv hω.resT)
  let d := GlobalTheory.BiTransfer.sumDec T (GlobalTheory.ChiGrid.negSp T)
  have hωd' : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T)) χS (χT * χT⁻¹) ωd := by
    rw [mul_inv_cancel]; exact hωd
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ T (GlobalTheory.ChiGrid.negSp T) d S).om_box χS χT χT⁻¹ ωd ω ωB
    hωd' hω hB 1 h 1 f₁ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂) hf₁ (GlobalTheory.CjNeg.theta_negT hψ hf₂)
  have e1 : d.emb (h, 1) = hd := by
    apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T))
    rw [GlobalTheory.SeesawSumTarget.emb_sumDec, GlobalTheory.SquareComm.mt_blk]
    refine Eq.trans ?_ hhd.symm
    rw [GlobalTheory.Doubling.blkMat, Matrix.reindex_apply, GlobalTheory.AdelicLatMove.mt_one]
  have e2 : ωB ((1 : GA D S), (1 : GA D (GlobalTheory.ChiGrid.negSp T))) = 1 := map_one ωB
  rw [e1, e2, Module.End.one_apply, GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.SeesawSumTarget.boxT_sumDec] at key
  exact key

end GlobalTheory.DblRestrictChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblRestrictChar.dbl_diag_box | exact GlobalTheory.DblRestrictChar.dbl_diag_box | (intros; apply GlobalTheory.DblRestrictChar.dbl_diag_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunDoubledSpaceBoxProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunDoubledSpaceBoxProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.DblBoxTheta

open GlobalTheory.DblBox

theorem isThetaFunO_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
    Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      Formalism.IndefR.Datum.IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (GlobalTheory.DblBox.box f₁ f₂) := by
  intro D ψ hψ S T f₁ f₂ h₁ h₂
  have ctop : Continuous (top : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  have cbot : Continuous (bot : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  let topH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' top top_add
  let botH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' bot bot_add
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    have e₁ : top (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
    have e₂ : bot (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
    simp only [box, top_add, bot_add, symplOH_dbl]
    rw [e₁, e₂, h₁.quasi, h₂.quasi]
    rw [sub_eq_add_neg, neg_add, AddChar.map_add_eq_mul, neg_neg]
    simp only [psi_neg hψ, star_mul', star_star]
    ring
  · obtain ⟨U₁, hU₁o, hU₁⟩ := h₁.level
    obtain ⟨U₂, hU₂o, hU₂⟩ := h₂.level
    refine ⟨U₁.comap topH ⊓ U₂.comap botH, ?_, ?_⟩
    · exact (hU₁o.preimage ctop).inter (hU₂o.preimage cbot)
    · intro u hu hinf
      have hu₁ : top u ∈ U₁ := hu.1
      have hu₂ : bot u ∈ U₂ := hu.2
      have ht : (top u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inl i))) j
      have hb : (bot u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inr i))) j
      rw [heisO_box hψ, hU₁ _ hu₁ ht, hU₂ _ hu₂ hb]
  · exact (h₁.cont.comp ctop).mul ((h₂.cont.comp cbot).star)
  · intro k L hL hfin w
    have hf₁ :=
      h₁.smooth k (topH.comp L) (ctop.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inl i))) j) (top w)
    have hf₂ :=
      h₂.smooth k (botH.comp L) (cbot.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inr i))) j) (bot w)
    exact ContDiff.mul hf₁ (Complex.conjCLE.contDiff.comp hf₂)

end GlobalTheory.DblBoxTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunDoubledSpaceBoxProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFun_doubledSpaceBoxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
    Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      Formalism.IndefR.Datum.IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (GlobalTheory.DblBox.box f₁ f₂) := by
  first | exact @GlobalTheory.DblBoxTheta.isThetaFunO_box | exact GlobalTheory.DblBoxTheta.isThetaFunO_box | (intros; apply GlobalTheory.DblBoxTheta.isThetaFunO_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceBoxProductInnerFactorizes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceBoxProductInnerFactorizes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section

namespace GlobalTheory.DblBoxHaar

open MeasureTheory Pointwise

section Generic

variable {G H : Type} [AddCommGroup G] [AddCommGroup H] [MeasurableSpace G] [MeasurableSpace H]

theorem isAddFundamentalDomain_blocks (e : G ≃ᵐ H × H) (he : ∀ x y, e (x + y) = e x + e y)
    (Γ : AddSubgroup G) (Λ : AddSubgroup H) (h1 : ∀ g ∈ Γ, (e g).1 ∈ Λ) (h2 : ∀ g ∈ Γ, (e g).2 ∈ Λ)
    (h3 : ∀ a ∈ Λ, ∀ b ∈ Λ, e.symm (a, b) ∈ Γ) (μ₁ : Measure H) [SigmaFinite μ₁] (𝓕₁ : Set H)
    (h : IsAddFundamentalDomain Λ 𝓕₁ μ₁) :
    IsAddFundamentalDomain Γ (e ⁻¹' (𝓕₁ ×ˢ 𝓕₁)) ((μ₁.prod μ₁).map e.symm) := by
  let eA : G →+ H × H := AddMonoidHom.mk' e he
  have hneg : ∀ g, e (-g) = -e g := fun g => eA.map_neg g
  have hqmp : Measure.QuasiMeasurePreserving e ((μ₁.prod μ₁).map e.symm) (μ₁.prod μ₁) :=
    ⟨e.measurable.aemeasurable, by rw [MeasurableEquiv.map_map_symm]⟩
  have hvadd : ∀ (g : Γ) (x : G), e (g +ᵥ x) = e g + e x := fun g x => he _ _
  refine ⟨(h.nullMeasurableSet.prod h.nullMeasurableSet).preimage hqmp, ?_, ?_⟩
  · rw [e.symm.measurableEmbedding.ae_map_iff]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae h.ae_covers] with p ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨⟨e.symm (a, b), h3 _ a.2 _ b.2⟩, ?_⟩
    simp only [Set.mem_preimage, hvadd, MeasurableEquiv.apply_symm_apply]
    exact ⟨ha, hb⟩
  · intro g g' hgg'
    have hset : ∀ g : Γ, g +ᵥ e ⁻¹' (𝓕₁ ×ˢ 𝓕₁) = e ⁻¹' (((⟨(e g).1, h1 _ g.2⟩ : Λ) +ᵥ 𝓕₁) ×ˢ ((⟨(e g).2, h2 _ g.2⟩ : Λ) +ᵥ 𝓕₁)) := by
      intro g
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage, Set.mem_prod, hvadd]
      simp only [AddSubgroup.vadd_def, NegMemClass.coe_neg, hneg, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, vadd_eq_add]
    show ((μ₁.prod μ₁).map e.symm) ((g +ᵥ e ⁻¹' (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ e ⁻¹' (𝓕₁ ×ˢ 𝓕₁))) = 0
    rw [hset, hset, ← Set.preimage_inter, Set.prod_inter_prod, MeasurableEquiv.map_apply,
      MeasurableEquiv.symm_preimage_preimage, Measure.prod_prod]
    by_cases hfst : (e g).1 = (e g').1
    · have hsnd : (e g).2 ≠ (e g').2 := fun hs => hgg' (Subtype.ext (e.injective (Prod.ext hfst hs)))
      have := h.aedisjoint (i := ⟨(e g).2, h2 _ g.2⟩) (j := ⟨(e g').2, h2 _ g'.2⟩) (fun hh => hsnd (congrArg Subtype.val hh))
      rw [show μ₁ _ = 0 from this, mul_zero]
    · have := h.aedisjoint (i := ⟨(e g).1, h1 _ g.2⟩) (j := ⟨(e g').1, h1 _ g'.2⟩) (fun hh => hfst (congrArg Subtype.val hh))
      rw [show μ₁ _ = 0 from this, zero_mul]

theorem setIntegral_blocks (e : G ≃ᵐ H × H) (μ₁ : Measure H) [SigmaFinite μ₁] (𝓕₁ : Set H) (f g : H → ℂ) :
    ∫ w in e ⁻¹' (𝓕₁ ×ˢ 𝓕₁), f (e w).1 * star (g (e w).2) ∂((μ₁.prod μ₁).map e.symm) =
      (∫ u in 𝓕₁, f u ∂μ₁) * star (∫ u in 𝓕₁, g u ∂μ₁) := by
  rw [MeasurableEquiv.restrict_map, MeasurableEquiv.symm_preimage_preimage,
    e.symm.measurableEmbedding.integral_map, ← Measure.prod_restrict]
  simp only [MeasurableEquiv.apply_symm_apply, Complex.star_def]
  rw [integral_prod_mul (f := f) (g := fun v => starRingEnd ℂ (g v)), integral_conj]

end Generic

end GlobalTheory.DblBoxHaar

namespace GlobalTheory.DblBoxHaar

open MeasureTheory GlobalTheory.DblBox

variable {D : D7} {S T : HSp D}

theorem continuous_join : Continuous fun p : WO S T × WO S T => join p.1 p.2 := by
  have : Continuous fun p : WO S T × WO S T => Matrix.fromRows p.1 p.2 :=
    continuous_pi fun i => match i with
      | Sum.inl k => (continuous_apply k).comp continuous_fst
      | Sum.inr k => (continuous_apply k).comp continuous_snd
  exact this.matrix_submatrix _ _

def blocks (S T : HSp D) : WO S (GlobalTheory.Doubling.dblSp T) ≃ₜ+ WO S T × WO S T where
  toFun w := (top w, bot w)
  invFun p := join p.1 p.2
  left_inv := join_top_bot
  right_inv p := by simp
  map_add' x y := by simp
  continuous_toFun := (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  continuous_invFun := continuous_join

theorem top_mem {g : WO S (GlobalTheory.Doubling.dblSp T)} (hg : g ∈ ratL (GlobalTheory.Doubling.dblSp T) S) : top g ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hg
  exact ⟨γ.submatrix (finSumFinEquiv ∘ Sum.inl) id, by ext i j; rfl⟩

theorem bot_mem {g : WO S (GlobalTheory.Doubling.dblSp T)} (hg : g ∈ ratL (GlobalTheory.Doubling.dblSp T) S) : bot g ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hg
  exact ⟨γ.submatrix (finSumFinEquiv ∘ Sum.inr) id, by ext i j; rfl⟩

theorem join_mem {u v : WO S T} (hu : u ∈ ratL T S) (hv : v ∈ ratL T S) : join u v ∈ ratL (GlobalTheory.Doubling.dblSp T) S := by
  obtain ⟨γ, rfl⟩ := hu
  obtain ⟨δ, rfl⟩ := hv
  refine ⟨(Matrix.fromRows γ δ).submatrix finSumFinEquiv.symm id, ?_⟩
  ext i j
  simp only [join, Matrix.submatrix_apply, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, id]
  generalize finSumFinEquiv.symm i = s
  rcases s with k | k <;> rfl

end GlobalTheory.DblBoxHaar


open MeasureTheory in
theorem GlobalTheory.DblBoxHaar.box_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D),
    ∃ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T))) (𝓕 : Set (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T)))
      (μ₁ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕₁ : Set (Formalism.IndefR.Datum.WO S T)),
      μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL (GlobalTheory.Doubling.dblSp T) S) 𝓕 μ ∧
      μ₁.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕₁ μ₁ ∧
      ∀ a a' b b' : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T a → Formalism.IndefR.Datum.IsThetaFunO ψ S T a' →
        Formalism.IndefR.Datum.IsThetaFunO ψ S T b → Formalism.IndefR.Datum.IsThetaFunO ψ S T b' →
        ∫ w in 𝓕, GlobalTheory.DblBox.box a b w * star (GlobalTheory.DblBox.box a' b' w) ∂μ =
          (∫ u in 𝓕₁, a u * star (a' u) ∂μ₁) * star (∫ u in 𝓕₁, b u * star (b' u) ∂μ₁) := by
  intro D ψ hψ S T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨j1, j2, j3, j4, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D (GlobalTheory.Doubling.dblSp T) S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO S (GlobalTheory.Doubling.dblSp T)) := ⟨rfl⟩
  obtain ⟨μ₁, 𝓕₁, hμ₁, h𝓕₁, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI := hμ₁
  let e := GlobalTheory.DblBoxHaar.blocks S T
  let eM : WO S (GlobalTheory.Doubling.dblSp T) ≃ᵐ WO S T × WO S T := e.toHomeomorph.toMeasurableEquiv
  refine ⟨(μ₁.prod μ₁).map eM.symm, eM ⁻¹' (𝓕₁ ×ˢ 𝓕₁), μ₁, 𝓕₁, ?_, ?_, hμ₁, h𝓕₁, ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map (μ₁.prod μ₁) e.symm
  · exact GlobalTheory.DblBoxHaar.isAddFundamentalDomain_blocks eM (fun x y => e.map_add x y) _ _
      (fun g hg => GlobalTheory.DblBoxHaar.top_mem hg) (fun g hg => GlobalTheory.DblBoxHaar.bot_mem hg)
      (fun a ha b hb => GlobalTheory.DblBoxHaar.join_mem ha hb) μ₁ 𝓕₁ h𝓕₁
  · intro a a' b b' _ _ _ _
    rw [← GlobalTheory.DblBoxHaar.setIntegral_blocks eM μ₁ 𝓕₁ (fun u => a u * star (a' u)) (fun v => b v * star (b' v))]
    congr 1
    funext w
    change (a (GlobalTheory.DblBox.top w) * star (b (GlobalTheory.DblBox.bot w))) *
      star (a' (GlobalTheory.DblBox.top w) * star (b' (GlobalTheory.DblBox.bot w))) =
      (a (GlobalTheory.DblBox.top w) * star (a' (GlobalTheory.DblBox.top w))) *
        star (b (GlobalTheory.DblBox.bot w) * star (b' (GlobalTheory.DblBox.bot w)))
    simp only [star_mul, star_star]
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceBoxProductInnerFactorizesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D),
    ∃ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T))) (𝓕 : Set (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T)))
      (μ₁ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕₁ : Set (Formalism.IndefR.Datum.WO S T)),
      μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL (GlobalTheory.Doubling.dblSp T) S) 𝓕 μ ∧
      μ₁.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕₁ μ₁ ∧
      ∀ a a' b b' : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T a → Formalism.IndefR.Datum.IsThetaFunO ψ S T a' →
        Formalism.IndefR.Datum.IsThetaFunO ψ S T b → Formalism.IndefR.Datum.IsThetaFunO ψ S T b' →
        ∫ w in 𝓕, GlobalTheory.DblBox.box a b w * star (GlobalTheory.DblBox.box a' b' w) ∂μ =
          (∫ u in 𝓕₁, a u * star (a' u) ∂μ₁) * star (∫ u in 𝓕₁, b u * star (b' u) ∂μ₁) := by
  first | exact @GlobalTheory.DblBoxHaar.box_integral | exact GlobalTheory.DblBoxHaar.box_integral | (intros; apply GlobalTheory.DblBoxHaar.box_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunFamiliesSameHeisenbergInnerEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunFamiliesSameHeisenbergInnerEqSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

open MeasureTheory

noncomputable section
open MeasureTheory

namespace GlobalTheory.ThetaSchurFam

theorem two_families_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ι : Type)
    (X Y : ι → Formalism.IndefR.Datum.WO S T → ℂ) (act : Formalism.IndefR.Datum.WO S T → ι → ι)
    (g : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T), Function.Surjective g →
    (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (X i)) → (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (Y i)) →
    (∀ w i, X (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (X i)) →
    (∀ w i, Y (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (Y i)) →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), μ.IsAddHaarMeasure →
      MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕 μ →
      (∀ i j, ∫ x in 𝓕, X i x * star (X j x) ∂μ = ∫ x in 𝓕, Y i x * star (Y j x) ∂μ) →
      ∃ c : ℂ, ∀ i, X i = c • Y i := by
  intro D ψ hψ S T ι X Y act g hg hX hY hXa hYa μ 𝓕 hμ h𝓕 hI
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hint : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
      Integrable (fun x => f x * star (f' x)) (μ.restrict 𝓕) := fun f f' hf hf' => by
    have hcont : Continuous fun x => f x * star (f' x) := hf.cont.mul hf'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hf hf' hγ w]
    exact hC _ h
  have h1 : ∀ i j x, X i x * star (X j x) = Y i x * star (Y j x) := fun i j x => by
    have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
      (fun γ x => ψ (symplO S T x γ))
      (fun γ => by
        have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
          GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
        simp only [← l4]
        exact hψ.1.1.comp (this.add this))
      (fun γ x y => by
        simp only [← l4, l1, AddChar.map_add_eq_mul]
        ring)
      (fun γ γ' x => by
        simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
        ring)
      (fun x => by
        simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
      (fun γ x => hψ.1.2.1 _)
      (fun x => by
        rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
        exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
      μ 𝓕 hμ h𝓕 (fun x => X i x * star (X j x) - Y i x * star (Y j x))
      (((hX i).cont.mul (hX j).cont.star).sub ((hY i).cont.mul (hY j).cont.star))
      (fun γ hγ x => by
        rw [GlobalTheory.ThetaSchur.prod_periodic hψ (hX i) (hX j) hγ, GlobalTheory.ThetaSchur.prod_periodic hψ (hY i) (hY j) hγ])
      (fun γ => by
        obtain ⟨w, hw⟩ := hg (γ : WO S T)
        have e : (fun x => ψ (symplO S T x γ) * (X i x * star (X j x) - Y i x * star (Y j x))) = fun x =>
            X (act w i) x * star (X j x) - Y (act w i) x * star (Y j x) := by
          funext x
          rw [hXa, hYa, hw, GlobalTheory.ThetaSchur.heisO_rat (hX i) γ.2, GlobalTheory.ThetaSchur.heisO_rat (hY i) γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hX _) (hX j)) (hint _ _ (hY _) (hY j)), hI, sub_self])
    exact sub_eq_zero.1 (congrFun key x)
  have h2 : ∀ i j x y, X i x * star (X j y) = Y i x * star (Y j y) := fun i j x y => by
    obtain ⟨w, hw⟩ := hg (y - x)
    have h := h1 i (act w j) x
    rw [hXa, hYa, hw] at h
    simp only [heisO, add_sub_cancel, star_mul'] at h
    linear_combination ψ (symplOH S T x (y - x)) * h -
      (X i x * star (X j y) - Y i x * star (Y j y)) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T x (y - x))
  by_cases h0 : ∃ j y, Y j y ≠ 0
  · obtain ⟨j, y, hy⟩ := h0
    have e1 := h2 j j y y
    have hn1 : ‖X j y‖ = ‖Y j y‖ := by
      have := congrArg norm e1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : X j y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (X j y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (Y j y) / star (X j y), fun i => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 i j x y, mul_comm]
  · push_neg at h0
    refine ⟨0, fun i => ?_⟩
    funext x
    have e1 := h2 i i x x
    rw [h0 i x, zero_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at e1
    rw [e1, Pi.smul_apply, h0 i x, smul_zero]

end GlobalTheory.ThetaSchurFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunFamiliesSameHeisenbergInnerEqSmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFun_families_same_heisenberg_inner_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ι : Type)
    (X Y : ι → Formalism.IndefR.Datum.WO S T → ℂ) (act : Formalism.IndefR.Datum.WO S T → ι → ι)
    (g : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T), Function.Surjective g →
    (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (X i)) → (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (Y i)) →
    (∀ w i, X (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (X i)) →
    (∀ w i, Y (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (Y i)) →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), μ.IsAddHaarMeasure →
      MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕 μ →
      (∀ i j, ∫ x in 𝓕, X i x * star (X j x) ∂μ = ∫ x in 𝓕, Y i x * star (Y j x) ∂μ) →
      ∃ c : ℂ, ∀ i, X i = c • Y i := by
  first | exact @GlobalTheory.ThetaSchurFam.two_families_scalar | exact GlobalTheory.ThetaSchurFam.two_families_scalar | (intros; apply GlobalTheory.ThetaSchurFam.two_families_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace
open Formalism.IndefR.Datum

noncomputable section

namespace GlobalTheory.DblThetaRestrict

open Formalism.IndefR.Datum GlobalTheory.DblBox MeasureTheory

theorem scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd h hd hh
  have hθ := GlobalTheory.T.isThetaFun_doubledSpaceBoxProduct D ψ hψ S
  have hH := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  let ι : Type := {p : (WO S T → ℂ) × (WO S T → ℂ) // IsThetaFunO ψ S T p.1 ∧ IsThetaFunO ψ S T p.2}
  let X : ι → WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun p => ωd (1, hd) (box p.1.1 p.1.2)
  let Y : ι → WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun p => box (ω (1, h) p.1.1) p.1.2
  let act : WO S (GlobalTheory.Doubling.dblSp T) → ι → ι := fun w p =>
    ⟨(heisO ψ S T (top w) p.1.1, heisO ψ S T (bot w) p.1.2), hH _ _ p.2.1, hH _ _ p.2.2⟩
  let g : WO S (GlobalTheory.Doubling.dblSp T) → WO S (GlobalTheory.Doubling.dblSp T) := actO S (GlobalTheory.Doubling.dblSp T) 1 hd
  have hg : Function.Surjective g := fun y => ⟨actO S (GlobalTheory.Doubling.dblSp T) 1 hd⁻¹ y, by
    simp only [g, actO, inv_one, show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc]
    rw [show Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd * Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd⁻¹ =
      Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) (hd * hd⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) 1 = 1 from rfl, Matrix.one_mul]⟩
  have hbox : ∀ p : ι, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (box p.1.1 p.1.2) := fun p => hθ T _ _ p.2.1 p.2.2
  have hX : ∀ p, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (X p) := fun p => hωd.om_pres _ _ (hbox p)
  have hY : ∀ p, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (Y p) := fun p => hθ T _ _ (hω.om_pres _ _ p.2.1) p.2.2
  have hXa : ∀ w p, X (act w p) = heisO ψ S (GlobalTheory.Doubling.dblSp T) (g w) (X p) := fun w p => by
    show ωd (1, hd) (box (heisO ψ S T (top w) p.1.1) (heisO ψ S T (bot w) p.1.2)) = _
    rw [← heisO_box hψ, hωd.om_heis _ _ _ _ (hbox p)]
  have hYa : ∀ w p, Y (act w p) = heisO ψ S (GlobalTheory.Doubling.dblSp T) (g w) (Y p) := fun w p => by
    show box (ω (1, h) (heisO ψ S T (top w) p.1.1)) (heisO ψ S T (bot w) p.1.2) = _
    rw [hω.om_heis _ _ _ _ p.2.1, heisO_box hψ, top_actO hh, bot_actO hh, actO_one_one]
  obtain ⟨μ, 𝓕, μ₁, 𝓕₁, hμ, h𝓕, hμ₁, h𝓕₁, hprod⟩ := GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes D ψ hψ S T
  have hn : ∀ p q : ι, ∫ x in 𝓕, X p x * star (X q x) ∂μ = ∫ x in 𝓕, Y p x * star (Y q x) ∂μ := fun p q => by
    have e1 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S (GlobalTheory.Doubling.dblSp T) μ 𝓕 hμ h𝓕 (ωd (1, hd))
      (hωd.om_pres _) (hωd.om_unit μ 𝓕 hμ h𝓕 _) _ _ (hbox p) (hbox q)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ₁ 𝓕₁ hμ₁ h𝓕₁ (ω (1, h))
      (hω.om_pres _) (hω.om_unit μ₁ 𝓕₁ hμ₁ h𝓕₁ _) _ _ p.2.1 q.2.1
    show ∫ x in 𝓕, X p x * star (X q x) ∂μ = ∫ x in 𝓕, box (ω (1, h) p.1.1) p.1.2 x * star (box (ω (1, h) q.1.1) q.1.2 x) ∂μ
    rw [e1, hprod _ _ _ _ p.2.1 q.2.1 p.2.2 q.2.2, hprod _ _ _ _ (hω.om_pres _ _ p.2.1) (hω.om_pres _ _ q.2.1) p.2.2 q.2.2, e2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaFun_families_same_heisenberg_inner_eq_smul D ψ hψ S (GlobalTheory.Doubling.dblSp T) ι X Y act g hg hX hY hXa hYa μ 𝓕 hμ h𝓕 hn
  exact ⟨c, fun f₁ f₂ hf₁ hf₂ => hc ⟨(f₁, f₂), hf₁, hf₂⟩⟩

end GlobalTheory.DblThetaRestrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblThetaRestrict.scalar | exact GlobalTheory.DblThetaRestrict.scalar | (intros; apply GlobalTheory.DblThetaRestrict.scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTens
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblRestrict


set_option maxHeartbeats 2000000 in
theorem omp_diag_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  let h : GA D T := ⟨g.1, GlobalTheory.ThetaTransform.mem_GA_target hA g⟩
  let hd : GA D (GlobalTheory.Doubling.dblSp T) := ⟨gd.1, GlobalTheory.ThetaTransform.mem_GA_target rfl gd⟩
  have hh : Formalism.L2.Theta.mt T h = g.1.1 := rfl
  have hhd : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd = gd.1.1 := rfl
  have h1S : Formalism.L2.Theta.mt S 1 = ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))⁻¹).1.1ᵀ := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨hB1, hΘ1⟩ := hom g 1 1 h hh h1S φ₁ hφ₁
  have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨hA1, hΘA⟩ := homp gd 1 1 hd hhd h1S _ hbox
  have hφ₂' := GlobalTheory.ConjSch.star_mem_schA κ φ₂ hφ₂
  have bij := GlobalTheory.ThetaTransform.thetaTr_bij co hψ hA hB hrat
  have bijd := GlobalTheory.ThetaTransform.thetaTr_bij (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) hψ rfl hB
    (GlobalTheory.WeilSchrodinger.DblTarget.coDbl_rat hA co hrat)
  refine bijd.2.1 _ hA1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ hB1 φ₂ hφ₂) ?_
  have e1 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hφ₁ _ hφ₂
  have e2 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hB1 _ hφ₂
  have hgd' : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) := hgd
  have key := GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct D ψ hψ S T χS χT ω hω ωd hωd (GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul D ψ hψ S T χS χT ω hω ωd hωd) h hd hgd' _ _
    ((bij.2.2 _).2 ⟨φ₁, hφ₁, rfl⟩) ((bij.2.2 _).2 ⟨_, hφ₂', rfl⟩)
  refine hΘA.trans ?_
  refine ((congrArg (ωd (1, hd)) e1).trans key).trans ?_
  refine Eq.trans ?_ e2.symm
  rw [hΘ1]

end GlobalTheory.WeilSchrodinger.DblRestrict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTensStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedWeilDatum_doubledTarget_restrict_boxTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun | exact GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun | (intros; apply GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRul
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger.DblTarget

set_option maxHeartbeats 1000000

theorem exists_dbl_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JA))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB) (incM D.host.F JA)
                           (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JB) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) dd χS (GlobalTheory.WeilM.diagCols (Fin T.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  have h1S := isHeckeChar_one (D := D)
  have r1 := resEta_one_dblSp T rT
  obtain ⟨ωd, hωd⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ S (GlobalTheory.Doubling.dblSp T) χS 1 hψ hS h1S rS r1
  have hrat' := coDbl_rat hA co hrat
  obtain ⟨omp, hmp⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (coDbl hA co)
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) omp := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hsg := GlobalTheory.T.siegelRule_transported_weilDatum_doubledTarget D ψ hψ S T χS hS rS JB ξ hB (κ ⊕ κ) (coDbl hA co) hrat' ωd hωd omp hmp
  have t1 := isDblCoord_transD co
  have t2 : GlobalTheory.WeilM.IsLagr (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))
      (GlobalTheory.WeilM.diagCols (Fin T.rank)) := GlobalTheory.WeilM.isLagr_diagCols _ _
  have t4 : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (transD _ (dblRows co)) (GlobalTheory.WeilM.actB _)
      ((omp.comp (MonoidHom.inl _ _)).comp (ugDbl T hA)) :=
    isUSplitting_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA) (isUSplitting_inl hsp)
  have t5 : GlobalTheory.WeilM.SiegelRule _ (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB) _ (transD _ (dblRows co)) χS
      (GlobalTheory.WeilM.diagCols (Fin T.rank)) ((omp.comp (MonoidHom.inl _ _)).comp (ugDbl T hA)) :=
    siegelRule_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA) χS _ hsg
  refine ⟨_, _, t1, ⟨t2, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := GlobalTheory.T.transportedWeilDatum_doubledTarget_restrict_boxTensor D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom ωd hωd omp hmp
    g (ugDbl T hA gd) (by rw [ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]
  exact key

end GlobalTheory.WeilSchrodinger.DblTarget

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JA))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB) (incM D.host.F JA)
                           (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JB) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) dd χS (GlobalTheory.WeilM.diagCols (Fin T.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target | exact GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target | (intros; apply GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target <;> assumption)
end

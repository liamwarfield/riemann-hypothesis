module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXAll

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTPinWrap
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinHyp_at (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (Formalism.L2.SG.Pf.Carrier.sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (j : Fin (nfE D)) (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j))))
    (hH : Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
      (tauE X e j) γ μRv ν) :
    Formalism.L2.SG.Pf.Carrier.CarPinTor.PinHypAt C u u' (e (plE D j)) γ μRv ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH
  refine ⟨h1, h2, ?_, h4, h5⟩
  have key : ∀ j' : Fin (nfE D), j' = (tauE X e).symm (tauE X e j) →
      Formalism.FourierDecayAlt.C6.IsRelevant (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ) →
      Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ) := by
    intro j' hj' h
    rw [Equiv.symm_apply_apply] at hj'
    subst hj'
    rw [towersOf_base] at h
    exact h
  exact key _ rfl h3

end Formalism.L2.SG.Pf.CarrierT
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CutAtHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HaarMeasureTransportInvariant
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotTrHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HaarTrHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EPerpMid
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut

section Fwd

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_spanLt (hT : TrHyp F Qm Qim c) {a : ℕ} {v : Fin n → ℂ} (hv : v ∈ spanLt F.e a) :
    ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qim *ᵥ v) i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro i hi
    rw [Qi_e hT b]
    have hne : i ≠ Formalism.QuantumDeterminants.eI k r b := fun h => by
      have := congrArg Fin.val h; simp only [Formalism.QuantumDeterminants.eI] at this; simp only [Set.mem_setOf_eq] at hb; omega
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hne]
  | zero => intro i _; simp
  | add x y _ _ hx hy => intro i hi; rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  | smul d x _ hx => intro i hi; rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero]

theorem e_perp_mid (hT : TrHyp F Qm Qim c) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) : hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := by
  have he : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he, smul_smul, inv_mul_cancel₀ (c_ne hT a), one_smul]
  have h0 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j = 0 := by
    have ha := a.isLt
    have hsum : a.val + j.val ≠ 2 * r + k := by omega
    unfold Formalism.QuantumDeterminants.Hpk
    simp only [Formalism.QuantumDeterminants.eI, hsum, not_lt.mpr hj1, not_le.mpr ha,
      and_false, false_and, if_false]
  rw [he, PtRepPf.hJ_smul_left, ← herm_Q hT]
  simp only [Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.bvec,
    ← Pi.single_star, star_one, single_dotProduct, Matrix.mulVec_single_one,
    Matrix.col_apply, h0, mul_zero]

theorem fwd_N (hT : TrHyp F Qm Qim c) {g : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hgU : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (hg : InN ε F.e z g) :
    Qim * g * Qm ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hQQ : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qim * g * Qm) i j = (Qim *ᵥ (g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
  refine ⟨?_, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · show (Qim * g * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * g * Qm) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hT.hH]
    calc (Qim * g * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * g * Qm)
        = Qmᴴ * gᴴ * (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) * g * Qm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qmᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Qm := by
          rw [hQQ, hT.h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hgU]
  · rw [hcol, hT.he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply]
    have hsplit : g *ᵥ F.e a = F.e a + (g - 1) *ᵥ F.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.1.1 a) i hi, add_zero, Qi_e hT a,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ (c_ne hT a), one_smul]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  · rw [hcol]
    have hw : ∀ a, hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := fun a => e_perp_mid hT a j hj1 hj2
    have hsplit : g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = Qm *ᵥ Formalism.QuantumDeterminants.bvec j + (g - 1) *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.2 _ hw) i hi, add_zero, Matrix.mulVec_mulVec,
      hT.h1, Matrix.one_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

end Fwd

end Formalism.L2.SG.Pf.Bridge
end
end

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem n_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have h := (PtRepPf.frU X (Classical.arbitrary D.what₂.Word) v).card
  omega

theorem trG_mul_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  unfold trG
  calc C.Qi τ * uMat γ * C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ)
      = C.Qi τ * uMat γ * (C.Q τ * C.Qi τ) * uMat γ⁻¹ * C.Q τ := by simp only [Matrix.mul_assoc]
    _ = C.Qi τ * (uMat γ * uMat γ⁻¹) * C.Q τ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul_inv, Matrix.mul_one, h1]

theorem trG_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (trG (C.Q τ) (C.Qi τ) γ)⁻¹ = trG (C.Q τ) (C.Qi τ) γ⁻¹ :=
  Matrix.inv_eq_right_inv (trG_mul_inv C τ γ)

theorem trG_mul (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (a * b) = trG (C.Q τ) (C.Qi τ) a * trG (C.Q τ) (C.Qi τ) b := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc C.Qi τ * (uMat a * uMat b) * C.Q τ = C.Qi τ * uMat a * (C.Q τ * C.Qi τ) * uMat b * C.Q τ := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem haarTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarTr C u u' τ := by
  intro γ μRv hH
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hT := trHyp_C C u τ
  have hT' := trHyp_C C u' τ
  set f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hf
  have hemb : Topology.IsClosedEmbedding f := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hme : MeasurableEmbedding f := hemb.measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := fun y => y.2

  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ, trG (C.Q τ) (C.Qi τ) y ∈ RStab D.R.k D.R.rS (gB C τ γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hT (hU y) hy1, ?_⟩
    show (trG (C.Q τ) (C.Qi τ) γ)⁻¹ * trG (C.Q τ) (C.Qi τ) y * trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS
    rw [trG_inv, ← trG_mul, ← trG_mul]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hT' (hU _) hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hσ
    exact hme.sigmaFinite_map
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [FunLike.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * s * C.Qi τ) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
        (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hT hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = C.Q τ * ((gB C τ γ)⁻¹ * s * gB C τ γ) * C.Qi τ := by
        rw [trG_inv]
        show uMat (γ⁻¹ * y0 * γ) = C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ * s * (C.Qi τ * uMat γ * C.Q τ)) * C.Qi τ
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (C.Q τ * s * C.Qi τ) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hT' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ f = f ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hf, Formalism.QuantumDeterminants.lmulM]
      rw [trG_mul]
      congr 1
      show s = C.Qi τ * (C.Q τ * s * C.Qi τ) * C.Q τ
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_const_mul y0).measurable, hinv y0 hy0S]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem y_inv_mem (τ : D.what₂.Tau) : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hu := Formalism.L2.SG.Pf.LocJEq.unit_det_y C τ
  show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  conv_lhs => rw [← hy]
  rw [Matrix.conjTranspose_nonsing_inv]
  calc ((C.y τ)ᴴ)⁻¹ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * (C.y τ)⁻¹
      = (((C.y τ)ᴴ)⁻¹ * (C.y τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * (C.y τ)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star),
          Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]


set_option maxHeartbeats 1000000 in
theorem quotTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : QuotTr C u u' τ := by
  intro γ μRv ν hH hq
  obtain ⟨hσ, -, -, -⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  set F : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hF
  have hemb : Topology.IsClosedEmbedding F := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hFm : Measurable F := hemb.continuous.measurable
  set cj : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j with hcjdef
  have hcj : Measurable cj := by
    have : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hSm : Measurable (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ) := (Formalism.L2.SG.Pf.LocJEq.smap_cont C τ γ).measurable
  set y' := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (y_inv_mem C τ)) with hy'
  have hty' : trG (C.Q τ) (C.Qi τ) y' = (C.y τ)⁻¹ := by
    show C.Qi τ * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) * C.Q τ = _
    simp only [← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

  have key : ∀ σ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      (fun i j => (Matrix.of (cj (F σ)) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j) =
        F (γ⁻¹ * (σ * z) * y') := by
    intro σ z
    have hs : Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) = trG (C.Q τ) (C.Qi τ) (γ⁻¹ * z) * (C.y τ)⁻¹ := by
      rw [Formalism.L2.SG.Pf.LocJEq.smap_val]; rfl
    have hgg : trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := trG_mul_inv C τ γ
    have hM : (gB C τ γ)⁻¹ * trG (C.Q τ) (C.Qi τ) σ * gB C τ γ * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) =
        trG (C.Q τ) (C.Qi τ) (γ⁻¹ * (σ * z) * y') := by
      rw [hs, trG_inv, trG_mul, trG_mul, trG_mul, trG_mul, hty']
      calc trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) σ * gB C τ γ *
          (trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) z * (C.y τ)⁻¹)
          = trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) σ *
            (trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹) * trG (C.Q τ) (C.Qi τ) z * (C.y τ)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    funext i j
    exact congrFun (congrFun hM i) j
  intro f hf
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map F) = _
  rw [lintegral_map hf hFm]
  haveI : SigmaFinite μRv := hσ
  have hfm2 : Measurable fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) := by
    refine hf.comp ?_
    have : Continuous fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
      continuous_snd.matrix_mul continuous_fst
    exact this.measurable
  have hinner : Measurable fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂((μRv.map F).map cj) :=
    hfm2.lintegral_prod_right'
  rw [lintegral_map hinner hSm]
  have hin : ∀ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j)
      ∂((μRv.map F).map cj) = ∫⁻ σ, f (F (γ⁻¹ * (σ * z) * y')) ∂μRv := by
    intro z
    have hm3 : Measurable fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        f (fun i j => (Matrix.of s * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j) :=
      hfm2.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_map hm3 hcj]
    rw [lintegral_map (f := fun a => f fun i j => (Matrix.of (cj a) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j)
      (hm3.comp hcj) hFm]
    refine lintegral_congr fun σ => ?_
    rw [key]
  simp only [hin]
  have hg : Measurable fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => f (F (γ⁻¹ * w * y')) :=
    hf.comp (hFm.comp ((continuous_mul_const y').measurable.comp (continuous_const_mul γ⁻¹).measurable))
  rw [← hq _ hg]
  symm
  calc ∫⁻ x, f (F (γ⁻¹ * x * y')) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
      = ∫⁻ x, (fun w => f (F (γ⁻¹ * w))) (x * y') ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by
        simp only [mul_assoc]
    _ = ∫⁻ x, f (F (γ⁻¹ * x)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_mul_right_eq_self (fun w => f (F (γ⁻¹ * w))) y'
    _ = ∫⁻ x, f (F x) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_mul_left_eq_self (fun w => f (F w)) γ⁻¹

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal Pointwise

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

section Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {v : InfinitePlace X.B.I.F} {lam : ℂ}
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}

theorem trHyp_gen (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (PtRepPf.frU X u v) Q Qi (fun a : Fin D.R.rS => lam ^ (D.R.rS - (a : ℕ))) := by
  obtain ⟨h1, h2, hH, hef⟩ := hT
  exact ⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩

theorem trG_mul_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    trG Q Qi (a * b) = trG Q Qi a * trG Q Qi b := by
  obtain ⟨-, h2, -, -⟩ := hT
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc Qi * (uMat a * uMat b) * Q = Qi * uMat a * (Q * Qi) * uMat b * Q := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem trG_inv_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (γ : Formalism.REAL.UJ (X.B.I.ε v)) :
    (trG Q Qi γ)⁻¹ = trG Q Qi γ⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← trG_mul_g hT, mul_inv_cancel]
  obtain ⟨h1, -, -, -⟩ := hT
  show Qi * uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) * Q = 1
  simp [uMat, h1]

theorem transp_mem_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) {m : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Q * m * Qi ∈ UJset (X.B.I.ε v) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := hT
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  show (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi) = Formalism.REAL.Jm (X.B.I.ε v)
  have e1 : (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi) =
      Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * m) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hH, hm', ← hH]
  have e2 : Qiᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * Qi) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

variable (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u u' : D.what₂.Word) (γ : Formalism.REAL.UJ (X.B.I.ε v))
  (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)))
include hT

theorem emb_g : Topology.IsClosedEmbedding
    (fun x : Formalism.REAL.UJ (X.B.I.ε v) => (Matrix.of.symm (trG Q Qi x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
  Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ hT.2.1

theorem haar_measure_transport_invariant (hH : IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v)
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ) μRv) :
    (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) (Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ))ᶜ = 0 ∧
    (∀ a ∈ Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ),
      (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))).map (Formalism.QuantumDeterminants.lmulM a) = μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) ∧
    μRv.map (fun x => Matrix.of.symm (trG Q Qi x)) ≠ 0 := by
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  have h1 := hT.1
  have h2 := hT.2.1
  have hTu := trHyp_gen hT u
  have hTu' := trHyp_gen hT u'
  set F : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun x => Matrix.of.symm (trG Q Qi x) with hF
  have hme : MeasurableEmbedding F := (emb_g hT).measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ,
      trG Q Qi y ∈ Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hTu (hU y) hy1, ?_⟩
    rw [trG_inv_g hT, ← trG_mul_g hT, ← trG_mul_g hT]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hTu' (hU _) hy2
  refine ⟨?_, ?_, ?_⟩
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := transp_mem_g hT hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (Q * s * Qi) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hTu hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = Q * ((trG Q Qi γ)⁻¹ * s * trG Q Qi γ) * Qi := by
        rw [trG_inv_g hT]
        show uMat (γ⁻¹ * y0 * γ) = Q * (Qi * uMat γ⁻¹ * Q * s * (Qi * uMat γ * Q)) * Qi
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (Q * s * Qi) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hTu' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ F = F ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hF, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]
      rw [trG_mul_g hT]
      congr 1
      show s = Qi * (Q * s * Qi) * Q
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_const_mul y0).measurable, hinv y0 hy0S]
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h

theorem fin_g (ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) (hq : IsQuotLoc μRv ν) (K : Set (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
    (hK : IsCompact K) : (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) K < ∞ := by
  have hemb := emb_g hT
  rw [hemb.measurableEmbedding.map_apply]
  set Cc := (fun x : Formalism.REAL.UJ (X.B.I.ε v) => (Matrix.of.symm (trG Q Qi x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ⁻¹' K
  have hC : IsCompact Cc := hemb.isCompact_preimage hK

  have hν : ν ≠ 0 := by
    intro h0
    have h := hq (fun _ => 1) measurable_const
    rw [h0] at h
    simp only [lintegral_const, Measure.coe_zero, Pi.zero_apply, mul_zero, lintegral_zero_measure] at h
    have : Formalism.REAL.muG (X.B.I.ε v) Set.univ = 0 := by simpa using h
    exact (isOpen_univ.measure_pos (Formalism.REAL.muG (X.B.I.ε v)) Set.univ_nonempty).ne' this

  obtain ⟨m, hm⟩ : ∃ m, 0 < ν (compactCovering (Formalism.REAL.UJ (X.B.I.ε v)) m) := by
    by_contra hcon
    push_neg at hcon
    apply hν
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null fun m => nonpos_iff_eq_zero.1 (hcon m)
  set V := compactCovering (Formalism.REAL.UJ (X.B.I.ε v)) m
  have hV : IsCompact V := isCompact_compactCovering _ m
  have hCV : IsCompact (Cc * V) := hC.mul hV
  have hfin : Formalism.REAL.muG (X.B.I.ε v) (Cc * V) < ∞ := hCV.measure_lt_top
  have hmeas : MeasurableSet (Cc * V) := hCV.isClosed.measurableSet
  have hW := hq ((Cc * V).indicator 1) (measurable_one.indicator hmeas)
  rw [lintegral_indicator_one hmeas] at hW
  have hlow : μRv Cc * ν V ≤ ∫⁻ x, (∫⁻ s, (Cc * V).indicator 1 (s * x) ∂μRv) ∂ν := by
    rw [← lintegral_indicator_const (hV.isClosed.measurableSet)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx, ← lintegral_indicator_one hC.isClosed.measurableSet]
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ Cc
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (Set.mul_mem_mul hs hx)]; exact le_rfl
      · rw [Set.indicator_of_notMem hs]; exact bot_le
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  rw [← hW] at hlow
  by_contra hinf
  rw [not_lt, top_le_iff] at hinf
  rw [hinf, ENNReal.top_mul hm.ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hfin) (lt_irrefl _)

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem haarAtC_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarAtC C u u' τ := by
  intro γ μRv ν hP
  obtain ⟨-, -, -, hH, hq⟩ := hP
  have hT := Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)
  obtain ⟨hc, hl, hne⟩ := haar_measure_transport_invariant hT u u' γ μRv hH
  exact ⟨hc, hl, fun K hK => fin_g hT μRv ν hq K hK, hne⟩

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.LocWSOf Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem cutAt_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c :=
  cutAt_of_haar C u u' τ a b ξ ξ' c (haarAtC_holds C u u' τ) A₀ hA hCC

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PinCovCarrierInTc
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinCov_carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (Formalism.L2.SG.Pf.Carrier.sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (Hj : ∀ j : Fin (nfE D),
      ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j)))),
        Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
          (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
          (tauE X e j) γ μRv ν →
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
          Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
          Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
            (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
            (Formalism.L2.SG.Pf.Carrier.CarPinTor.fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (cc j))) :
    Formalism.L2.SG.Pf.Carrier.JointPin.PinCov
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo) := by
  intro v γ μRv ν hH
  obtain ⟨j, rfl⟩ := (tauE X e).surjective v
  have key : ∀ (j' : Fin (nfE D)) (h' : X.pl.symm (e (plE D j')) = tauE X e j),
      (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
        Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
        ((castLoc X u h').toContinuousLinearEquiv.toContinuousLinearMap :
            X.Vloc u (tauE X e j') →L[ℂ] X.Vloc u (tauE X e j)).comp
          ((Formalism.FourierDecayAlt.D.orbJ (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
              (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
              (fcT X C e u u' a b ξ ξ' cc j')).comp
            ((castLoc X u' h').symm.toContinuousLinearEquiv.toContinuousLinearMap :
              X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u' (tauE X e j'))) := by
    intro j' h'
    have hj : j' = j := (tauE X e).injective h'
    subst hj
    rw [towersOf_base, Hj j' γ μRv ν hH]
    ext x
    rfl
  exact key _ (tauE_symm X e (tauE X e j))

end Formalism.L2.SG.Pf.CarrierT
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ac_le (c Cl L : ℝ) (r k f : ℕ) (hCl : 1000 + |c| ≤ Cl) (hf : 2 ≤ f) (hL : 1 / 2 ≤ L) :
    max (c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) 0 ≤
      Cl * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn]
  have hn1 : (1 : ℝ) ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hrn : (r : ℝ) + 1 ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hCl0 : 0 ≤ Cl := by linarith [abs_nonneg c]
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (f : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hf' 5
    norm_num at this
    linarith
  have hP0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) := by positivity
  have hn19 : 0 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := by positivity
  have hP : ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by
    have h1 : ((r : ℝ) + 1) ^ 2 ≤ (2 * (r : ℝ) + k + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hrn 2
    have h2 : (r : ℝ) * (2 * (r : ℝ) + k + 1) + 1 ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 2 := by
      linarith [mul_nonneg hr0 hk0, mul_nonneg hr0 hr0, mul_nonneg hk0 hk0]
    have h3 : (2 * (r : ℝ) + k + 1) ^ 4 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)
        ≤ (2 * (r : ℝ) + k + 1) ^ 2 * (2 * (2 * (r : ℝ) + k + 1) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (2 * (r : ℝ) + k + 1) ^ 4 := by ring
      _ ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by linarith
  have hA : 0 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 := mul_nonneg hCl0 hn19
  have hRHS : 8 * (Cl * (2 * (r : ℝ) + k + 1) ^ 19) ≤
      Cl * (2 * (r : ℝ) + k + 1) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
    have hfl : (32 : ℝ) * (1 / 2) ≤ (f : ℝ) ^ 5 * L := mul_le_mul hf5 hL (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_left hfl hA
    linarith
  apply max_le
  · have hcP : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) ≤
        |c| * (2 * (2 * (r : ℝ) + k + 1) ^ 19) :=
      (mul_le_mul_of_nonneg_right (le_abs_self c) hP0).trans
        (mul_le_mul_of_nonneg_left hP (abs_nonneg c))
    have hcl : |c| * (2 * (r : ℝ) + k + 1) ^ 19 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 :=
      mul_le_mul_of_nonneg_right (by linarith) hn19
    have e : c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) =
        c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) := by ring
    rw [e]
    linarith
  · linarith

end Formalism.L2.SG.Pf.CarrierXAll

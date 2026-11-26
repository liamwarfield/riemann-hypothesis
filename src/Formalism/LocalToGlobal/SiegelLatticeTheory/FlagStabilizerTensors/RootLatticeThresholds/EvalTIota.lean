module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgePlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.DensLow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Eqv Formalism.IndefR
open scoped TensorProduct

namespace Formalism.L2.SG.EvalTIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def uM' (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (v : InfinitePlace D.host.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ := uMat (x.1 v)

def Pi (v : InfinitePlace D.host.F) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (Formalism.IndefR.RationalEmbedding.inst D).P v

theorem P_isUnit_det' (v : InfinitePlace D.host.F) : IsUnit (Pi (D := D) v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)

theorem thetaV_eq_psiT_i (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : (Formalism.IndefR.RationalEmbedding.inst D).φ (Formalism.L2.Host.tauPl D ρ) x = tauE D ρ x := by
      show Formalism.MainNotions.S.embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = _
      rw [Equiv.symm_apply_apply]
      rfl
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem infMat_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig (D.sp.Y 0).gram (thetaC D ρ) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM' x (Formalism.L2.Host.tauPl D ρ) = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (psiT D ρ) *
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT_i ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC_i {M : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : x.1 = 1 ↔ ∀ v, uM' x v = 1 := by
  constructor
  · intro h v
    show uMat (x.1 v) = 1
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ x.1 = 1 := by
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff_i]
  have hc : ∀ ρ, ((matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D)).map (thetaC D ρ) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg_i, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
    have e' : Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM' x (Formalism.L2.Host.tauPl D ρ)
        = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹) * Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC_i
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det' _)]

theorem tauF_eq_i : Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : Lev.finE (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = (x.2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq_i] at hb
  exact hb.symm

theorem iota_symm_mem_GinfC (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) :
    (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GinfC (D.sp.Y 0) ↔ x.2 = 1 := by
  show finHom (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = 1 ↔ _
  rw [Formalism.IndefR.Eqv.finHom_eq_one_iff, finE_brg_i]
  constructor
  · intro e
    exact Subtype.ext e
  · intro e
    rw [e]
    rfl

end Formalism.L2.SG.EvalTIota

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierBridge
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.DFrameBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  P.FromX → P.Base i0 i0' → ∀ γ h h' : X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' γ h h' → ∀ v,
    Formalism.FourierDecayAlt.D.IsDFrame (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v))
      (trG (P.Q v) (P.Qi v) ((h⁻¹ * γ * h') v))

end Formalism.L2.SG.Pf.Carrier
end
end

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

section UMat

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_inv_mul (a : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat a⁻¹ * Formalism.MainNotions.S.uMat a = 1 := by
  simp [Formalism.MainNotions.S.uMat]

theorem uMat_mul_inv (a : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
  simp [Formalism.MainNotions.S.uMat]

theorem uMat_unitary (a : Formalism.REAL.UJ ε) :
    (Formalism.MainNotions.S.uMat a)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat a = Formalism.REAL.Jm ε := a.2

end UMat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem dFrameBridge_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))
    (sc : ℝ) (hsc : sc ≠ 0) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) :
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).DFrameBridge
      sc i0 i0' := by
  intro hFX hB γ h h' hDX v
  obtain ⟨hHu, hH'u, hDv⟩ := hDX
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  obtain ⟨hi, hν, hm⟩ := hB v
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v))
      (fun a => cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
      (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) (fun a => cTor ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hfix : ∀ (w : D.what₂.Word) (s : X.B.I.Ginf), s ∈ HsetU X w →
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).e a = (PtRepPf.frU X w v).e a) ∧
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).fd a = (PtRepPf.frU X w v).fd a) ∧
      Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).z = (PtRepPf.frU X w v).z := by
    intro w s hs
    refine ⟨fun a => hs v _ ?_, fun a => hs v _ ?_, hs v _ ?_⟩
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, rfl⟩)
    · exact Or.inr rfl
  obtain ⟨hHe, hHf, hHz⟩ := hfix u h hHu
  obtain ⟨hH'e, hH'f, hH'z⟩ := hfix u' h' hH'u
  have hD := hDv v
  rw [hi] at hD
  have key := Bridge.bridge_place hTr hTr' hsc (uMat_mul_inv (γ v)) (uMat_unitary (h v)) (uMat_mul_inv (h v))
    (uMat_inv_mul (h v)) hHe hHf hHz (uMat_unitary (h' v)) (uMat_mul_inv (h' v)) (uMat_inv_mul (h' v))
    hH'e hH'f hH'z hD (T ((tauE X e).symm v)).base hz hz' (m₀ ((tauE X e).symm v)) hm
  show Formalism.FourierDecayAlt.D.IsDFrame (T ((tauE X e).symm v)).base (ν' ((tauE X e).symm v)) (m₀ ((tauE X e).symm v))
    (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) * Formalism.MainNotions.S.uMat ((h⁻¹ * γ * h') v) * Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
  rw [show ν' ((tauE X e).symm v) = _ from hν]
  exact key

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTopOf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

open Formalism.L2.SG.RealObj

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem placeTie_ePl : PlaceTie X (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm :=
  fun x => Formalism.L2.SG.Pf.CarrierTop.placeTie_ePl X x

theorem embE_apply (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) (x : X.B.I.E) :
    embE X e j (X.ιE x) = X.B.I.φ (tauE X e j) x := by
  show X.B.I.φ _ (X.ιE.symm (X.ιE x)) = _
  rw [RingEquiv.symm_apply_apply]

variable {X} {u u' : D.what₂.Word}

theorem G_sOf (I : CarrierIn X u u') (j : Fin I.nf) (q : Formalism.FourierDecayAlt.C.LPt) :
    ((sOf I).pd j).G q = Complex.normSq (Formalism.FourierDecayAlt.D.ptLast q).2 - Tw (D := D) u * Tw (D := D) u' := by
  show Complex.normSq _ - Formalism.QuantumDeterminants.Tz I.G.k I.G.r (I.T j).base.z * Formalism.QuantumDeterminants.Tz I.G.k I.G.r (I.T j).base.z' = _
  rw [(I.hT j).1, (I.hT j).2]
  rfl

theorem emb_carrierInOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) :
    ∀ j x, (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).emb j (X.ιE x) =
      X.B.I.φ ((carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).τ j) x :=
  fun j x => embE_apply X e j x


open Matrix in
theorem base_carrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hQ : ∀ v, I.Q v * I.Qi v = 1) (hi : ∀ v, i0 v = i0' v)
    (hν : ∀ j, I.ν' j = I.Qi (I.τ j) *ᵥ X.wfr u' (I.τ j) (i0' (I.τ j)))
    (hm : ∀ j, I.m₀ j = Formalism.L2.SG.Pf.CarrierBase.m0Of X u u' (I.τ j) (I.Q (I.τ j)) (I.Qi (I.τ j))) :
    (CarrierOf I Mo).Base i0 i0' := by
  have h := Formalism.L2.SG.Pf.CarrierBase.baseFromX_of X u u' (sOf I) i0 i0' I.τ I.Q I.Qi hQ hi
  have e1 : I.ν' = fun j => I.Qi (I.τ j) *ᵥ X.wfr u' (I.τ j) (i0' (I.τ j)) := funext hν
  have e2 : I.m₀ = fun j => Formalism.L2.SG.Pf.CarrierBase.m0Of X u u' (I.τ j) (I.Q (I.τ j)) (I.Qi (I.τ j)) := funext hm
  show BaseFromX X (sOf I) u u' i0 i0' I.τ I.Q I.Qi I.ν' I.m₀
  rw [e1, e2]
  exact h

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTEquiv
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sm_stable_uh (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  obtain ⟨gg, rfl⟩ := Formalism.IndefR.Eqv.KerDiag.gt_of_uh τ M hg
  exact Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ gg hw

abbrev comp (a : GA D V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) a


open Classical in
def translS (a : GA D V) (s : Finset D.what₂.Tau) (v : M.Vec) : M.Vec := fun τ =>
  if τ ∈ s then ⟨M.rep τ (comp a τ) (v τ), sm_stable_uh M τ (Formalism.IndefR.Eqv.infMat_unitary' D V a τ) (v τ).2⟩
  else v τ

def transl (a : GA D V) (v : M.Vec) : M.Vec := translS M a Finset.univ v

theorem transl_apply (a : GA D V) (v : M.Vec) (τ : D.what₂.Tau) :
    (transl M a v τ : M.H τ) = M.rep τ (comp a τ) (v τ) := by
  simp [transl, translS]

variable {M}

theorem equiv_ginf {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {T : MMap M}
    (hT : Formalism.IndefR.AutomorphicEvaluation.EqCont θ M T) {a : GA D V} (ha : a ∈ GinfC V) (v : M.Vec) (y : GA D V) :
    T v (y * a) = T (transl M a v) y := by
  classical
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => comp a τ with hgsd
  have hgs : Formalism.IndefR.Eqv.IsUnitFam D V gs := Formalism.IndefR.Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, ∀ y, T v (y * Formalism.IndefR.Eqv.famH D V _ (hu s)) = T (translS M a s v) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu ∅) = 1 := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_one]
        convert Formalism.IndefR.Eqv.famM_one D V using 2
        funext τ
        simp
      have e2 : translS M a ∅ v = v := by
        funext τ; simp [translS]
      rw [e, mul_one, e2]
    | insert τ0 s hτ0 ih =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu (insert τ0 s)) =
          Formalism.IndefR.Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Formalism.IndefR.Eqv.famH D V _ (hu s) := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_mul, Formalism.IndefR.Eqv.matA_atH, Formalism.IndefR.Eqv.matA_famH]
        apply Formalism.IndefR.Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Formalism.IndefR.Eqv.psi_famM, Formalism.IndefR.Eqv.psi_atM, Formalism.IndefR.Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Formalism.IndefR.Eqv.fin_famM, Formalism.IndefR.Eqv.fin_atM, Formalism.IndefR.Eqv.fin_famM,
            Matrix.one_mul]
      rw [e, ← mul_assoc, ih]
      have hw : M.rep τ0 (gs τ0) ((translS M a s v τ0 : M.H τ0)) ∈ M.sm τ0 :=
        sm_stable_uh M τ0 (hgs τ0) (translS M a s v τ0).2
      have hq := hT.equiv τ0 (gs τ0) (hgs τ0) (translS M a s v) ⟨_, hw⟩ rfl
      have hq' := congrFun hq y
      simp only [rTr] at hq'
      rw [Formalism.IndefR.Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)] at hq'
      rw [← hq']
      refine congrFun (congrArg T ?_) y
      funext τ
      by_cases h : τ = τ0
      · subst h
        rw [Function.update_self]
        apply Subtype.ext
        simp [translS, hτ0, hgsd]
      · rw [Function.update_of_ne h]
        simp [translS, h]
  have e : a = Formalism.IndefR.Eqv.famH D V _ (hu Finset.univ) :=
    Formalism.IndefR.Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  conv_lhs => rw [e]
  exact key Finset.univ y

section Read

variable {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Read

end Formalism.L2.SG.EvalTEquiv

end
end

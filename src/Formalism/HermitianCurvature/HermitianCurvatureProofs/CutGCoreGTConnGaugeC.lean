module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

private theorem contDiffOn_ann_of_wirt_fnZ_eq (P : M.Par) {u : ℂ → ℂ} (w : M.Var P.r) (F : ℂ → ℂ)
    (hF : ∀ q : MA.Qp P.r P.TT,
      MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = F q.1.2) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ann P) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ))) (MA.Qset P.r P.TT) :=
    MA.wirt_smooth (fnZ P u).2 w
  let ι : ℂ → MA.E P.r := fun ζ => ((fun _ => (1 : ℂ)), ζ)
  have hι : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ι := contDiff_const.prodMk contDiff_id
  have hmap : Set.MapsTo ι (Ann P) (MA.Qset P.r P.TT) := fun ζ hζ => ⟨fun _ => one_ne_zero, hζ⟩
  refine (hs.comp hι.contDiffOn hmap).congr fun ζ hζ => ?_
  exact (hF ⟨ι ζ, hmap hζ⟩).symm

theorem dZ_smooth (P : M.Par) {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (Ann P)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ u) (Ann P) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb u) (Ann P) :=
  ⟨contDiffOn_ann_of_wirt_fnZ_eq P M.vz _ fun q => wirtinger_derivative_fibre_function P hu q, contDiffOn_ann_of_wirt_fnZ_eq P M.vzb _ fun q => wirt_fnZ_zb P hu q⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem connF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
  have hSm : SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := fun ρ =>
    ⟨(hAB ρ).1.add ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).1),
      (hAB ρ).2.sub ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).2)⟩
  refine ⟨hSm, ?_⟩
  intro Φ ρ
  have hc := conj_smooth (hu ρ).1
  rw [trR_phase P Bs e u hu, trR_phase P Bs e u hu, trR_phase P Bs e u hu, (hC Φ ρ).1, (hC Φ ρ).2]
  set g := trR P Bs e Φ ρ
  constructor
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZ (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vz (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, Pi.mul_apply, Pi.add_apply]
    rw [e1, dzQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).1, fnZ_val P (hSm ρ).1,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).1]
    ring
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzbQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZb (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vzb (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, NegMemClass.coe_neg, Pi.mul_apply,
      Pi.add_apply, Pi.neg_apply]
    rw [e1, dzbQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).2, fnZ_val P (hSm ρ).2,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).2]
    ring


end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfCk
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def retV (g₀ : B.Mat k r) : Set (B.Mat k r) := {Y | IsUnit (g₀⁻¹ * Y + 1).det}

def retDom (g₀ : B.Mat k r) : Set (B.Mat k r) :=
  retV g₀ ∩ (fun Y => prj (iot (g₀⁻¹ * Y))) ⁻¹' {X | IsUnit (1 - X).det}

def ret (g₀ : B.Mat k r) (Y : B.Mat k r) : B.Mat k r := g₀ * kap (prj (iot (g₀⁻¹ * Y)))

lemma isOpen_unitDet {X : Type*} [TopologicalSpace X] {f : X → B.Mat k r} (hf : Continuous f) :
    IsOpen {x | IsUnit (f x).det} := by
  simp_rw [isUnit_iff_ne_zero]
  exact isOpen_ne_fun hf.matrix_det continuous_const

lemma isOpen_retV (g₀ : B.Mat k r) : IsOpen (retV g₀) := isOpen_unitDet ((continuous_const.mul continuous_id).add continuous_const)

lemma cd_iotL (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (fun Y => iot (g₀⁻¹ * Y)) (retV g₀) := by
  have h1 : ContDiffOn ℝ ∞ (fun Y : B.Mat k r => g₀⁻¹ * Y) (retV g₀) := cdm_mul contDiffOn_const contDiffOn_id
  show ContDiffOn ℝ ∞ (fun Y => (g₀⁻¹ * Y - 1) * (g₀⁻¹ * Y + 1)⁻¹) (retV g₀)
  exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun Y hY => hY)

lemma isOpen_retDom (g₀ : B.Mat k r) : IsOpen (retDom g₀) := by
  exact (cdm_prj (cd_iotL g₀)).continuousOn.isOpen_inter_preimage (isOpen_retV g₀)
    (isOpen_unitDet (f := fun X : B.Mat k r => 1 - X) (continuous_const.sub continuous_id))

lemma cd_ret (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (ret g₀) (retDom g₀) := by
  have hA : ContDiffOn ℝ ∞ (fun Y => prj (iot (g₀⁻¹ * Y))) (retDom g₀) :=
    cdm_prj ((cd_iotL g₀).mono Set.inter_subset_left)
  show ContDiffOn ℝ ∞ (fun Y => g₀ * ((1 + prj (iot (g₀⁻¹ * Y))) * (1 - prj (iot (g₀⁻¹ * Y)))⁻¹)) (retDom g₀)
  exact cdm_mul contDiffOn_const
    (cdm_mul (contDiffOn_const.add hA) (cdm_inv (contDiffOn_const.sub hA) fun Y hY => hY.2))

lemma ret_mem {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ retDom g₀) :
    ret g₀ Y ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.B2x8.al_mul_mem hg₀ (kap_mem (prj_lie (iot (g₀⁻¹ * Y))) hY.2)

private lemma prj_eq_self_of_inLie {X : B.Mat k r} (hX : B.inLie k r X) : prj X = X := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
  have h2 : Hpk k r * Xᴴ * Hpk k r = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Ux10.hpk_sq', Matrix.one_mul]
  unfold prj
  rw [h2, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

lemma ret_self {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ B.GV k r)
    (hu : IsUnit (g₀⁻¹ * Y + 1).det) : ret g₀ Y = Y := by
  have hh : g₀⁻¹ * Y ∈ B.GV k r := Formalism.FourierDecayAlt.P.B2x8.al_mul_mem (Formalism.FourierDecayAlt.P.B2x8.al_inv_mem hg₀) hY
  obtain ⟨hl, -, hk⟩ := iot_facts hh hu
  show g₀ * kap (prj (iot (g₀⁻¹ * Y))) = Y
  rw [prj_eq_self_of_inLie hl, hk, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀), Matrix.one_mul]

lemma self_mem_retDom {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : g₀ ∈ retDom g₀ := by
  have e : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀)
  refine ⟨?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1).det
    rw [e, ← two_smul ℂ (1 : B.Mat k r), Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
  · show IsUnit (1 - prj (iot (g₀⁻¹ * g₀))).det
    rw [e, show iot (1 : B.Mat k r) = 0 by simp [iot], prj_zero, sub_zero, Matrix.det_one]
    exact isUnit_one

lemma ret_at {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : ret g₀ g₀ = g₀ := ret_self hg₀ hg₀ (And.left (self_mem_retDom hg₀))

lemma glev0 {g : Mx k r} (hg : g ∈ B.GV k r) : g ∈ Glev k r 0 := by
  refine ⟨hg, ?_⟩
  intro a ha
  simp at ha

theorem smoothLev_of_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : ∀ m : ℕ, CkLev k r 0 m D f) : SmoothLev k r 0 D f := by
  intro g₀ hg₀
  have hG₀ : g₀ ∈ B.GV k r := hg₀.1.1
  have hU : IsOpen (retDom g₀ ∩ ret g₀ ⁻¹' D) :=
    (cd_ret g₀).continuousOn.isOpen_inter_preimage (isOpen_retDom g₀) hD
  refine ⟨retDom g₀ ∩ ret g₀ ⁻¹' D, fun Y => f (ret g₀ Y), hU, ⟨self_mem_retDom hG₀, ?_⟩, ?_, ?_⟩
  · show ret g₀ g₀ ∈ D
    rw [ret_at hG₀]
    exact hg₀.2
  · intro Y hY
    refine ContDiffAt.contDiffWithinAt ?_
    have hr : ContDiffAt ℝ ∞ (ret g₀) Y := (cd_ret g₀).contDiffAt ((isOpen_retDom g₀).mem_nhds hY.1)
    refine contDiffAt_infty.2 fun m => ?_
    have hZ : ret g₀ Y ∈ Glev k r 0 ∩ D := ⟨glev0 (ret_mem hG₀ hY.1), hY.2⟩
    obtain ⟨U, F, hUo, hZU, hF, hfF⟩ := hf m (ret g₀ Y) hZ
    have hc : ContDiffAt ℝ m (fun Y' => F (ret g₀ Y')) Y :=
      (hF.contDiffAt (hUo.mem_nhds hZU)).comp Y (contDiffAt_infty.1 hr m)
    refine hc.congr_of_eventuallyEq ?_
    have h1 : ∀ᶠ Y' in 𝓝 Y, Y' ∈ retDom g₀ := (isOpen_retDom g₀).mem_nhds hY.1
    have h2 : ∀ᶠ Y' in 𝓝 Y, ret g₀ Y' ∈ U := hr.continuousAt.preimage_mem_nhds (hUo.mem_nhds hZU)
    filter_upwards [h1, h2] with Y' h1' h2'
    exact hfF _ h2' (glev0 (ret_mem hG₀ h1'))
  · intro g hg hgl
    show f g = f (ret g₀ g)
    rw [ret_self hG₀ hgl.1 hg.1.1]

end Formalism.FourierDecayAlt.P5.Rad
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceSS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem sliceLoc_zero : SliceLoc P Bs 0 := by
  intro Φ Φ' c c' _ _ _ ζ _
  simp

theorem sliceLoc_add {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T + S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ, hS Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_smul {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (a : ℂ) (hT : SliceLoc P Bs T) :
    SliceLoc P Bs (a • T) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_mul {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T * S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  exact hT (S Φ) (S Φ') c c' hc hc' (hS Φ Φ' c c' hc hc' h) ζ hζ

theorem sliceLoc_sum {ι : Type} (s : Finset ι) (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (hT : ∀ i ∈ s, SliceLoc P Bs (T i)) : SliceLoc P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact sliceLoc_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact sliceLoc_add (hT i (Finset.mem_insert_self _ _)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem sliceLoc_of_smul {T U : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {a : ℂ} (ha : a ≠ 0)
    (hU : U = a • T) (h : SliceLoc P Bs U) : SliceLoc P Bs T := by
  have hTU : T = a⁻¹ • U := by rw [hU, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hTU]
  exact sliceLoc_smul _ h

end closure

open Formalism.FourierDecayAlt.P.NFx4.NO in
theorem second_shift_slice_operator : GTSSLSliceSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT l hl
  have hP := hH.1.1
  have hRel := hH.2.2.2.2.2.1
  have hQQ := hH.2.2.2.2.2.2
  obtain ⟨Qr, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  have hK : ∀ f : M.Ty P → ℂ, SliceLoc P Bs (d.κ f).1 := by
    intro f Φ Φ' c c' hc hc' h ζ hζ
    have e1 := hQ.2.2.2 f Φ ⟨(c, ζ), ⟨hc, hζ⟩⟩
    have e2 := hQ.2.2.2 f Φ' ⟨(c', ζ), ⟨hc', hζ⟩⟩
    simp only at e1 e2
    rw [e1, e2, h ζ hζ]
  have hPj : ∀ ρ, SliceLoc P Bs (Pj d ρ).1 := fun ρ => hK _
  have e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1 := fun Y => by rw [← hQQ Y]; rfl
  have e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1 := fun Y => by rw [← hQQ Y]; rfl
  refine ⟨?_, ?_⟩
  · have hdec : (d.SS l).1 = ∑ a, ∑ b, (Pj d a * d.SS l * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (d.SS l))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l b a
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} b Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hne : M.rho P b i ≠ M.rho P b l :=
          rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by rw [hY] at h0; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 1 0 * (Pj d b).1 = M.xEx P {l} b Y • (Pj d a * d.SS l * Pj d b).1 := by
        have h := congrArg (fstA _) (B1 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e10]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 1 0)) (hPj b))
    · rw [block_zero hRel hUp]
      exact sliceLoc_zero
  · have hdec : (star (d.SS l)).1 = ∑ a, ∑ b, (Pj d a * star (d.SS l) * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (star (d.SS l)))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l a b
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} a Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hil : i ≠ l := fun e => hi'.2 (by simp [e])
        have hup := Formalism.FourierDecayAlt.P.Mx3.rhoUp P l a b hUp i hi'.1
        rw [if_neg hil, add_zero] at hup
        have hne : M.rho P b i ≠ M.rho P b l := rho_ne P hP b hi'.1 hl hil
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by
          rw [hY] at h0; rw [hup]; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 0 1 * (Pj d b).1 = M.xEx P {l} a Y • (Pj d a * star (d.SS l) * Pj d b).1 := by
        have h := congrArg (fstA _) (B4 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e01]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 0 1)) (hPj b))
    · rw [star_block_zero hRel hUp]
      exact sliceLoc_zero

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePhiF
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiMajNonneg
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasSgsPow
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralAdjoint
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointOfIso
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem unit_of_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  obtain ⟨-, h2, -⟩ := PI.WBL.Cv.grpAll k r 0
  exact ⟨(h2 g hg).1, (h2 g hg).2.1⟩

theorem inv_inv_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹⁻¹ = g :=
  Matrix.inv_eq_left_inv (unit_of_uh hg).1

theorem inner_sig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hU : PI.WBL.Cv.SigU σ) {a : Mx k r} (ha : a ∈ UH (Hpk k r)) (u v : H) :
    ⟪σ a u, v⟫_ℂ = ⟪u, σ a⁻¹ v⟫_ℂ := by
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ a : H →ₗ[ℂ] H), norm_map' := hU.2.2 a ha }
  have hai : a⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_inv ha
  have hv : σ a (σ a⁻¹ v) = v := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.2.1 a ha _ hai, (unit_of_uh ha).1, hU.1]; rfl
  calc ⟪σ a u, v⟫_ℂ = ⟪T u, T (σ a⁻¹ v)⟫_ℂ := by
        show ⟪σ a u, v⟫_ℂ = ⟪σ a u, σ a (σ a⁻¹ v)⟫_ℂ
        rw [hv]
    _ = ⟪u, σ a⁻¹ v⟫_ℂ := T.inner_map_map _ _

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem measurePreserving_invM_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (h : B.IsHaarOn (UWset k r z) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) h⟩

theorem mp_inv_N {μ : Measure (Mt k r)} (h : B.IsHaarOn (Nset k r) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) h⟩

end Formalism.FourierDecayAlt.P.S3dx6
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aInt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 a : H) (t : Mx k r) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.2) * ⟪a, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹ * t) w0⟫_ℂ) • π (Matrix.of p.1)

theorem aInt_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 a : H) {t : Mx k r} (ht : t ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p) = aInt z c π σ w0 a t p := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  have hinv : ((Matrix.of p1)⁻¹)⁻¹ = Matrix.of p1 :=
    Matrix.inv_eq_left_inv (PI.WBL.Cv.uh_inv hh).1
  have hmul : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) =
      (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹)).comp (σ t) :=
    hU.2.1 _ (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh).2.2 (PI.WBL.Cv.uh_inv hn).2.2) t ht
  have hpsi := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z c hz (Matrix.of p2) hp2
  show (⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹) (σ t w0)⟫_ℂ *
      star (psi k r z c (Matrix.of p2)⁻¹)) • π ((Matrix.of p1)⁻¹)⁻¹ =
    (psi k r z c (Matrix.of p2) * ⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) w0⟫_ℂ) •
      π (Matrix.of p1)
  rw [hinv, hpsi, hmul, ContinuousLinearMap.comp_apply, mul_comm]

end Formalism.FourierDecayAlt.P.S3dx6
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

end Formalism.FourierDecayAlt.P.S3dx6
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_nonneg (g : Mx k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

end Formalism.FourierDecayAlt.P.S3dx6
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun g : Mt k r => psi k r z c (Matrix.of g) := by
  have hl := B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

attribute [local instance] B7.properFD

end Formalism.FourierDecayAlt.P.S3dx6
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem one_mem_uh : (1 : Mx k r) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_DD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {t : Mx k r} (ht : t ∈ UH (Hpk k r)) : σ t w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨t, ht, rfl⟩

theorem fdeg_of_schur {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} {w0 : H} (hw : w0 ≠ 0) {d : ℝ} (hd : 0 < d)
    (hS : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪w0, w0⟫_ℂ * ⟪w0, w0⟫_ℂ / (d : ℂ)) :
    PI.BesselPeriodGGP.fdegH μG σ w0 = d := by

  have hpt : ∀ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ =
      ((‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [show star ⟪w0, σ (Matrix.of x) w0⟫_ℂ = (starRingEnd ℂ) ⟪w0, σ (Matrix.of x) w0⟫_ℂ from rfl,
      RCLike.mul_conj]
    norm_cast
  simp_rw [hpt] at hS
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hS
  have hI : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have h2 : ((‖w0‖ ^ 4 / d : ℝ) : ℂ) = (‖w0‖ : ℂ) ^ 2 * (‖w0‖ : ℂ) ^ 2 / (d : ℂ) := by
      push_cast; ring
    exact_mod_cast hS.trans h2.symm
  have hw' : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [PI.BesselPeriodGGP.fdegH]
  rw [hI]
  field_simp

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def absTy (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def ThetaC {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : A :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

def GTCCurvPoly : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel → 2 ≤ P.k →
    d.L.TT = (P.TT : ℂ) →
    MAx3.G.PolyIn (fun u => d.QQ u 0 0 - u ^ (P.k + 1) • (1 : A) - u ^ P.k • ThetaC d) (P.k - 1) ∧
    MAx3.G.PolyIn (fun u => d.QQ u 1 0) P.k

def GTCCurvRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (f g : ℂ → A) (Θ : A), 1 ≤ n →
    (∀ u v : ℂ, (u - v) • (f u * g v - g v * f u) = g u * f v - g v * f u) →
    MAx3.G.PolyIn (fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ) (n - 1) →
    MAx3.G.PolyIn g n → ∀ v, Θ * g v - g v * Θ = - g v

def GTCCurvBlock : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel →
    (∀ v : ℂ, ThetaC d * d.QQ v 1 0 - d.QQ v 1 0 * ThetaC d = - d.QQ v 1 0) →
    ∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
      algebraMap ℂ A ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvIdOfCut : Prop := GTCCurvPoly → GTCCurvRTT → GTCCurvBlock → GTCCurvId

theorem gTCCurvId_of_cut : GTCCurvIdOfCut := by
  intro hPo hR hB Wp Wq _ _ _ _ _ _ P Bs X d hyp ρ
  obtain ⟨hPl, hk, -, hAL, -, hRel, hQQ⟩ := hyp
  have hS : Wd.IsStart d.QQ (M.qC P) := by
    have h0 := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X).1
    rwa [show X.QQ = d.QQ from funext hQQ] at h0
  have hTT : d.L.TT = (P.TT : ℂ) := by
    rw [hAL.2.2.2.2.2.2.2.2.2.2.2.2, Formalism.FourierDecayAlt.P.NFx4.TT_eq hPl]
  obtain ⟨h1, h2⟩ := hPo P _ d hRel hk hTT
  have hc := hR _ P.k (fun u => d.QQ u 0 0) (fun u => d.QQ u 1 0) (ThetaC d) (by omega)
    (fun u v => Formalism.FourierDecayAlt.P.NFx4.SX.rtt_ent d hS u v 0 0 1 0) h1 h2
  exact hB P _ d hRel hc ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

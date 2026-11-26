module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SRaiseSNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SsnRepOfOpen2
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepTop
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSEntry
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSEn

theorem coe_sum_apply {r : ℕ} {TT : ℝ} {ι : Type} (s : Finset ι) (g : ι → MA.SmQ r TT) (q : MA.Qp r TT) :
    Subtype.val (∑ i ∈ s, g i) q = ∑ i ∈ s, Subtype.val (g i) q := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

theorem ss_entry_apply (P : M.Par) (l : ℕ) (ρ π' : M.Ty P) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 f) q =
      (if M.Up P l π' ρ then ((Real.sqrt (M.Nrm P l π') : ℝ) : ℂ) else 0) * (f : MA.Qp P.r P.TT → ℂ) q := by
  simp only [MA.SS, Matrix.of_apply]
  split_ifs with h
  · rfl
  · rw [zero_mul]
    rfl

end SSEn

open SSEn in
theorem second_shift_entry_holds : SSn.Rep.Core.SSEntry := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hSSF l hl S hS ζ hζ π ρ
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hA
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hRB := Gauge.GC.radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

  have hsec : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e π q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨((he.1 π).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 π
    · simp [Set.indicator_of_notMem hq]
  obtain ⟨Ψ0, hΨ0, hΨr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsec
  let Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Ψ0, hΨ0⟩
  have hΨ : (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = e π ζ := by
    have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
    have h := congrFun hΨr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
      ((Gauge.GC.trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
        Gauge.rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
    Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (Gauge.GC.radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
  let q : MA.Qp P.r P.TT := ⟨((c0, ζ) : MA.E P.r), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw := Gauge.GC.wRc_ne P hζ

  have e1 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) := by
    refine (congrFun (hv ((d.SS l).1 Ψ) ρ) q).trans ?_
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((((d.SS l).1 Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hS Ψ c0 hc0 ζ hζ, hΨ]

  have e2 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q := by
    refine (congrArg (fun F : M.Ty P → MA.SmQ P.r P.TT => Subtype.val (F ρ) q) (hSSF l hl Ψ).1).trans ?_
    exact coe_sum_apply _ _ _
  have hterm : ∀ π' : M.Ty P, Subtype.val (Gauge.GC.trR P Bs e Ψ π') q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (if π' = π then 1 else 0) := by
    intro π'
    rw [congrFun (hv Ψ π') q]
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e π' ζ))
      (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hΨ, (he.2 ζ hζ).2.1 π' π]
  have e3 : ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q =
      (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) * ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) := by
    simp only [ss_entry_apply, hterm]
    rw [Finset.sum_eq_single π (fun π' _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ π) h)]
    simp
  have h2 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) *
        (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) := by
    rw [← e1, e2, e3, mul_comm]
  exact mul_left_cancel₀ hw h2

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSF
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFKap
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

open Classical

theorem lagrange_all {T : Type} [Fintype T] (K : (T → ℂ) → Prop) (hc : ∀ c : ℂ, K fun _ => c)
    (hadd : ∀ f g, K f → K g → K (f + g)) (hmul : ∀ f g, K f → K g → K (f * g))
    (x : T → ℂ) (hx : K x) (hinj : Function.Injective x) : ∀ f, K f := by
  classical
  have hsum : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∑ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.sum_empty]
      exact hc 0
    · intro a s ha ih hg
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  have hprod : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∏ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.prod_empty]
      exact hc 1
    · intro a s ha ih hg
      rw [Finset.prod_insert ha]
      exact hmul _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  intro f
  have key : f = ∑ t, (fun _ : T => f t) *
      ∏ s ∈ Finset.univ.erase t, ((x + fun _ : T => -x s) * fun _ : T => (x t - x s)⁻¹) := by
    funext u
    simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.add_apply]
    rw [Finset.sum_eq_single u]
    · rw [Finset.prod_eq_one, mul_one]
      intro s hs
      have hne : x u - x s ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hinj h).symm)
      rw [← sub_eq_add_neg, mul_inv_cancel₀ hne]
    · intro t _ htu
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm htu, Finset.mem_univ u⟩), mul_zero]
      rw [add_neg_cancel, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ u) h
  rw [key]
  exact hsum _ _ _ fun t _ => hmul _ _ (hc _) (hprod _ _ _ fun s _ => hmul _ _ (hadd _ _ hx (hc _)) (hc _))

section main

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

theorem quadratic_kappa_identity : GQKap := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hQ
  obtain ⟨hpl, hL, -, -, -⟩ := hA
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := by
    intro Φ
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm
  have hTT : 0 ≤ P.TT := (mul_pos hP.T_pos hP.T'_pos).le
  haveI : Fact ((MA.DQ P).Laws P.TT) := ⟨Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT⟩
  have hx : ∀ Y : ℝ, Intw P Bs e (d.κ fun ρ => M.xC P ρ (Y : ℂ)) (MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ)) := by
    intro Y
    have h1 := intw_mul hsm hGGi (hQ Y 1 1)
    have e1 : d.L.GGi * d.QQ (Y : ℂ) 1 1 = d.κ fun ρ => M.xC P ρ (Y : ℂ) := by
      show d.L.GGi * (d.L.GG * d.x (Y : ℂ)) = _
      rw [← mul_assoc, d.L.GGi_GG, one_mul]; rfl
    have e2 : MA.ggiA P (MA.DQ P) * MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ) := by
      show MA.ggiA P (MA.DQ P) * (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ)) = _
      rw [← mul_assoc, Formalism.FourierDecayAlt.P.MAx1.D5.ggi_gg, one_mul]; rfl
    rw [e1, e2] at h1; exact h1
  obtain ⟨Y₀, hinj⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hP
  refine lagrange_all (fun f => Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) ?_ ?_ ?_ _ (hx Y₀) hinj
  · intro c
    have e1 : d.κ (fun _ => c) = algebraMap ℂ _ c := d.κ.commutes c
    have e2 : MA.kap P (MA.DQ P) (fun _ => c) = algebraMap ℂ _ c := (MA.kap P (MA.DQ P)).commutes c
    show Intw P Bs e (d.κ (fun _ => c)) (MA.kap P (MA.DQ P) (fun _ => c))
    rw [e1, e2]; exact intw_alg hsm c
  · intro f g hf hg
    show Intw P Bs e (d.κ (f + g)) (MA.kap P (MA.DQ P) (f + g))
    rw [map_add (f := _), map_add (f := _)]; exact intw_add hsm hf hg
  · intro f g hf hg
    show Intw P Bs e (d.κ (f * g)) (MA.kap P (MA.DQ P) (f * g))
    rw [map_mul, map_mul]; exact intw_mul hsm hf hg

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFBridge
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

theorem quadratic_transfer_identity : GQBridge := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg Y a b Φ
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hΦ : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φ.2
  have hF : Gauge.FamR P Bs (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    refine ⟨Qx5.isOpen_OpR P.k P.r Bs.z Bs.z', fun c _ => Qx8.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_, ?_⟩
    · exact (Gauge.GC.GT.sec_pt P Bs hpl q).1.2.2
    · exact NFx1.TC.radSp_fam hΦ
    · intro c hc
      exact Qx8.slice_FF hz hz' hΦ hc
  have h := hg (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) hF Y a b
  funext ρ
  show MA.toSm P (Gauge.rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ')) ρ
  refine Eq.trans ?_ (h ρ)
  congr 1
  funext q
  unfold Gauge.rawR
  rw [X.t_apply (Y : ℂ) a b Φ _ (Gauge.GC.GT.sec_pt P Bs hpl q).1]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFSS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

section gen

variable {P : M.Par} {A : Type} [Ring A] [Algebra ℂ A]

def pj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (ρ : M.Ty P) : A := κ fun σ => if σ = ρ then 1 else 0

variable (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (S : ℕ → A)

theorem kap_pj (h : M.Ty P → ℂ) (ρ : M.Ty P) : κ h * pj κ ρ = h ρ • pj κ ρ := by
  unfold pj
  rw [← map_mul, ← map_smul]
  congr 1
  funext σ
  by_cases hσ : σ = ρ
  · subst hσ; simp
  · simp [hσ]

theorem pj_kap (h : M.Ty P → ℂ) (ρ : M.Ty P) : pj κ ρ * κ h = h ρ • pj κ ρ := by
  unfold pj
  rw [← map_mul, ← map_smul]
  congr 1
  funext σ
  by_cases hσ : σ = ρ
  · subst hσ; simp
  · simp [hσ]

theorem pj_mul_ne {ρ σ : M.Ty P} (h : ρ ≠ σ) : pj κ ρ * pj κ σ = 0 := by
  unfold pj
  rw [← map_mul, ← map_zero κ]
  congr 1
  funext τ
  by_cases h1 : τ = ρ
  · subst h1; simp [h]
  · simp [h1]

theorem sum_pj : ∑ ρ, pj κ ρ = 1 := by
  unfold pj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_one κ]
  congr 1
  funext σ
  simp [Finset.sum_apply]

theorem decomp' (a : A) : a = ∑ ρ', ∑ ρ, pj κ ρ' * a * pj κ ρ := by
  calc a = 1 * a * 1 := by rw [one_mul, mul_one]
    _ = (∑ ρ', pj κ ρ') * a * (∑ ρ, pj κ ρ) := by rw [sum_pj κ]
    _ = ∑ ρ', ∑ ρ, pj κ ρ' * a * pj κ ρ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      rw [Finset.mul_sum]

def Rai : Prop := ∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → κ g * S l = S l * κ f

def RaiS : Prop := ∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → S l * κ g = κ f * S l

theorem rai_ind {l : ℕ} {ρ' : M.Ty P} :
    ∀ σ τ, M.Up P l σ τ → (fun τ : M.Ty P => if τ = ρ' then (1 : ℂ) else 0) τ =
      (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) σ := by
  intro σ τ hU
  by_cases h : τ = ρ'
  · subst h; simp [hU]
  · have h2 : ¬ M.Up P l σ ρ' := by
      intro h2
      apply h
      funext i
      exact Fin.ext ((hU i).trans (h2 i).symm)
    simp [h, h2]

theorem blk_zero (hR : Rai κ S) {l : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P l ρ ρ') : pj κ ρ' * S l * pj κ ρ = 0 := by
  have h1 : pj κ ρ' * S l = S l * κ (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) :=
    hR l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) rai_ind
  rw [h1, mul_assoc, kap_pj]
  simp [h]

theorem blk_zeroS (hR : RaiS κ S) {l : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P l ρ ρ') : pj κ ρ * S l * pj κ ρ' = 0 := by
  have h1 : S l * pj κ ρ' = κ (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) * S l :=
    hR l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) rai_ind
  rw [mul_assoc, h1, ← mul_assoc, pj_kap]
  simp [h]

private theorem ne_and_unique_index_of_up {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P}
    (hU : M.Up P l ρ ρ') : ρ ≠ ρ' ∧ ∀ j, j ≠ l → ¬ M.Up P j ρ ρ' := by
  rw [Finset.mem_Icc] at hl
  obtain ⟨i, hi⟩ : ∃ i : Fin (P.k - 1), (i : ℕ) + 1 = l := ⟨⟨l - 1, by omega⟩, show l - 1 + 1 = l by omega⟩
  have h1 := hU i
  rw [if_pos hi] at h1
  refine ⟨fun h => ?_, fun j hj h2 => ?_⟩
  · subst h
    omega
  · have h3 := h2 i
    rw [if_neg (by omega)] at h3
    omega

theorem projected_block_lower_sum (hR : Rai κ S) {B : A} (hB : ∀ f, Commute (κ f) B) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) :
    pj κ ρ' * (B + ∑ j ∈ Finset.Icc 1 (P.k - 1), S j * κ (fun π => M.xEx P {j} π Y)) * pj κ ρ =
      M.xEx P {l} ρ Y • (pj κ ρ' * S l * pj κ ρ) := by
  obtain ⟨hne, hoth⟩ := ne_and_unique_index_of_up hl hU
  have hc : pj κ ρ' * B = B * pj κ ρ' := (hB _).eq
  have hB0 : pj κ ρ' * B * pj κ ρ = 0 := by
    rw [hc, mul_assoc, pj_mul_ne κ (Ne.symm hne), mul_zero]
  have hterm : ∀ j, pj κ ρ' * (S j * κ (fun π => M.xEx P {j} π Y)) * pj κ ρ =
      M.xEx P {j} ρ Y • (pj κ ρ' * S j * pj κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (κ _), kap_pj, mul_smul_comm]
  rw [mul_add, add_mul, hB0, zero_add, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single l]
  · intro j _ hjl
    rw [blk_zero κ S hR (hoth j hjl), smul_zero]
  · intro h
    exact absurd hl h

theorem projected_block_upper_sum (hR : RaiS κ S) {B : A} (hB : ∀ f, Commute (κ f) B) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) :
    pj κ ρ * (B + ∑ j ∈ Finset.Icc 1 (P.k - 1), κ (fun π => M.xEx P {j} π Y) * S j) * pj κ ρ' =
      M.xEx P {l} ρ Y • (pj κ ρ * S l * pj κ ρ') := by
  obtain ⟨hne, hoth⟩ := ne_and_unique_index_of_up hl hU
  have hc : pj κ ρ * B = B * pj κ ρ := (hB _).eq
  have hB0 : pj κ ρ * B * pj κ ρ' = 0 := by
    rw [hc, mul_assoc, pj_mul_ne κ hne, mul_zero]
  have hterm : ∀ j, pj κ ρ * (κ (fun π => M.xEx P {j} π Y) * S j) * pj κ ρ' =
      M.xEx P {j} ρ Y • (pj κ ρ * S j * pj κ ρ') := by
    intro j
    rw [← mul_assoc, pj_kap, smul_mul_assoc, smul_mul_assoc]
  rw [mul_add, add_mul, hB0, zero_add, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single l]
  · intro j _ hjl
    rw [blk_zeroS κ S hR (hoth j hjl), smul_zero]
  · intro h
    exact absurd hl h

def yl (l : ℕ) (ρ : M.Ty P) : ℝ := -M.rho P ρ l

private theorem lo_le_rho_and_rho_le_hi (hP : P.OK) {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ P.k - 1) (ρ : M.Ty P) :
    P.lo m ≤ M.rho P ρ m ∧ M.rho P ρ m ≤ P.hi m := by
  have hg := hP.gap m (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have h3 : ((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) ≤ P.wid m := by
    have h4 := (ρ ⟨m - 1, by omega⟩).isLt
    have e : m - 1 + 1 = m := by omega
    simp only [Fin.val_mk, e] at h4
    omega
  have hw : (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ P.hi m - P.lo m := by
    calc (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ (P.wid m : ℝ) := by exact_mod_cast h3
      _ ≤ P.hi m - P.lo m := Nat.floor_le (by linarith)
  have h0 : (0 : ℝ) ≤ (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold M.rho
  rw [dite_eq_left ⟨h1, h2⟩]
  constructor <;> linarith

private theorem hi_succ_lt_lo (m : ℕ) : P.hi (m + 1) < P.lo m := by
  unfold M.Par.hi M.Par.lo
  have h1 := min_le_left (P.u (m + 1)) (P.u' (m + 1))
  have h2 := le_max_left (P.u (m + 1)) (P.u' (m + 1))
  linarith

private theorem hi_le_hi_of_le (hP : P.OK) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ P.k - 1) :
    P.hi b ≤ P.hi a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    have hg := hP.gap n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h1 := hi_succ_lt_lo (P := P) n
    have h2 := ih (by omega)
    linarith

private theorem rho_lt_rho_of_lt (hP : P.OK) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ P.k - 1) (ρ : M.Ty P) :
    M.rho P ρ b < M.rho P ρ a := by
  have h1 := (lo_le_rho_and_rho_le_hi hP (by omega) hb ρ).2
  have h2 := hi_le_hi_of_le hP (a := a + 1) (b := b) (by omega) (by omega) hb
  have h3 := hi_succ_lt_lo (P := P) a
  have h4 := (lo_le_rho_and_rho_le_hi hP ha (by omega) ρ).1
  linarith

private theorem rho_ne_rho_of_ne (hP : P.OK) {l i : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    (hi : i ∈ Finset.Icc 1 (P.k - 1)) (hil : i ≠ l) (ρ : M.Ty P) : M.rho P ρ i ≠ M.rho P ρ l := by
  rw [Finset.mem_Icc] at hl hi
  rcases Nat.lt_or_gt_of_ne hil with h | h
  · exact ne_of_gt (rho_lt_rho_of_lt hP hi.1 h hl.2 ρ)
  · exact ne_of_lt (rho_lt_rho_of_lt hP hl.1 h hi.2 ρ)

theorem xEx_yl_ne (hP : P.OK) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    M.xEx P {l} ρ ((yl l ρ : ℝ) : ℂ) ≠ 0 := by
  unfold M.xEx yl
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
  have hne := rho_ne_rho_of_ne hP hl hi.1 hi.2 ρ
  intro h
  apply hne
  have h' : ((-(M.rho P ρ l) + M.rho P ρ i : ℝ) : ℂ) = 0 := by exact_mod_cast h
  have h'' := Complex.ofReal_eq_zero.mp h'
  linarith

theorem ss_expand (hR : Rai κ S) (hP : P.OK) (T B : ℂ → A) (hB : ∀ Y f, Commute (κ f) (B Y))
    (hT : ∀ Y, T Y = B Y + ∑ j ∈ Finset.Icc 1 (P.k - 1), S j * κ (fun π => M.xEx P {j} π Y))
    {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    S l = ∑ ρ', ∑ ρ, if M.Up P l ρ ρ' then
      (M.xEx P {l} ρ ((yl l ρ : ℝ) : ℂ))⁻¹ • (pj κ ρ' * T ((yl l ρ : ℝ) : ℂ) * pj κ ρ) else 0 := by
  conv_lhs => rw [decomp' κ (S l)]
  refine Finset.sum_congr rfl fun ρ' _ => Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs with hU
  · rw [hT, projected_block_lower_sum κ S hR (hB _) hl hU, smul_smul, inv_mul_cancel₀ (xEx_yl_ne hP hl ρ), one_smul]
  · exact blk_zero κ S hR hU

theorem ssS_expand (hR : RaiS κ S) (hP : P.OK) (T B : ℂ → A) (hB : ∀ Y f, Commute (κ f) (B Y))
    (hT : ∀ Y, T Y = B Y + ∑ j ∈ Finset.Icc 1 (P.k - 1), κ (fun π => M.xEx P {j} π Y) * S j)
    {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    S l = ∑ ρ, ∑ ρ', if M.Up P l ρ ρ' then
      (M.xEx P {l} ρ ((yl l ρ : ℝ) : ℂ))⁻¹ • (pj κ ρ * T ((yl l ρ : ℝ) : ℂ) * pj κ ρ') else 0 := by
  conv_lhs => rw [decomp' κ (S l)]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  split_ifs with hU
  · rw [hT, projected_block_upper_sum κ S hR (hB _) hl hU, smul_smul, inv_mul_cancel₀ (xEx_yl_ne hP hl ρ), one_smul]
  · exact blk_zeroS κ S hR hU

end gen

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
  (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

theorem intw_zero : Gauge.GC.Intw P Bs e 0 0 := by
  intro Φ
  have h0 : Gauge.GC.trR P Bs e 0 = 0 := by
    have h := Gauge.GC.trR_smul hsm (0 : ℂ) 0
    rwa [zero_smul, zero_smul] at h
  rw [Gauge.actA_zero]
  exact h0

theorem intw_smul' (c : ℂ) {X : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' : MA.A P (MA.DQ P)}
    (h : Gauge.GC.Intw P Bs e X X') : Gauge.GC.Intw P Bs e (c • X) (c • X') := by
  intro Φ
  rw [Gauge.GC.actA_smulM, ← h Φ, ← Gauge.GC.trR_smul hsm]
  rfl

private theorem intw_add' {X Y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' Y' : MA.A P (MA.DQ P)}
    (hX : Gauge.GC.Intw P Bs e X X') (hY : Gauge.GC.Intw P Bs e Y Y') :
    Gauge.GC.Intw P Bs e (X + Y) (X' + Y') := by
  intro Φ
  rw [Gauge.actA_add, ← hX Φ, ← hY Φ, ← Gauge.GC.trR_add hsm]
  rfl

theorem intw_sum' {ι : Type} (s : Finset ι) (X : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (X' : ι → MA.A P (MA.DQ P)) (h : ∀ i ∈ s, Gauge.GC.Intw P Bs e (X i) (X' i)) :
    Gauge.GC.Intw P Bs e (∑ i ∈ s, X i) (∑ i ∈ s, X' i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ?_) (fun a t hat ih h => ?_)
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact intw_zero hsm
  · rw [Finset.sum_insert hat, Finset.sum_insert hat]
    exact intw_add' hsm (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intw_ite' (c : Prop) [Decidable c] {X : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' : MA.A P (MA.DQ P)}
    (h : c → Gauge.GC.Intw P Bs e X X') : Gauge.GC.Intw P Bs e (if c then X else 0) (if c then X' else 0) := by
  split_ifs with hc
  · exact h hc
  · exact intw_zero hsm

end intw

private theorem intw_mul' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
    {X Y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' Y' : MA.A P (MA.DQ P)}
    (hX : Gauge.GC.Intw P Bs e X X') (hY : Gauge.GC.Intw P Bs e Y Y') :
    Gauge.GC.Intw P Bs e (X * Y) (X' * Y') := by
  intro Φ
  rw [Gauge.actA_mul, ← hY Φ, ← hX]
  all_goals rfl

private theorem commute_algHom_of_functions {T A' : Type} [Ring A'] [Algebra ℂ A'] (κ' : (T → ℂ) →ₐ[ℂ] A') (f g : T → ℂ) :
    Commute (κ' f) (κ' g) := by
  show κ' f * κ' g = κ' g * κ' f
  rw [← map_mul, mul_comm, map_mul]

private theorem raiS_star_of_rai_of_star_comm {P : M.Par} {A' : Type} [Ring A'] [StarRing A'] [Algebra ℂ A']
    (κ' : (M.Ty P → ℂ) →ₐ[ℂ] A') (S' : ℕ → A') (hR : Rai κ' S')
    (hst : ∀ f, star (κ' f) = κ' (fun ρ => star (f ρ))) : RaiS κ' (fun l => star (S' l)) := by
  intro l f g hfg
  have h := hR l (fun ρ => star (f ρ)) (fun ρ => star (g ρ))
    (fun ρ ρ' hU => by show star (g ρ') = star (f ρ); rw [hfg ρ ρ' hU])
  have h2 := congrArg star h
  rw [star_mul, star_mul, hst, hst] at h2
  simpa using h2

private theorem commute_kap_diagonal {P : M.Par} (f : M.Ty P → ℂ) (v : M.Ty P → (MA.DQ P).Pr) :
    Commute (MA.kap P (MA.DQ P) f) (Matrix.diagonal v) := by
  have hk : MA.kap P (MA.DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (f π) := by
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk]
  show Matrix.diagonal _ * Matrix.diagonal v = Matrix.diagonal v * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

private theorem rai_kap_SS_DQ {P : M.Par} : Rai (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) := by
  intro l f g hfg
  have hk : ∀ h : M.Ty P → ℂ,
      MA.kap P (MA.DQ P) h = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (h π) := by
    intro h
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk, hk]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [MA.SS, Matrix.of_apply]
  split_ifs with hU
  · rw [hfg π π' hU, Algebra.commutes]
  · simp

theorem quadratic_shift_identity : GQSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct e hF hQQ hκ l hl
  obtain ⟨hPl, -, -, hRel, -⟩ := hAct
  have hP : P.OK := hPl.1
  have hsm := Gauge.GC.radial_space_smoothness Wp Wq P Bs hPl hk e hF
  have hpj : ∀ ρ : M.Ty P, Gauge.GC.Intw P Bs e (pj d.κ ρ) (pj (MA.kap P (MA.DQ P)) ρ) :=
    fun ρ => hκ _
  have hfn : ∀ f (g : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
      g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} → Commute (d.κ f) g :=
    fun f g hg => hRel.2.1 f g hg
  have hdB : ∀ (Y : ℂ) f, Commute (d.κ f) (d.L.GG * d.x Y * d.L.l0 Y) := by
    intro Y f
    have hl0 : Commute (d.κ f) (d.L.l0 Y) := by
      show Commute (d.κ f) (-d.L.nab - algebraMap ℂ _ (Y + 1 / 2) * (d.L.ζb * d.L.GGi))
      exact (hfn f d.L.nab (by simp)).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
        ((hfn f d.L.ζb (by simp [R.LevelData.fns])).mul_right (hfn f d.L.GGi (by simp [R.LevelData.fns]))))
    exact ((hfn f d.L.GG (by simp [R.LevelData.fns])).mul_right
      (commute_algHom_of_functions d.κ f (fun ρ => M.xC P ρ Y))).mul_right hl0
  have hdB' : ∀ (Y : ℂ) f, Commute (d.κ f) (d.L.GG * d.x Y * d.L.m0 Y) := by
    intro Y f
    have hm0 : Commute (d.κ f) (d.L.m0 Y) := by
      show Commute (d.κ f) (-d.L.nabs - algebraMap ℂ _ (Y - 1 / 2) * (d.L.ζ * d.L.GGi))
      exact (hfn f d.L.nabs (by simp)).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
        ((hfn f d.L.ζ (by simp [R.LevelData.fns])).mul_right (hfn f d.L.GGi (by simp [R.LevelData.fns]))))
    exact ((hfn f d.L.GG (by simp [R.LevelData.fns])).mul_right
      (commute_algHom_of_functions d.κ f (fun ρ => M.xC P ρ Y))).mul_right hm0
  have hmB : ∀ (Y : ℂ) f, Commute (MA.kap P (MA.DQ P) f)
      (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.l0A P (MA.DQ P) Y) := by
    intro Y f
    have hl0 : Commute (MA.kap P (MA.DQ P) f) (MA.l0A P (MA.DQ P) Y) := by
      show Commute _ (-MA.nabA P (MA.DQ P) - algebraMap ℂ _ (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
      exact (commute_kap_diagonal f _).neg_right.sub_right
        ((Algebra.commute_algebraMap_right _ _).mul_right
          ((commute_kap_diagonal f _).mul_right
            (commute_kap_diagonal f _)))
    exact ((commute_kap_diagonal f _).mul_right
      (commute_algHom_of_functions (MA.kap P (MA.DQ P)) f (fun π => M.xC P π Y))).mul_right hl0
  have hmB' : ∀ (Y : ℂ) f, Commute (MA.kap P (MA.DQ P) f)
      (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.m0A P (MA.DQ P) Y) := by
    intro Y f
    have hm0 : Commute (MA.kap P (MA.DQ P) f) (MA.m0A P (MA.DQ P) Y) := by
      show Commute _ (-MA.nabsA P (MA.DQ P) - algebraMap ℂ _ (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
      exact (commute_kap_diagonal f _).neg_right.sub_right
        ((Algebra.commute_algebraMap_right _ _).mul_right
          ((commute_kap_diagonal f _).mul_right
            (commute_kap_diagonal f _)))
    exact ((commute_kap_diagonal f _).mul_right
      (commute_algHom_of_functions (MA.kap P (MA.DQ P)) f (fun π => M.xC P π Y))).mul_right hm0
  have hRm : Rai (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) := rai_kap_SS_DQ
  have hRSm : RaiS (MA.kap P (MA.DQ P)) (fun l => star (MA.SS P (MA.DQ P) l)) := by
    first
    | exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift (P := P) (D := MA.DQ P) l f g h
    | exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift P (MA.DQ P) l f g h
    | exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift P l f g h
    | exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => Formalism.FourierDecayAlt.P.MAx1.D5.star_kap (P := P) (D := MA.DQ P) f)
    | exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => Formalism.FourierDecayAlt.P.MAx1.D5.star_kap P (MA.DQ P) f)
    | exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => by
        have hk : ∀ h : M.Ty P → ℂ,
            MA.kap P (MA.DQ P) h = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (h π) := fun h => rfl
        rw [hk, hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
        congr 1
        funext π
        first
        | (rw [starRingEnd_apply, algebraMap_star_comm])
        | exact (algebraMap_star_comm (f π)).symm
        | simp [Algebra.algebraMap_eq_smul_one, star_smul]
        | (simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]; rfl))
  refine ⟨?_, ?_⟩
  · have e1 := ss_expand d.κ d.SS hRel.2.2.2.1 hP (fun Y => d.QQ Y 1 0)
      (fun Y => d.L.GG * d.x Y * d.L.l0 Y) hdB (fun Y => rfl) hl
    have e2 := ss_expand (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) hRm hP (fun Y => MA.QQr P (MA.DQ P) Y 1 0)
      (fun Y => MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.l0A P (MA.DQ P) Y) hmB (fun Y => rfl) hl
    rw [e1, e2]
    refine intw_sum' hsm _ _ _ fun a _ => intw_sum' hsm _ _ _ fun b _ =>
      intw_ite' hsm _ fun _ => intw_smul' hsm _ ?_
    exact intw_mul' (intw_mul' (hpj a) (hQQ (yl l b) 1 0)) (hpj b)
  · have e3 := ssS_expand d.κ (fun l => star (d.SS l)) (raiS_star_of_rai_of_star_comm d.κ d.SS hRel.2.2.2.1 hRel.1) hP
      (fun Y => d.QQ Y 0 1) (fun Y => d.L.GG * d.x Y * d.L.m0 Y) hdB' (fun Y => rfl) hl
    have e4 := ssS_expand (MA.kap P (MA.DQ P)) (fun l => star (MA.SS P (MA.DQ P) l))
      hRSm hP
      (fun Y => MA.QQr P (MA.DQ P) Y 0 1)
      (fun Y => MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.m0A P (MA.DQ P) Y) hmB' (fun Y => rfl) hl
    rw [show star (d.SS l) = _ from e3, show star (MA.SS P (MA.DQ P) l) = _ from e4]
    refine intw_sum' hsm _ _ _ fun a _ => intw_sum' hsm _ _ _ fun b _ =>
      intw_ite' hsm _ fun _ => intw_smul' hsm _ ?_
    exact intw_mul' (intw_mul' (hpj a) (hQQ (yl l a) 0 1)) (hpj b)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem quadratic_second_shift_form : SSn.Rep.Core.GQQSSF :=
  SSn.Rep.Core.GQ.gQQSSF_of_cut SSn.Rep.Core.GQ.quadratic_transfer_identity SSn.Rep.Core.GQ.quadratic_kappa_identity SSn.Rep.Core.GQ.quadratic_shift_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsmS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

theorem theta_constancy_assembly_scalar : ThConstOfCutS := by
  intro hPR hMC hLN hPF
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw'
  have main : ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) := by
    intro π ρ hup
    obtain ⟨n, q, hq⟩ := hPR Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    obtain ⟨c₁, c₂, hc⟩ := hMC Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    have hGG : ∀ ζ ∈ Gauge.GC.Ann P, (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) ≠ 0 := by
      intro ζ hζ
      have : (0 : ℝ) < Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      exact pow_ne_zero _ (by exact_mod_cast this.ne')
    by_cases hc2 : c₂ = 0
    · refine ⟨0, fun ζ hζ Xf hXf hfix => ?_⟩
      have hB0 := (hc ζ hζ Xf hXf hfix).2
      rw [hc2, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hB0
      have hB0' := tc_hsVec_eq_zero hB0
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hB0', smul_zero] at h1
      rw [zero_smul]
      exact (smul_eq_zero.1 h1).resolve_left (hGG ζ hζ)
    ·
      have hTT : 0 ≤ P.TT := by
        have := hAct.1.1
        exact mul_nonneg this.T_pos.le this.T'_pos.le
      have hmod : ∀ x : ℝ, 0 < x → Complex.normSq (q.eval (x : ℂ)) = (c₁ / c₂) * (x - 0) ^ (2 * (2 * n)) := by
        intro x hx
        have hxx : 0 ≤ x ^ 2 + P.TT := by positivity
        set ζ : ℂ := ((Real.sqrt (x ^ 2 + P.TT) : ℝ) : ℂ) with hζdef
        have hnz : Complex.normSq ζ = x ^ 2 + P.TT := by
          rw [hζdef, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hxx]
        have hζ : ζ ∈ Gauge.GC.Ann P := by
          show P.TT < Complex.normSq ζ
          rw [hnz]; nlinarith
        have hgg : Complex.normSq ζ - P.TT = x ^ 2 := by rw [hnz]; ring
        have hsq : Real.sqrt (Complex.normSq ζ - P.TT) = x := by rw [hgg, Real.sqrt_sq hx.le]
        obtain ⟨Xf, hXf, hfix, hne⟩ := hLN Wp Wq P Bs hAct.1 hk Pr hPr π ζ hζ
        obtain ⟨hS1, hB1⟩ := hc ζ hζ Xf hXf hfix
        have h1 := congrArg (fun w => ‖B.hsVec w‖ ^ 2) (hq ζ hζ Xf hXf hfix)
        simp only [tc_hsVec_smul, norm_smul, mul_pow] at h1
        rw [hS1, hB1, hsq, hgg] at h1
        have hX : 0 < ‖B.hsVec Xf‖ ^ 2 := by
          have : B.hsVec Xf ≠ 0 := fun h0 => hne (tc_hsVec_eq_zero h0)
          positivity
        have hnq : ‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 = Complex.normSq (q.eval (x : ℂ)) := by
          rw [Complex.normSq_eq_norm_sq]
        have hng : ‖((x ^ 2 : ℝ) : ℂ) ^ n‖ ^ 2 = (x - 0) ^ (2 * (2 * n)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), ← pow_mul,
            ← pow_mul, sub_zero]
          ring_nf
        rw [hng] at h1
        have h2 : (‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 * c₂ - (x - 0) ^ (2 * (2 * n)) * c₁) * ‖B.hsVec Xf‖ ^ 2 = 0 := by
          linear_combination (-1 : ℝ) * h1
        have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX.ne')
        rw [← hnq, div_mul_eq_mul_div, eq_div_iff hc2]
        linarith [h3]
      obtain ⟨c, hcq⟩ := hPF q (2 * n) 0 (c₁ / c₂) hmod
      refine ⟨c, fun ζ hζ Xf hXf hfix => ?_⟩
      have h1 := hq ζ hζ Xf hXf hfix
      have hpos : 0 ≤ Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      have hev : q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) =
          c * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) := by
        rw [hcq]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
          Complex.ofReal_zero, sub_zero]
        rw [pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hpos]
      rw [hev, mul_comm, mul_smul] at h1
      exact smul_right_injective _ (hGG ζ hζ) h1
  classical
  refine ⟨fun π => if h : ∃ ρ, M.Up P l π ρ then (main π h.choose h.choose_spec).choose else 0, ?_⟩
  intro ζ hζ π ρ hup Xf hXf hfix
  have hex : ∃ ρ, M.Up P l π ρ := ⟨ρ, hup⟩
  have hρ : hex.choose = ρ := tc_up_unique hex.choose_spec hup
  simp only [dif_pos hex]
  have := (main π hex.choose hex.choose_spec).choose_spec ζ hζ Xf hXf hfix
  subst hρ
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepPolyFinish
open Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

theorem pf_conj_eval' (q : ℂ[X]) (x : ℝ) :
    (q.map (starRingEnd ℂ)).eval (x : ℂ) = starRingEnd ℂ (q.eval (x : ℂ)) := by
  rw [Polynomial.eval_map]
  have hx : (x : ℂ) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  conv_lhs => rw [hx]
  exact Polynomial.eval₂_at_apply _ _

theorem pf_id (q : ℂ[X]) (n : ℕ) (a C : ℝ)
    (h : ∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) :
    q * q.map (starRingEnd ℂ) = Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n) := by
  have hroots : Set.Infinite {z : ℂ | IsRoot (q * q.map (starRingEnd ℂ) -
      Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n)) z} := by
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((a + 1 + m : ℝ) : ℂ)) ?_ ?_
    · intro s t hst
      have := Complex.ofReal_injective hst
      exact_mod_cast (by linarith : (s : ℝ) = t)
    · intro m
      simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      have hx : a < a + 1 + (m : ℝ) := by have := m.cast_nonneg (α := ℝ); linarith
      rw [pf_conj_eval', Complex.mul_conj, h _ hx]
      push_cast
      ring
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hroots)

theorem polynomial_finish_holds : PolyFinish := by
  intro q n a C h
  have hid := pf_id q n a C h
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hqb : q.map (starRingEnd ℂ) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
  have hC : (C : ℂ) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0, zero_mul] at hid
    exact mul_ne_zero hq hqb hid
  have hroot : ∀ b ∈ q.roots, b = (a : ℂ) := by
    intro b hb
    have hb0 : q.eval b = 0 := (Polynomial.mem_roots hq).1 hb
    have := congrArg (Polynomial.eval b) hid
    simp only [eval_mul, hb0, zero_mul, eval_C, eval_pow, eval_sub, eval_X] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left hC
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h2).1
  have hcard : Multiset.card q.roots = q.natDegree := by
    first
      | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits q)).symm
      | exact IsAlgClosed.card_roots_eq_natDegree
  have hrep : q.roots = Multiset.replicate q.natDegree (a : ℂ) := by
    rw [← hcard]; exact Multiset.eq_replicate.2 ⟨rfl, hroot⟩
  have hform : q = Polynomial.C q.leadingCoeff * (X - Polynomial.C (a : ℂ)) ^ q.natDegree := by
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [hrep, Multiset.map_replicate, Multiset.prod_replicate]
  have hdeg : q.natDegree = n := by
    have h1 := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hq hqb, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _),
      Polynomial.natDegree_C_mul hC, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at h1
    omega
  exact ⟨q.leadingCoeff, by rw [← hdeg]; exact hform⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_open2 (hPE : PRho.PRhoExists) (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open hPE theta_facts_hold hMC hLN hPoly

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem modular_constancy_holds : ModConst :=
  modConst_of_cut line_nonvanishing_holds line_at_most_one_holds datum_transitivity_holds s_raise_section s_norm_section
    Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.theta_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_polyS (h : Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open2 rho_projection_existence Core.TC.MC.modular_constancy_holds Core.TC.line_nonvanishing_holds (Or.inr h)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_polyS (hJ : JfSmoothDS) (h : JA.SSn.Rep.Core.TC.PolyRadialS) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_SSnRep hJ (JA.SSn.Rep.ssnRep_of_polyS h)

end Formalism.FourierDecayAlt.P.CutMP

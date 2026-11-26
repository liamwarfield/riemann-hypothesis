module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def xD (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

def IsSCoef {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq) : Prop :=
  ∀ (s : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → ∀ g ∈ C6.domL p.T.base ∅,
    ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-s) : ℝ) : ℂ) •
        p.Θ.Θ w e (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') g =
      ∑ q : Fin (Q + 1), ((s ^ (q : ℕ) : ℝ) : ℂ) • B.opApply (L q) F g

def NFUnfoldTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), w ≠ [] →
    D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      topD p H w c = (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c))) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2

def NFVMul : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (φ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt), D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) γ = ((φ (TBB.Gp p γ) : ℝ) : ℂ) • p.V F γ

def NFCutSup : Prop :=
  ∀ χ : ℝ → ℝ, C6.IsCut0 χ → ∀ q : ℕ, ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 0 < x →
    |(xD^[q] (fun y => χ (y / ε))) x| ≤ K

def NFLeibV : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ w, KB.CutWord P p.l0 w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq),
        (∀ q, B.SmoothCoef (C6.domL p.T.base ∅) (L q)) ∧ IsSCoef p w e Q L ∧
        ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
          B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
            p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
              ∑ q : Fin (Q + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L q) F) γ

def NFEmptyOps : Prop :=
  ∃ C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ), ∃ Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th₀ ∧ NFOpOK C₁ p N Th₁ ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g

theorem unfolding_top_term_holds : NFUnfoldTop := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hw hloc _
  have hn : TBB.normC (fun _ => 1) w = 1 := by
    simp [TBB.normC]
  have hRR : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w (TBB.bigPt P.r c) (TBB.bigPt P.r c) := by
    rw [KB.Pl.RR, D.RRplace, dite_eq_left ⟨hloc, hloc⟩, dite_eq_right (Nat.not_succ_le_self _), if_pos rfl, if_neg hw]
  show (TBB.NP p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re = _
  rw [TBB.NP, hn, div_one, hRR, Top.topOf, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hsq : ∀ v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 :=
    fun v => by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [Complex.re_ofReal_mul, B.hsInner, hsq]
  simp only [TBB.TTp, KB.Pl.V]
  ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolTop
namespace Formalism.FourierDecayAlt.P.CutBP.PolTop

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_integrand_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (a b : ℂ) (p : B.SS k r) :
    D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) p =
      a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p := by

  unfold D.orbIntegrand B.rho
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]

theorem orbJ_linear_of_decay : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₁) Bs.μSS →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₂) Bs.μSS →
      (∀ p, Bs.inSS p → ‖H₁ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₂ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) → ∀ a b : ℂ,
      D.orbJ Bs γ (D.muR Bs γ w) (fun g => a • H₁ g + b • H₂ g) =
        a • D.orbJ Bs γ (D.muR Bs γ w) H₁ + b • D.orbJ Bs γ (D.muR Bs γ w) H₂ := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d := ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ,
    Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G c hc hGm hGb =>
    Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)
  have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G c hc hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G c hc hGm hGb⟩
    unfold D.orbJ
    rw [dif_pos hex]
    exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G c hc hGm hGb)
  have hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) =
      fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p :=
    funext fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS := by
    rw [hlin]
    exact (hm₁.const_smul a).add (hm₂.const_smul b)
  have hc' : 0 ≤ (‖a‖ + ‖b‖) * cF := mul_nonneg (by positivity) hcF
  have hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤
      (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by
    intro p hp
    have h1 := hb₁ p hp
    have h2 := hb₂ p hp
    calc ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ ‖a‖ * ‖H₁ (B.sgs p γ)‖ + ‖b‖ * ‖H₂ (B.sgs p γ)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring
  have i₁ := hInt H₁ cF hcF hm₁ hb₁
  have i₂ := hInt H₂ cF hcF hm₂ hb₂
  rw [hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]
  have e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) =
      fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p) := by
    funext p
    rw [smul_add, smul_comm (θ p) a, smul_comm (θ p) b]
  have j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS := i₁.smul a
  have j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS := i₂.smul b
  rw [e, integral_add j₁ j₂, integral_smul, integral_smul]

theorem vector_valued_orbital_linear : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      ContinuousOn H₁ (B.GPos Bs) → ContinuousOn H₂ (B.GPos Bs) →
      (∀ g ∈ B.GPos Bs, ‖H₁ g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₂ g‖ ≤ cF * B.gN g ^ (-A)) →
      ∀ a b : ℂ, D.vecV Bs ν' m₀ (fun g => a • H₁ g + b • H₂ g) q =
        a • D.vecV Bs ν' m₀ H₁ q + b • D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := orbJ_linear_of_decay
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF
        (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂)
        (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b
    · simp only [dif_neg h']
      simp
  · simp only [dif_neg h]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP.PolTop

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem ckOn_of_polyOp {d : ℕ} {A : B.Mat k r → (Wq' →L[ℂ] Wq)} (hA : PolyOp d A) : B.CkOn ⊤ (B.GV k r) A := by
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  have hconst : ∀ i, B.CkOn ⊤ (B.GV k r) (fun _ : B.Mat k r => L i) := fun i _ _ =>
    ⟨Set.univ, fun _ => L i, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hterm : ∀ i, B.CkOn ⊤ (B.GV k r) (fun g => c i g • L i) := fun i =>
    (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (Wp := Wq) (Wq := Wq') (hc i)).1 _ (hconst i)
  have hsum : ∀ s : Finset (Fin n), B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, c i g • L i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩
    | insert a s ha ih =>
      have e : (fun g => ∑ i ∈ insert a s, c i g • L i) = (fun g => c a g • L a) + fun g => ∑ i ∈ s, c i g • L i := by
        funext g; simp [Finset.sum_insert ha]
      rw [e]; exact Formalism.FourierDecayAlt.P.B4.ckOn_add (hterm a) ih
  have e : A = fun g => ∑ i, c i g • L i := funext hAe
  rw [e]; exact hsum Finset.univ

end poly

structure ShiftAt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp n₀ Ap
  polyM : PolyOp n₀ Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAt.iNp ShiftAt.iIp ShiftAt.iFp ShiftAt.iNm ShiftAt.iIm ShiftAt.iFm

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2OperatorBoundHolds
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def bcE (r : ℕ) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last r)).trans MeasurableEquiv.prodComm

theorem bcE_apply (r : ℕ) (c : Fin (r + 1) → ℂ) : bcE r c = ((fun j => c j.castSucc), c (Fin.last r)) := by
  ext j <;> simp [bcE, MeasurableEquiv.piFinSuccAbove_apply] <;> rfl

theorem bcE_mp (r : ℕ) : MeasurePreserving (bcE r) volume volume := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := Measure.pi fun _ : Fin r => (volume : Measure ℂ))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r))
  exact h

theorem ae_ne_zero_all (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ a, c a ≠ 0 := by
  exact ae_all_iff.2 fun a => Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

private theorem ptEntry_map_one_eq_ite_getD (L : List ℂ) :
    ∀ a b : ℕ, D.ptEntry (L.map fun t => ((1 : ℕ), t)) a b = if a = b then L.getD a 0 else 0 := by
  induction L with
  | nil => intro a b; simp [D.ptEntry]
  | cons t L ih =>
    intro a b
    rcases a with _ | a <;> rcases b with _ | b <;> simp [D.ptEntry, ih]

private theorem ptMatN_bigPt_eq_diagonal (r n : ℕ) (c : Fin (r + 1) → ℂ) :
    D.ptMatN (TBB.bigPt r c) n = Matrix.diagonal fun i : Fin n => (List.ofFn c).getD i 0 := by
  have hb : TBB.bigPt r c = (List.ofFn c).map fun t => ((1 : ℕ), t) := by
    simp [TBB.bigPt, List.map_ofFn, Function.comp_def]
  ext a b
  rw [D.ptMatN, hb, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Fin.val_inj]

private theorem ofFn_getD_eq_apply {m : ℕ} (c : Fin m → ℂ) (j : ℕ) (hj : j < m) :
    (List.ofFn c).getD j 0 = c ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem Gp_bigPt_eq (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ i, c i) - TBB.TTp p * Complex.normSq (∏ i : Fin P.r, c i.castSucc) := by
  simp only [TBB.Gp, D.ptG, ptMatN_bigPt_eq_diagonal, Matrix.det_diagonal]
  have h1 : ∀ i : Fin (P.r + 1), (List.ofFn c).getD i 0 = c i := fun i => ofFn_getD_eq_apply c i i.isLt
  have h2 : ∀ i : Fin P.r, (List.ofFn c).getD i 0 = c i.castSucc := fun i =>
    ofFn_getD_eq_apply c i (by omega)
  simp only [h1, h2]

private theorem isLocPt_bigPt_of_ne_zero (r : ℕ) (c : Fin (r + 1) → ℂ) (hd : ∀ a, c a ≠ 0) :
    D.IsLocPt (TBB.bigPt r c) (r + 1) := by
  refine ⟨fun b hb => ?_, ?_⟩
  · rw [TBB.bigPt, List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨le_rfl, hd l⟩
  · simp [D.ptSize, TBB.bigPt, List.map_ofFn, Function.comp_def]
    omega

private theorem bcWeight_eq_zero_of_normSq_le {k r : ℕ} (hk : 2 ≤ k) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ)
    (hq : Complex.normSq q.2 ≤ T * T') : bcWeight k r T T' q = 0 := by
  unfold bcWeight
  split_ifs with h
  · have h0 : Complex.normSq q.2 - T * T' = 0 := by linarith
    rw [h0, zero_pow (by omega), mul_zero]
  · rfl

private theorem gp_bigPt_eq_normSq_prod_mul_sub (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    TBB.Gp p (TBB.bigPt P.r c) = Complex.normSq (∏ i : Fin P.r, c i.castSucc) *
      (Complex.normSq (c (Fin.last P.r)) - TBB.TTp p) := by
  rw [Gp_bigPt_eq, Fin.prod_univ_castSucc, Complex.normSq_mul]
  ring

theorem ew_eq_weight (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r)) *
        ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2 := by
  have hloc := isLocPt_bigPt_of_ne_zero P.r c hd
  have hTT : TBB.TTp p = Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := rfl
  have hpos : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd _)
  have hRR : p.RR F (P.r + 1) [] (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      B.hsInner (p.V F (TBB.bigPt P.r c)) (p.V F (TBB.bigPt P.r c)) := by
    unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hloc, hloc⟩, dite_eq_right (by omega), if_pos rfl, if_pos rfl]
    rfl
  have hEw : TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        ‖B.hsVec (p.V F (TBB.bigPt P.r c))‖ ^ 2 := by
    rw [TBB.Ew, TBB.NP, hRR, B.hsInner, JCTx2.inner_self_real, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp [TBB.normC]
  rw [hEw]
  by_cases hζ : TBB.TTp p < Complex.normSq (c (Fin.last P.r))
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [gp_bigPt_eq_normSq_prod_mul_sub]
      exact mul_pos hpos (by linarith)
    have hn := nPt_bigPt P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') c
      (by rw [← hTT]; exact hζ.le)
    rw [hTT, hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _), hsVec_norm_V_bigPt p F c hd hG]
  · replace hζ := not_lt.1 hζ
    have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [gp_bigPt_eq_normSq_prod_mul_sub]
      intro h
      have := (pos_iff_pos_of_mul_pos h).1 hpos
      linarith
    have hV0 : p.V F (TBB.bigPt P.r c) = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right]
      exact fun hh => hG hh.2
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      simpa using JCTx2.hsVec_smul' (0 : ℂ) (0 : Wq →L[ℂ] Wp)
    rw [bcWeight_eq_zero_of_normSq_le p.hl.2.2 _ _ _ (by exact hζ), hV0, h0]
    simp

theorem ew_integrable (p : KB.Pl P Wp Wq) {A : ℝ} {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hAB : B.AB P.k P.r ≤ A)
    (hT : JF.TransportedAlt P.k P.r A 0) (hH : ∀ j : ℕ, j ≤ 5 → B.InCC A j H) :
    Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  obtain ⟨cc, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq p.T.base A hAB
  obtain ⟨c4, hc4⟩ := hH 4 (by norm_num)
  have hfin : B.normSq p.T.base H ≠ ⊤ := (hB1 H H c4 c4 (hH 5 le_rfl) (hH 5 le_rfl) hc4 hc4).1
  set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
      ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q))‖ ^ 2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ q) (sq_nonneg _)
  have hmeas : AEStronglyMeasurable g volume := by
    have hc := jgq_continuousOn p.T.base hT (hH 0 (by norm_num))
    have h2 : ContinuousOn (fun q => ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q))‖ ^ 2)
        (JF.QDom P.k P.r p.T.base.z p.T.base.z') :=
      ((JCTx2.hsVec_cont'.comp_continuousOn hc).norm).pow 2
    simpa [hg, smul_eq_mul] using aesm_weight_smul p.T.base h2
  have hint : Integrable g volume := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)]
    have hns : B.normSq p.T.base H = ∫⁻ q, ENNReal.ofReal (g q) := rfl
    rw [← hns]
    exact lt_top_iff_ne_top.2 hfin
  have hcomp : Integrable (g ∘ bcE P.r) volume :=
    ((bcE_mp P.r).integrable_comp_emb (bcE P.r).measurableEmbedding).2 hint
  refine hcomp.congr ?_
  filter_upwards [ae_ne_zero_all P.r] with c hc
  simp only [Function.comp, bcE_apply, hg, B.gq]
  exact (ew_eq_weight p H c hc).symm

end place

theorem nf_pow_bound (y : ℝ) (hy : 0 ≤ y) (a b : ℕ) (E : ℝ) (hE : 0 ≤ E) : y ^ (a - b) * E ≤ E + y ^ a * E := by
  have hya : 0 ≤ y ^ a * E := mul_nonneg (pow_nonneg hy _) hE
  rcases le_total y 1 with h | h
  · have h1 : y ^ (a - b) ≤ 1 := pow_le_one₀ hy h
    nlinarith [mul_le_mul_of_nonneg_right h1 hE]
  · have h1 : y ^ (a - b) ≤ y ^ a := pow_le_pow_right₀ h (Nat.sub_le a b)
    nlinarith [mul_le_mul_of_nonneg_right h1 hE]

theorem nf_arith_d (C₁ R x N : ℝ) (hC₁ : 0 ≤ C₁) (hR1 : 1 ≤ R) (hx1 : 1 ≤ x) (hN0 : 0 ≤ N) :
    C₁ * R * x * (N + 1) ≤ C₁ * (R ^ 4 * (N * x ^ 2 + x ^ 3)) := by
  have h4 : R ≤ R ^ 4 := le_self_pow₀ hR1 (by norm_num)
  have h2 : x ≤ x ^ 2 := le_self_pow₀ hx1 (by norm_num)
  have h3 : x ≤ x ^ 3 := le_self_pow₀ hx1 (by norm_num)
  have hS : x * (N + 1) ≤ N * x ^ 2 + x ^ 3 := by nlinarith
  have hx0 : 0 ≤ x * (N + 1) := mul_nonneg (by linarith) (by linarith)
  have hR0 : 0 ≤ R ^ 4 := by positivity
  have hmain : R * (x * (N + 1)) ≤ R ^ 4 * (N * x ^ 2 + x ^ 3) := mul_le_mul h4 hS hx0 hR0
  calc C₁ * R * x * (N + 1) = C₁ * (R * (x * (N + 1))) := by ring
    _ ≤ C₁ * (R ^ 4 * (N * x ^ 2 + x ^ 3)) := mul_le_mul_of_nonneg_left hmain hC₁

theorem nf_arith_low (R x N : ℝ) (hR1 : 1 ≤ R) (hx1 : 1 ≤ x) (hN0 : 0 ≤ N) :
    R * x ^ 3 ≤ R ^ 4 * (N * x ^ 2 + x ^ 3) := by
  have h4 : R ≤ R ^ 4 := le_self_pow₀ hR1 (by norm_num)
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg (by linarith) 3
  have hNx : 0 ≤ N * x ^ 2 := mul_nonneg hN0 (sq_nonneg x)
  have hR4 : 0 ≤ R ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h4 hx3, mul_nonneg hR4 hNx]

theorem nf_arith_ab (r k : ℝ) (hr : 0 ≤ r) (hk : 2 ≤ k) :
    2 * (k + r) * (r + 1) + 1 ≤ 20 * ((r + 1) * (2 * r + k + 1) ^ 3) := by
  have hs : 3 ≤ 2 * r + k + 1 := by linarith
  have hs3 : 9 * (2 * r + k + 1) ≤ (2 * r + k + 1) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r + k + 1)
      (by linarith : (0 : ℝ) ≤ 2 * r + k + 1 - 3)) (by linarith : (0 : ℝ) ≤ 2 * r + k + 1 + 3)]
  have h1 : (r + 1) * (9 * (2 * r + k + 1)) ≤ (r + 1) * (2 * r + k + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hs3 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : k + r ≤ 2 * r + k + 1) (by linarith : (0 : ℝ) ≤ r + 1)]

theorem nf_arith_thr (R x : ℝ) (hR1 : 1 ≤ R) (hx1 : 1 ≤ x) : x ^ 2 * (9 * R) < 20 * (R * x ^ 3) := by
  have hx2 : 0 < R * x ^ 2 := mul_pos (by linarith) (pow_pos (by linarith) 2)
  nlinarith [mul_lt_mul_of_pos_left (by linarith : (9 : ℝ) < 20 * x) hx2]

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDom
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def DominatedL2TruncationBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) ≤ h c

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cutN_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => cutN k r n g • f g) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutN k r n) := by
    unfold cutN
    refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
    refine ContDiff.div_const (contDiff_const.sub ?_) _
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    exact hN.comp ((contDiff_apply_apply (𝕜 := ℝ) i j).comp (contDiff_const_smul _))
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => cutN k r n g • f' g, hU, hgU, hc.contDiffOn.smul hf', fun g hg hgv => ?_⟩
  show cutN k r n g • f g = cutN k r n g • f' g
  rw [hff g hg hgv]

end cutn

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TypeNormMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), JF.TransportedAlt P.k P.r A 0 → B.InCC A 0 Y → ∀ ρ : M.Ty P,
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖) volume

def VecVGPos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y Y' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = Y' g) → ∀ a : C.LPt, p.V Y a = p.V Y' a

def DopCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
    ∀ e : Wd.Ix (Fin w.length), ∃ Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = p.Θ.Θ w e X g) ∧
        ∀ A : ℝ, B.InCC A 0 Y

def ScalarMeas : Prop :=
  ∀ (k r : ℕ) (TT : ℝ), Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) ∧
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c))

def EmptyMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base X → AEStronglyMeasurable (topD p X []) volume

theorem ae_all_ne (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : volume ((fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have e : {a : Fin (r + 1) → ℂ | ¬a i ≠ 0} = (fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0} := by
    ext a; simp
  exact ae_iff.2 (by rw [e]; exact h)

theorem topDMeasCpt_of_parts (h1 : TypeNormMeas) (h2 : VecVGPos) (h3 : DopCC) (h4 : ScalarMeas) (h5 : EmptyMeas) :
    TopDMeasCpt := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw
  by_cases hw0 : w = []
  · subst hw0; exact h5 Wp Wq P p X hX
  choose Y hYe hYc using h3 Wp Wq P p X w Cb hD hX hw
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hV : ∀ e a, p.V (p.Θ.Θ w e X) a = p.V (Y e) a := fun e a =>
    h2 Wp Wq P p _ _ (fun g hg hG => (hYe e g hg hG).symm) a
  obtain ⟨hn, hW⟩ := h4 P.k P.r TT
  set g : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ((((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
        TBB.normC (fun _ => 1) w : ℝ) : ℂ) *
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ))).re with hg
  have hgm : AEStronglyMeasurable g volume := by
    have hdH : ∀ e ρ, Measurable (fun c : Fin (P.r + 1) → ℂ => Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ) := by
      intro e ρ
      unfold Top.dH
      exact ((hW.pow_const _).mul_const _).sqrt
    have hterm : ∀ e ρ, AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume := by
      intro e ρ
      have h1' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2) volume :=
        (h1 Wp Wq P p (Y e) A hThr (hYc e A) ρ).pow 2
      have h2' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable h1'
      have h3' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ)) volume :=
        (Complex.measurable_ofReal.comp ((hdH e ρ).mul (hdH e ρ))).aestronglyMeasurable
      exact h3'.mul h2'
    have hsum : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun e _ => Finset.aestronglyMeasurable_fun_sum _ fun ρ _ => hterm e ρ
    have hpre : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        (((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
          TBB.normC (fun _ => 1) w : ℝ) : ℂ))) volume :=
      (Complex.measurable_ofReal.comp (((hn.sqrt.mul hn.sqrt).div_const _))).aestronglyMeasurable
    exact Complex.continuous_re.comp_aestronglyMeasurable (hpre.mul hsum)
  refine hgm.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
  show g c = topD p X w c
  unfold topD TBB.Ew TBB.NP KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hl, hl⟩, dite_eq_right (by omega), if_pos rfl, if_neg hw0]
  unfold Top.topOf
  simp only [hg]
  congr 3
  funext e
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  show _ = _ * (((‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e X) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)
  rw [hV e]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

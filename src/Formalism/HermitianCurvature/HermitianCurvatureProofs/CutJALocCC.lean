module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAlg
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inCC_antiA {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {A A' : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : A' ≤ A) (hF : B.InCC A m F) : B.InCC A' m F := by
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hc1, fun u w hu hw hl g hg => ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 h) (norm_nonneg _)).trans
    (hc2 u w hu hw hl g hg)

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem cCg_antiA {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {A A' Bg : ℝ} {F : GFn S v} (h : A' ≤ A)
    (hF : CCg S v A Bg F) : CCg S v A' Bg F :=
  fun m => inCC_antiA (by linarith) (hF m)

theorem locCC_antiA {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A A' Bg : ℝ} {J : GFn S v} (h : A' ≤ A) (hJ : LocCC S T v A Bg J) : LocCC S T v A' Bg J := by
  refine ⟨hJ.1, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  exact ⟨F, h1, cCg_antiA h h2, h3⟩

theorem locCC_JF {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} {F : GFn S v} (hF : B.CkOn ⊤ (B.GV S.G.k S.G.r) F) (hA : ∀ m : ℕ, B.InCC A m F)
    (hFF : B.JF (T v).base F ∈ smoothFormsPositiveCone S T v) (hBg : 0 ≤ Bg) : LocCC S T v A Bg (B.JF (T v).base F) :=
  ⟨hFF, fun _ _ => ⟨F, hF, fun m => inCC_antiA (sub_le_self _ (mul_nonneg hBg (Nat.cast_nonneg m))) (hA m),
    fun _ _ _ => rfl⟩⟩

theorem locCC_smul {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} (c : ℂ) {J : GFn S v} (hJ : LocCC S T v A Bg J) : LocCC S T v A Bg (c • J) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_smul hJ.1 c, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  refine ⟨c • F, Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' c h1, fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c0, hc0⟩ := h2 m
    exact ⟨‖c‖ * c0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc0⟩
  · rw [Formalism.FourierDecayAlt.P.CutMP.En.JF_smul', Pi.smul_apply, h3 x hx hG]

end loc

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

def JALocOp : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)

def JALocAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)

def JALocPhi : Prop :=
  ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)

def JALocAdd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')

def LocalSquareIntegrableTransfer : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

theorem nDim_nonneg (k r : ℕ) : 0 ≤ nDim k r := by unfold nDim; positivity

theorem mul_mul_le_mul_mul_of_nonneg {a b x y : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) : a * x * y ≤ b * x * y :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hx) hy

theorem mul_le_of_le_of_mul_le {a b x B : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hB : b * x ≤ B) : a * x ≤ B :=
  (mul_le_mul_of_nonneg_right h hx).trans hB

theorem jALocCC_of_leaves (h2 : JALocOp) (h3 : JALocAdj) (h4 : JALocPhi) (h5 : JALocAdd) (h8 : LocalSquareIntegrableTransfer) :
    JALocCC := by
  obtain ⟨C2, G2, -, H2⟩ := h2
  obtain ⟨C3, G3, -, H3⟩ := h3
  obtain ⟨G4, -, H4⟩ := h4
  obtain ⟨C5, H5⟩ := h5
  obtain ⟨C8, H8⟩ := h8
  refine ⟨max (max C2 C3) (max C5 C8), max (max G2 G3) (max G4 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  have hn := nDim_nonneg S.G.k S.G.r
  have hn2 : 0 ≤ nDim S.G.k S.G.r ^ 2 := by positivity
  have hr2 : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 2 := by positivity
  have c2 : C2 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_left _ _)
  have c3 : C3 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_right _ _)
  have c5 : C5 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_left _ _)
  have c8 : C8 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_right _ _)
  have g2 : G2 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_left _ _)
  have g3 : G3 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_right _ _)
  have g4 : G4 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_right (le_max_left _ _)
  refine ⟨fun F A Bg h1 h2 h3 h4 => locCC_JF h1 h2 h3 h4, ?_, ?_, ?_, ?_, fun Bg A c J hJ => locCC_smul c hJ,
    fun Bg A A' J h hJ => locCC_antiA h hJ, ?_⟩
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H2 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g2 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c2 hr hn2]) hA) hJ hFF
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H3 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g3 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c3 hr hn2]) hA) hJ hFF
  · intro φ Bg A J hφ hld hG hJ hFF
    exact H4 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v φ Bg A J hφ hld (mul_le_of_le_of_mul_le g4 hr hG) hJ hFF
  · intro Bg A J J' hBg hA hJ hJ'
    exact H5 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A J J' hBg (le_trans (mul_mul_le_mul_mul_of_nonneg c5 hr hn2) hA) hJ hJ'
  · intro Bg A ε J e hFr hBg hε hA hJ π
    exact H8 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A ε J e hFr hBg hε
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c8 hr2 hn]) hA) hJ π

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

open Asm in
theorem polynomial_radial_base_holds : PolynomialRadialAtSectionOfPhaseInvariance := by
  intro hD hK hF hA hC hP hE hW Wp Wq _ _ _ _ _ _ P Bs hsec hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hAct' := hAct
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hAct'
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hTT : 0 < P.TT := by rw [← hTz]; exact mul_pos Bs.T_pos Bs.T'_pos
  have hcs := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  rw [← hsec] at hcs
  have hAnn : ∀ ζ ∈ Gauge.GC.Ann P, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ :=
    fun ζ hζ => by rw [hTz]; exact hζ
  set ζ₁ : ℂ := ((P.TT + 1 : ℝ) : ℂ) with hζ₁def
  have hζ₁ : ζ₁ ∈ Gauge.GC.Ann P := by
    show P.TT < Complex.normSq ζ₁
    rw [hζ₁def, Complex.normSq_ofReal]; nlinarith
  have hDc : ∀ ζ ∈ Gauge.GC.Ann P,
      SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ ∧
      SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ = SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ ∧
      SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ := by
    intro ζ hζ
    rw [hsec]
    exact hD P.k P.r Bs.z Bs.z' (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ ζ₁ (hAnn ζ hζ) (hAnn ζ₁ hζ₁)
  have hFc : ∀ ζ ∈ Gauge.GC.Ann P,
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    intro ζ hζ
    unfold NF.Fib
    rw [hcs.2 ζ ζ₁ (hAnn ζ hζ) (hAnn ζ₁ hζ₁)]
  obtain ⟨Qr, hKP, hKL⟩ := hK Wp Wq P Bs hsec hk X d hAct Pr hPr
  have hGT : Gauge.GC.GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hSt, hRel, hQQ⟩
  have hLine := Gauge.GC.gauge_kappa_line_holds Wp Wq P Bs X d hGT Qr hKP ζ₁ hζ₁
  obtain ⟨Eπ, hEπF, hEπQ, hEπn, hEπsp⟩ := hLine π
  obtain ⟨Eρ, hEρF, hEρQ, hEρn, hEρsp⟩ := hLine ρ
  have hQQr : ∀ σ, (Qr σ).comp (Qr σ) = Qr σ := fun σ => by rw [hKP.1 σ σ, if_pos rfl]

  have hval : ∀ (Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r →
      ∀ ζ ∈ Gauge.GC.Ann P, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro Ψ c hc ζ hζ p hp
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, hAnn ζ hζ⟩
    have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
    have h1 := Ψ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom p.1 hp.1 p.2 hp.2.1
    simp only at h1
    rw [hp.2.2] at h1
    exact h1.symm
  have hEπne : Eπ ≠ 0 := by
    intro h0
    rw [h0] at hEπn
    have : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq)).map_zero
    rw [this, inner_zero_left] at hEπn
    exact zero_ne_one hEπn
  have hEπFa : ∀ ζ ∈ Gauge.GC.Ann P, Eπ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun ζ hζ => (hFc ζ hζ).symm ▸ hEπF
  have hPπ : ∀ ζ ∈ Gauge.GC.Ann P, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Eπ = Eπ :=
    fun ζ hζ => by rw [hKL ζ hζ Eπ (hEπFa ζ hζ) π, hEπQ]

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := Gauge.GC.radBase_of P Bs hpl
  have hsecπ : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun _ : (Fin P.r → ℂ) × ℂ => Eπ) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨(contDiffOn_const (c := Eπ)).congr fun q hq => by simp [Set.indicator_of_mem hq], fun q hq => ?_,
      fun q hq => by simp [Set.indicator_of_notMem hq]⟩
    rw [Set.indicator_of_mem hq]
    exact hEπFa q.2 (by show P.TT < _; rw [← hTz]; exact hq.2)
  obtain ⟨Φ0, hΦ0, hΦr⟩ :=
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsecπ
  let Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ0, hΦ0⟩
  have hΦ : ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = Eπ := by
    intro c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, hAnn ζ hζ⟩
    have h := congrFun hΦr (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hsum : ∀ σ : M.Ty P, (∑ τ, (Pi.single σ (1 : ℂ) : M.Ty P → ℂ) τ • Qr τ) = Qr σ := by
    intro σ
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (fun h => absurd (Finset.mem_univ σ) h)]
    simp
  have hKπ : (d.κ (Pi.single π 1)).1 Φ = Φ := by
    apply Subtype.ext
    refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ (Pi.single π 1)).1 Φ).2 _ Φ.2 (funext fun q => ?_)
    by_cases hq : q ∈ NF.QR P.k P.r Bs.z Bs.z'
    · simp only [NF.radR, Set.indicator_of_mem hq]
      have hqA : q.2 ∈ Gauge.GC.Ann P := by show P.TT < _; rw [← hTz]; exact hq.2
      have h1 := hKP.2.2.2 (Pi.single π 1) Φ ⟨(q.1, q.2), hq.1, hqA⟩
      simp only at h1
      rw [h1, hsum, hΦ q.1 hq.1 q.2 hqA, hEπQ]
    · simp only [NF.radR, Set.indicator_of_notMem hq]

  obtain ⟨Y, hY⟩ : ∃ Y : ℂ, M.xEx P {l} π Y ≠ 0 := by
    refine ⟨((1 + ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| : ℝ) : ℂ), ?_⟩
    unfold M.xEx
    rw [Finset.prod_ne_zero_iff]
    intro i hi h0
    have h2 := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h2
    have hle : |M.rho P π i| ≤ ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P π j| :=
      Finset.single_le_sum (f := fun j => |M.rho P π j|) (fun j _ => abs_nonneg _) (Finset.mem_sdiff.1 hi).1
    linarith [neg_abs_le (M.rho P π i)]

  have hAlg := hA P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) d hRel l hl π ρ hUp Y
  have hAlg1 : (d.κ (Pi.single ρ 1)).1 (X.t Y 1 0 Φ) = M.xEx P {l} π Y • (d.SS l).1 Φ := by
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ) hAlg
    rw [← hQQ Y] at h
    change ((d.κ (Pi.single ρ 1)).1 * (X.t Y 1 0) * (d.κ (Pi.single π 1)).1) Φ =
      (algebraMap ℂ (Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (M.xEx P {l} π Y) *
        ((d.SS l).1 * (d.κ (Pi.single π 1)).1)) Φ at h
    simp only [Module.End.mul_apply, Module.algebraMap_end_apply] at h
    rw [hKπ] at h
    exact h
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hPt : ∀ ζ ∈ Gauge.GC.Ann P, M.xEx P {l} π Y • S ζ Eπ =
      (Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0)
        (NF.muZ P.k P.r Bs.μsec ζ)).comp (Qr ρ) := by
    intro ζ hζ
    have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, hAnn ζ hζ⟩
    have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
    have e1 := congrArg (fun Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)) hAlg1
    have h1 := hKP.2.2.2 (Pi.single ρ 1) (X.t Y 1 0 Φ) ⟨(c0, ζ), hc0, hζ⟩
    simp only at h1 e1
    rw [h1, hsum, X.t_apply Y 1 0 Φ (c0, NF.muZ P.k P.r Bs.μsec ζ) hdom, Submodule.coe_smul] at e1
    simp only [Pi.smul_apply] at e1
    rw [hS Φ c0 hc0 ζ hζ, hΦ c0 hc0 ζ hζ] at e1
    exact e1.symm

  have hSF : ∀ ζ ∈ Gauge.GC.Ann P, S ζ Eπ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro ζ hζ
    have h := hval ((d.SS l).1 Φ) c0 hc0 ζ hζ
    rw [hS Φ c0 hc0 ζ hζ, hΦ c0 hc0 ζ hζ] at h
    exact h
  have hW1 : ∀ ζ ∈ Gauge.GC.Ann P, (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ) =
      (M.xEx P {l} π Y)⁻¹ • (Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0)
        (NF.muZ P.k P.r Bs.μsec ζ)).comp (Qr ρ) := by
    intro ζ hζ
    rw [hKL ζ hζ _ (hSF ζ hζ) ρ]
    have h := hPt ζ hζ
    have h2 : S ζ Eπ = (M.xEx P {l} π Y)⁻¹ • (Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0) (NF.muZ P.k P.r Bs.μsec ζ)).comp (Qr ρ) := by
      rw [← h, smul_smul, inv_mul_cancel₀ hY, one_smul]
    rw [h2, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hQQr]

  have hWline : ∀ ζ ∈ Gauge.GC.Ann P, (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ) =
      inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ))) • Eρ := by
    intro ζ hζ
    have hWF := (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ hζ _ (hSF ζ hζ) ρ).1
    refine hEρsp _ (hFc ζ hζ ▸ hWF) ?_
    rw [hKL ζ hζ _ (hSF ζ hζ) ρ, ContinuousLinearMap.comp_assoc, hQQr]

  let F : ℂ → ℂ := fun ζ =>
    inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ)))
  have hCP := hC Wp Wq P Bs hpl hk hsec Φ Eπ hΦ c0 hc0 Y
  let Lf : (Wq →L[ℂ] Wp) →ₗ[ℂ] ℂ := (M.xEx P {l} π Y)⁻¹ •
    ((innerₛₗ ℂ (B.hsVec Eρ)).comp ((Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq)).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (Qr ρ)).toLinearMap))
  have hFPS : PS P.TT F := by
    refine PS.congr (PSV.apply hCP Lf) fun ζ hζ => ?_
    show inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ))) = _
    rw [hW1 ζ hζ]
    simp only [Lf, LinearMap.smul_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, smul_eq_mul]
    change inner ℂ (B.hsVec Eρ) (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq) ((M.xEx P {l} π Y)⁻¹ • _)) = _
    rw [map_smul, inner_smul_right]
    rfl

  obtain ⟨T1, hT1def⟩ : ∃ T : Wq →L[ℂ] Wp, T = (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁)).comp
      (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁)
        (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ₁) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁) Eπ) := ⟨_, rfl⟩
  have hT1ne : T1 ≠ 0 := by
    rw [hT1def]
    exact hW Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' l hl π ρ hUp ζ₁ hζ₁ Eπ hEπF (hPπ ζ₁ hζ₁) hEπne
  have hThtF := (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ₁ hζ₁ Eπ hEπF ρ).2
  have hT1F := (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ₁ hζ₁ _ hThtF ρ).1
  have hT1line : T1 = inner ℂ (B.hsVec Eρ) (B.hsVec T1) • Eρ := by
    rw [hT1def]
    refine hEρsp _ hT1F ?_
    rw [hKL ζ₁ hζ₁ _ hThtF ρ, ContinuousLinearMap.comp_assoc, hQQr]
  obtain ⟨t0, ht0def⟩ : ∃ t : ℂ, t = inner ℂ (B.hsVec Eρ) (B.hsVec T1) := ⟨_, rfl⟩
  rw [← ht0def] at hT1line
  have ht0 : t0 ≠ 0 := by
    intro h0; apply hT1ne; rw [hT1line, h0, zero_smul]

  have hrotA : ∀ θ : ℝ, ∀ ζ ∈ Gauge.GC.Ann P, rot θ ζ ∈ Gauge.GC.Ann P := by
    intro θ ζ hζ
    show P.TT < Complex.normSq (rot θ ζ)
    have h1 : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
    rw [rot, Complex.normSq_mul, h1, one_mul]; exact hζ
  have hFinv : ∀ θ : ℝ, ∀ ζ : ℂ, P.TT < Complex.normSq ζ → F (rot θ ζ) = F ζ := by
    intro θ ζ hζ
    obtain ⟨c, hc⟩ := hP Wp Wq P Bs hsec hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp θ
    have hc1 : c = 1 := by
      have h := (hc ζ₁ hζ₁ Eπ hEπF (hPπ ζ₁ hζ₁)).2
      obtain ⟨e1, e2, e3⟩ := hDc (rot θ ζ₁) (hrotA θ ζ₁ hζ₁)
      rw [e1, e2, e3, ← hT1def] at h
      have h' : (1 - c) • T1 = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact (sub_eq_zero.1 h'').symm
      · exact absurd h'' hT1ne
    have h := (hc ζ hζ Eπ (hEπFa ζ hζ) (hPπ ζ hζ)).1
    rw [hc1, one_smul] at h
    show inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp
      (S (rot θ ζ) Eπ))) = inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
      (S ζ Eπ)))
    rw [h]
  obtain ⟨m, q, hq⟩ := hE P.TT F hTT hFPS hFinv
  refine ⟨m, Polynomial.C t0⁻¹ * q, fun ζ hζ Xf hXf hXπ => ?_⟩
  have hXF1 : Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := hFc ζ hζ ▸ hXf
  have hXQ : Xf.comp (Qr π) = Xf := by rw [← hKL ζ hζ Xf hXf π, hXπ]
  obtain ⟨x, hXe⟩ : ∃ x : ℂ, Xf = x • Eπ := ⟨_, hEπsp Xf hXF1 hXQ⟩
  subst hXe
  have hW' : (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ) = F ζ • Eρ := hWline ζ hζ
  obtain ⟨e1, e2, e3⟩ := hDc ζ hζ
  rw [map_smul, map_smul, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, hW', e1, e2, e3,
    ← hT1def, hT1line]
  simp only [smul_smul, Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  have hq' := hq ζ hζ
  simp only [gg, sig] at hq'
  have hinv : t0⁻¹ * t0 = 1 := inv_mul_cancel₀ ht0
  rw [mul_left_comm, hq']
  linear_combination (-(q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) * x)) * hinv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

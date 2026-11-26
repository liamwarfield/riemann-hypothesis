module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LocOp

def lcChi (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem lcChi_zero {x : ℝ} (hx : x < 1 / 2) : lcChi x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem lcChi_one {x : ℝ} (hx : 1 ≤ x) : lcChi x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem isCut0_lcChi : C6.IsCut0 lcChi :=
  ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
    ⟨1 / 2, by norm_num, fun _ hx => lcChi_zero hx⟩, fun _ hx => lcChi_one hx⟩

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem wR_lie {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w, B.inLie k r x.2 :=
  fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx)

theorem rw_congr_GV {F₀ : Type} [NormedAddCommGroup F₀] [NormedSpace ℂ F₀] {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → F₀} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) {w : List (B.Mat k r)}
    (hw : ∀ X ∈ w, B.inLie k r X) : ∀ g ∈ B.GV k r, g ∈ O → B.Rw w f₁ g = B.Rw w f₂ g := by
  intro g hg hgO
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR, ← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc (wR_lie hw) hO h g hg hgO

theorem opApply_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ f₁ g = B.opApply Θ f₂ g := by
  intro g hg hgO
  unfold B.opApply
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_congr_GV hO h T.word_lie g hg hgO]

theorem opAdj_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ f₁ g = B.opAdj Θ f₂ g := by
  intro g hg hgO
  unfold B.opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  have h' : ∀ x ∈ B.GV k r, x ∈ O → T.coefAdj x (f₁ x) = T.coefAdj x (f₂ x) := fun x hx hxO => by
    rw [h x hx hxO]
  have hrev : ∀ X ∈ T.word.reverse, B.inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
  rw [rw_congr_GV hO h' hrev g hg hgO]

end gen

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem rep (hAg : LT.AgreeOm) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {Cb A₀ : ℝ} (hB : BuiltOW Cb S T f χ ν' m₀ top A₀) (v : Fin S.f) {A Bg δ : ℝ} {J : GFn S v}
    (hBg : 2 * ((S.G.r : ℝ) + 1) ≤ Bg) (hJ : LocCC S T v A Bg J) (hδ : 0 < δ) :
    ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
      (∀ g ∈ B.GV S.G.k S.G.r, Gf S.G.k S.G.r (T v).base.z (T v).base.z' g < 3 * δ / 8 → F g = 0) ∧
      ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g →
        J g = B.JF (T v).base F g := by
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  obtain ⟨F₀, hF₀c, hF₀g, hF₀e⟩ := hJ.2 (δ / 4) (by positivity)
  have hε : (0 : ℝ) < 3 * δ / 4 := by positivity
  obtain ⟨δ', -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div isCut0_lcChi hε
  obtain ⟨hFc, hFg⟩ := gcut_graded (T v).base.z (T v).base.z' (fun x => lcChi (x / (3 * δ / 4))) (δ' * (3 * δ / 4))
    hcut hBg hF₀c hF₀g
  refine ⟨D.cutF (T v).base lcChi F₀ (3 * δ / 4), hFc, hFg, ?_, ?_⟩
  · intro g _ hg
    have h1 : Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / (3 * δ / 4) < 1 / 2 := by
      rw [div_lt_iff₀ hε]; linarith
    simp [D.cutF, lcChi_zero h1]
  · intro g hg hG
    refine hAg _ _ _ _ (T v).base J _ (Set.Ioi (3 * δ / 4)) hJ.1 ?_ g hg hG
    intro q hq hGq
    have hGq' : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) := hGq
    have hx : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT := ⟨hq.1, by rw [hTT]; exact hq.2⟩
    rw [hF₀e q hx (by unfold GfP; linarith), Formalism.FourierDecayAlt.P.JCTx2.JF_cutF]
    have h1 : 1 ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) / (3 * δ / 4) := by
      rw [le_div_iff₀ hε]; linarith
    rw [lcChi_one h1]
    simp

theorem isOpen_omPlus_inter_lt {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℝ) :
    IsOpen (Q.OmPlus k r z z' ∩ {g | c < Gf k r z z' g}) :=
  (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z').inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont z z'))

end place

end LocOp

namespace LocOp

section place2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem thr_of {k r : ℕ} {o : ℕ} {A d Bg : ℝ} (hd : 0 ≤ d) (hBg : 0 ≤ Bg)
    (hA : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d + 2 * Bg * ((o : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (A - Bg * o) o := by
  have ho : (0 : ℝ) ≤ (o : ℝ) := Nat.cast_nonneg o
  have hBo : 0 ≤ Bg * (o : ℝ) := mul_nonneg hBg ho
  exact jdc_thrW o (A - Bg * o) d hd (by nlinarith)

end place2

end LocOp

theorem jALocOp_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJApply) : JALocOp := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨⟨hc, hg⟩, -⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opApply Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opApply_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  exact hTh _ _ _ _ (T v).base Θ _ F (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn _ hgO

theorem jALocAdj_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJ) : JALocAdj := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨-, ⟨hc, hg⟩⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opAdj Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opAdj_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  set UU : Set (B.Mat S.G.k S.G.r) := {g | g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∧
    3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g} with hUU
  have hCkJ : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J := jdc_ckOn_om _ _ hJ.1.1
  have hCk : B.CkOn ⊤ UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc', he⟩ := hCkJ g₀ hg₀.1
    refine ⟨U ∩ (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
        {g | 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g}), f',
      hU.inter (LocOp.isOpen_omPlus_inter_lt _ _ _), ⟨hgU, hg₀.1.2, hg₀.2⟩, hc'.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
    rw [← hFe g ⟨hgG, hg.2.1⟩ hg.2.2]
    exact he g hg.1 hgG
  exact (hTh _ _ _ _ (T v).base Θ _ F UU (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn (fun g hg => hg.1)
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono le_top hCk)).2 _ ⟨hgO, hGx⟩

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6.Lev0

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lev0Q {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (0 + ρ) + k + 1) → ℂ) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (ε : ℝ) (hε : 0 < ε)
    (A₀ A : ℝ) (mm : ℕ) (hA : A + 2 * (((0 + ρ : ℕ) : ℝ) + 1) * (mm : ℝ) ≤ A₀) :
    ∃ ε' C : ℝ, 0 < ε' ∧ 0 ≤ C ∧ ∀ (f : B.Mat k (0 + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm f c →
      B.CCle A mm (fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g) (C * c) ∧
      ∀ g ∈ B.GV k (0 + ρ), ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g ≠ 0 → ε' ≤ Gf k (0 + ρ) z z' g := by
  obtain ⟨δ, hδ, hG, hsupp⟩ := isCutG_div hχ hε
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k 0 ρ Wp Wq z z' 0 0 (idOp k (0 + ρ) Wp Wq) bumpOne
    (fun x => χ (x / ε)) (δ * ε) (inDD_idOp k ρ Wp Wq) isCutC_bumpOne hG mm mm A₀ (by simp)
  refine ⟨δ * ε, max C 0, by positivity, le_max_right _ _, fun f c hc => ?_⟩
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hS := hC f c hc
  have hF : B.opApply (idOp k (0 + ρ) Wp Wq) (U.cutDG k 0 ρ z z' bumpOne (fun x => χ (x / ε)) f) =
      fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g := by
    rw [opApply_idOp]
    funext g
    simp [U.cutDG, U.DjU, bumpOne_one]
  rw [hF] at hS
  obtain ⟨hck, -, hbd⟩ := hS
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.compactly_supported_monotone k (0 + ρ) _
      (A₀ - ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) - 2 * (((0 + ρ : ℕ) : ℝ) + 1) * ((mm + 0 : ℕ) : ℝ))
      A (C * c) mm _ ?_ ⟨hck, ?_⟩) (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0), ?_⟩
  · push_cast at hA ⊢; linarith
  · intro u v hu hv hl g hg
    refine hbd u v ?_ ?_ hl g hg
    · intro X hX; exact ⟨⟨(hu X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hu X hX).2⟩
    · intro X hX; exact ⟨⟨(hv X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hv X hX).2⟩
  · intro g hg hne
    have h1 : χ (Gf k (0 + ρ) z z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have h2 := hsupp _ h1
    rw [le_div_iff₀ hε] at h2
    linarith

def xs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) (p : C.LPt) (hc : r - i = r - D.ptSize p) (h : B.Mat k r → (Wq →L[ℂ] Wp))
    (a : Wd.Ix (Fin w.length)) : B.Mat k (r - i) → (Wq →L[ℂ] Wp) :=
  D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h ε) i hi w a) p)

theorem sliceQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (a : Wd.Ix (Fin w.length)),
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      (∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (xs T χ ε i hi w p hc h a) ∧
        B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xs T χ ε i hi w p hc h a) (K * c)) ∧
      ∀ (h₁ h₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV k r) h₁ → B.CkOn ⊤ (B.GV k r) h₂ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₁ c₁ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₂ c₂ →
        ∀ γ ∈ B.GV k (r - i), xs T χ ε i hi w p hc h₁ a γ - xs T χ ε i hi w p hc h₂ a γ =
          xs T χ ε i hi w p hc (fun g => h₁ g - h₂ g) a γ := by
  obtain ⟨Cp, hCp0, hL⟩ := levQ
  refine ⟨max 150 (16 * Cp), by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw p hc hp a
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    obtain rfl : p = [] := by
      cases p with
      | nil => rfl
      | cons b p =>
        exfalso
        have h1 := (hp.1 b (by simp)).1
        have h2 := hp.2
        simp [D.ptSize] at h2
        omega
    have hfun : ∀ h : B.Mat k r → (Wq →L[ℂ] Wp), xs T χ ε 0 hi w [] hc h a =
        (if a = Wd.e1 then D.cutF T.base χ h ε else 0) := by
      intro h
      funext γ
      have hcm : D.castM (k := k) (a := r - 0) (b := r - D.ptSize []) hc γ = γ := by
        ext i j; rfl
      simp only [xs, D.castF]
      rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem, Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
    obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
    have hb := Formalism.FourierDecayAlt.P.JCTx6.Link.budget0 (0 + ρ) k N hk2 A₀ Cc (le_trans (le_max_left _ _) hCc) hA₀
    obtain ⟨ε', C, hε', hC0, hQ⟩ := lev0Q (Wp := Wp) (Wq := Wq) T.base.z T.base.z' χ hχ ε hε A₀ (P5.Auser P0 N + 1) (P5.mmUser P0 N) (by
        simp only [P5.Auser, P5.mmUser, P5.nV, hPk, hPr]
        push_cast
        push_cast at hb
        linarith)
    have hmmM : P5.mmUser P0 N ≤ 3 * (11 * (N * (2 * (0 + ρ) + k + 1) ^ 2 + (2 * (0 + ρ) + k + 1) ^ 3) + 5) := by
      obtain ⟨-, -, b3, -, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs (0 + ρ) k N 0 0 hk2 (Nat.zero_le _) (Nat.zero_le _)
      have : P5.mmUser P0 N = 5 + 3 * ((0 + ρ) + 1) * (N + 2) * (2 * (0 + ρ) + k + 1) + N * (0 + ρ) := by
        simp only [P5.mmUser, P5.nV, hPk, hPr]
      omega
    refine ⟨ε', C, hε', hC0, ?_, ?_⟩
    · intro h c _ hcl
      have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hcl
      rw [hfun h]
      by_cases ha : a = Wd.e1
      · rw [if_pos ha]
        obtain ⟨q1, q2⟩ := hQ h c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmmM hcl)
        exact ⟨⟨q1.1, ⟨_, q1⟩, q2⟩, q1⟩
      · rw [if_neg ha]
        have hz : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (0 : B.Mat k (0 + ρ - 0) → (Wq →L[ℂ] Wp)) (C * c) :=
          Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (mul_nonneg hC0 hc0)
        exact ⟨⟨hz.1, ⟨_, hz⟩, fun g _ hne => (hne rfl).elim⟩, hz⟩
    · intro h₁ h₂ c₁ c₂ _ _ _ _ γ _
      rw [hfun h₁, hfun h₂, hfun (fun g => h₁ g - h₂ g)]
      by_cases ha : a = Wd.e1
      · simp only [if_pos ha, D.cutF, smul_sub]
      · simp only [if_neg ha, Pi.zero_apply, sub_zero]
  · obtain ⟨ε', K, hε', hK, hQ1, hQ2⟩ := hL Cc (le_trans (le_max_right _ _) hCc) k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ
      hA₀ ε hε i hi h1 w hw p hc hp a
    exact ⟨ε', K, hε', hK, hQ1, hQ2⟩

theorem auser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.Auser P0 L ≤ P5.Auser P0 N := by
  unfold P5.Auser
  have : (L : ℝ) ≤ N := by exact_mod_cast h
  gcongr

theorem mmUser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.mmUser P0 L ≤ P5.mmUser P0 N := by
  unfold P5.mmUser
  gcongr

theorem formLev_limit {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
      D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) (fun e => (hdx n e).1) (fun e => (hyn n e).1)).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) (fun e => (hdy n e).1) (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ n, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    intro n
    rw [key n]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx n e).2) (hv _ _ fun e => (hyn n e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy n e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) atTop (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero (fun n => norm_nonneg _) hbd hlim

end Formalism.FourierDecayAlt.P.PBE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section smooth

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_global {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X ψ = fun g => fderiv ℝ ψ g (g * X) := by
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ (Formalism.FourierDecayAlt.P.B4.cv false X 0 g)) (Formalism.FourierDecayAlt.P.B4.cv false X 0 g) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (Formalism.FourierDecayAlt.P.B4.cv_hasDerivAt false X g)
  rw [Formalism.FourierDecayAlt.P.B4.cv_zero] at h
  exact h.deriv

theorem rdV_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) : ContDiff ℝ ∞ (RdV X ψ) := by
  rw [rdV_global hψ X]
  exact (hψ.fderiv_right (m := ∞) (by simp)).clm_apply (Formalism.FourierDecayAlt.P.B4.mulR X).contDiff

theorem rw_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) : ∀ w : List (B.Mat k r), ContDiff ℝ ∞ (B.Rw w ψ)
  | [] => hψ
  | X :: w => rdV_contDiff (rw_contDiff hψ w) X

theorem contDiff_listSum {ι : Type*} (f : ι → B.Mat k r → E) :
    ∀ L : List ι, (∀ i ∈ L, ContDiff ℝ ∞ (f i)) → ContDiff ℝ ∞ (fun g => (L.map fun i => f i g).sum)
  | [], _ => by simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : B.Mat k r => (0 : E)))
  | i :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (contDiff_listSum f L fun j hj => h j (by simp [hj]))

theorem ckOn_of_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (m : ℕ∞) (UU : Set (B.Mat k r)) :
    B.CkOn m UU ψ :=
  fun _ _ => ⟨Set.univ, ψ, isOpen_univ, trivial,
    (hψ.of_le (by exact_mod_cast (le_top : m ≤ ⊤))).contDiffOn, fun _ _ _ => rfl⟩

theorem ckOn_sub_set {m : ℕ∞} {UU UU' : Set (B.Mat k r)} (h : UU' ⊆ UU) {f : B.Mat k r → E}
    (hf : B.CkOn m UU f) : B.CkOn m UU' f :=
  fun g hg => hf g (h hg)

end smooth

section pointwise

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opAdj_capTh_contDiff (s Y : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (B.opAdj (capTh k r Wp Wq s Y) ψ) := by
  unfold B.opAdj
  refine contDiff_listSum (fun (T : B.DTerm k r Wp Wq) g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse
    (fun x => T.coefAdj x (ψ x)) g) _ fun T hT => ?_
  obtain ⟨c, w, rfl⟩ := mem_capOp s (capLw k r Y) hT
  refine (rw_contDiff ?_ _).const_smul _
  show ContDiff ℝ ∞ (fun x => (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (ψ x))
  simpa using hψ.const_smul (conj c)

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  have h := (Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_smul c A
  rw [Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply] at h
  exact h

theorem hsVec_sub (A C : Wq →L[ℂ] Wp) : B.hsVec (A - C) = B.hsVec A - B.hsVec C := by
  have h := (Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_sub A C
  rw [Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply] at h
  exact h

theorem hs_sub_right (A C D : Wq →L[ℂ] Wp) : B.hsInner A (C - D) = B.hsInner A C - B.hsInner A D := by
  unfold B.hsInner
  rw [hsVec_sub, inner_sub_left]

theorem hsInner_smul_self (c : ℂ) (A : Wq →L[ℂ] Wp) :
    B.hsInner (c • A) A = c * ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [hsVec_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp

theorem pt_of_int (hI : CapAdjInt) {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) (s Y : ℂ)
    {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {g₀ : B.Mat k r}
    (hg₀ : g₀ ∈ B.GV k r) :
    B.opAdj (capTh k r Wp Wq s Y) ψ g₀ = conj s • Q.CV k r (conj Y) ψ g₀ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set Θ := capTh k r Wp Wq s Y
  set Ht : B.Mat k r → (Wq →L[ℂ] Wp) := fun g =>
    B.opAdj Θ ψ g - conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum with hHt
  have hCVg : ∀ g ∈ B.GV k r, Q.CV k r (conj Y) ψ g = (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum :=
    fun g hg => hCV _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg
  have hS : ContDiff ℝ ∞ (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) :=
    contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 ψ g) L fun cw _ => (rw_contDiff hψ _).const_smul _
  have hA : ContDiff ℝ ∞ (B.opAdj Θ ψ) := opAdj_capTh_contDiff s Y hψ
  have hHs : ContDiff ℝ ∞ Ht := hA.sub (hS.const_smul _)
  by_contra hne
  have hH0 : Ht g₀ ≠ 0 := by
    intro h0
    apply hne
    have := sub_eq_zero.1 h0
    rw [hCVg g₀ hg₀]
    exact this

  obtain ⟨β⟩ : Nonempty (ContDiffBump g₀) := ⟨⟨1, 2, one_pos, one_lt_two⟩⟩
  have hβs : ContDiff ℝ ∞ (fun g => ((β g : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hβc : HasCompactSupport (fun g => ((β g : ℝ) : ℂ)) :=
    β.hasCompactSupport.comp_left Complex.ofReal_zero
  set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • Ht g with hφ
  have hφs : ContDiff ℝ ∞ φ := hβs.smul hHs
  have hφc : HasCompactSupport φ := hβc.smul_right
  have hInt := hI k r Wp Wq s Y μ hμ φ ψ hφs hφc hψ hψc

  have hcont1 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x))) :=
    Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk hA.continuous)
  have hcs1 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x))) :=
    hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)
  have i1 := hcont1.integrable_of_hasCompactSupport (μ := μ) hcs1
  have hcont2 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x))
      (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)) :=
    Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk (hS.const_smul _).continuous)
  have hcs2 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x))
      (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)) :=
    hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)
  have i2 := hcont2.integrable_of_hasCompactSupport (μ := μ) hcs2
  have hae2 : (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x))) =ᵐ[μ]
      fun x => B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCVg _ hx]
  rw [integral_congr_ae hae2] at hInt

  set h : Mt k r → ℝ := fun x => β (Matrix.of x) * ‖B.hsVec (Ht (Matrix.of x))‖ ^ 2 with hh
  have hpt : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x)) -
      B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) =
      ((h x : ℝ) : ℂ) := by
    intro x
    rw [← hs_sub_right]
    show B.hsInner (((β (Matrix.of x) : ℝ) : ℂ) • Ht (Matrix.of x)) (Ht (Matrix.of x)) = _
    rw [hsInner_smul_self]
    simp [hh]
  have hzero : ∫ x, ((h x : ℝ) : ℂ) ∂μ = 0 := by
    rw [← integral_congr_ae (Eventually.of_forall hpt), integral_sub i1 i2, hInt, sub_self]
  have hnn : 0 ≤ h := fun x => mul_nonneg (β.nonneg) (sq_nonneg _)
  have hcv : Continuous (fun x : B.Mat k r => B.hsVec (Ht x)) :=
    ((Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).continuous.comp hHs.continuous).congr
      (fun x => Formalism.FourierDecayAlt.P.B5.hsL_apply _)
  have hcont : Continuous h := β.continuous.mul ((continuous_norm.comp hcv).pow 2)
  have hint : Integrable h μ := by
    have := (i1.sub i2).congr (Eventually.of_forall hpt)
    exact this.re.congr (Eventually.of_forall fun x => by simp)
  have hzero' : ∫ x, h x ∂μ = 0 := by
    have := hzero
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  have hae : h =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero'
  have hO : IsOpen {x : Mt k r | 0 < h x} := isOpen_lt continuous_const hcont
  have hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < h x} := by
    show 0 < β g₀ * ‖B.hsVec (Ht g₀)‖ ^ 2
    have h1 : β g₀ = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
    rw [h1, one_mul]
    have : B.hsVec (Ht g₀) ≠ 0 := fun h0 => hH0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by
      rw [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))
    positivity
  have hpos := haar_open_pos hμ hO (g₀ := g₀) hg₀ hg₀O
  apply hpos
  have : {x : Mt k r | 0 < h x} ⊆ {x | h x ≠ 0} := fun x hx => (ne_of_gt hx)
  exact measure_mono_null this (by simpa [Filter.EventuallyEq, ae_iff] using hae)

end pointwise

theorem capacity_adjoint_from_integral : CapAdjFromInt := by
  intro hI k r Wp Wq _ _ _ _ _ _ s Y F hF g₀ hg₀
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨U, F', hU, hg₀U, hc, he⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hg₀U
  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  set ψ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • F' g with hψ
  have hψs : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp β.contDiff).contDiffAt).smul
        ((hc.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_rfl))
    · have hx2 : ε ≤ dist x g₀ := by
        by_contra hlt
        exact hx (hball (Metric.mem_ball.2 (lt_of_not_ge hlt)))
      have hO : IsOpen {y : B.Mat k r | ε / 2 < dist y g₀} := isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hev : ∀ᶠ y in 𝓝 x, β y = 0 := by
        filter_upwards [hO.mem_nhds (show ε / 2 < dist x g₀ by linarith)] with y hy
        exact β.zero_of_le_dist (by rw [hβout]; exact le_of_lt hy)
      refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : Wq →L[ℂ] Wp)) ?_
      filter_upwards [hev] with y hy
      simp [hψ, hy]
  have hψc : HasCompactSupport ψ :=
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right
  have hV : IsOpen (Metric.ball g₀ (ε / 4)) := Metric.isOpen_ball
  have hagree : ∀ x ∈ Metric.ball g₀ (ε / 4), x ∈ B.GV k r → F x = ψ x := by
    intro x hx hxG
    have h1 : β x = 1 := β.one_of_mem_closedBall (by rw [hβin]; exact Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U := hball (Metric.ball_subset_ball (by linarith) hx)
    simp [hψ, h1, he x hxU hxG]
  have hg₀V : g₀ ∈ Metric.ball g₀ (ε / 4) := Metric.mem_ball_self (by positivity)
  have h1 := Formalism.FourierDecayAlt.P.JFxG.adj_local (capTh k r Wp Wq s Y) hV hagree g₀ hg₀V hg₀
  have h2 := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r _ (Metric.ball g₀ (ε / 4)) F ψ (conj Y) hV
    (ckOn_sub_set Set.inter_subset_right (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF))
    (ckOn_of_contDiff hψs _ _) (fun x hx => hagree x hx.1 hx.2) g₀ ⟨hg₀V, hg₀⟩
  rw [h1, h2]
  exact pt_of_int hI hμ s Y hψs hψc hg₀

theorem capAdj_of_int (hI : CapAdjInt) : CapAdj := capacity_adjoint_from_integral hI

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section smul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_smul' (M : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Wd.Ix S → RadSp k r z z' π π') (a : ℂ) :
    P5.act M (fun e => a • x e) = fun e => a • P5.act M x e := by
  funext e
  simp only [P5.act, map_smul, Finset.smul_sum]

theorem rrform_smul (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (i : Fin (r + 1)) (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ) :
    P5.RRform L st μ i w (fun e => a • x e) (fun e => a • y e) c = a * conj a * P5.RRform L st μ i w x y c := by
  unfold P5.RRform
  rw [act_smul']
  unfold P5.form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [HerA.pairAt_smul_left, HerA.pairAt_smul_right, ← Finset.mul_sum]
  ring

end smul

theorem isLocPt_snoc {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) {t : ℂ} (ht : t ≠ 0) :
    D.IsLocPt (h ++ [(1, t)]) (j + 1) := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact h1 b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨le_rfl, ht⟩
  · unfold D.ptSize at h2 ⊢
    rw [List.map_append, List.sum_append, h2]
    simp

theorem levW_below (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) {t : ℂ} (ht : t ≠ 0) :
    ‖t‖ ^ (-2 : ℤ) * (‖t‖ ^ (2 * (P.r - j) + P.k)) ^ 2 = KB.levW P (j + 1) t := by
  have hj' : j + 1 ≠ P.r + 1 := by omega
  unfold KB.levW
  rw [if_neg hj']
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ ht']
  congr 1
  unfold C.Mlev
  push_cast [Nat.cast_sub (show j ≤ P.r by omega)]
  ring

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of (hOne : PBO.FormOne) (hZN : PBO.ZetaNormExists) (hHP : HeadPic) : KB.RadHead := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' X μ L st Φ Φ' hD hZ hF hw hΦ hΦ' t ht
  let jF : Fin (P.r + 1) := ⟨j + 1, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
  obtain ⟨μs, hμs⟩ := hZN P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
  have hDs : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' Xs μs Ls sts p.l0 :=
    ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T, hT, hph⟩ :=
    Formalism.FourierDecayAlt.P.radial_transport_plus Wp Wq P p j hj X μ L st Xs μs Ls sts hD hZ hDs hμs t ht
  refine (hph (Fin w.length) (D.positionted w) Φ Φ' (fun _ => 1) 0).trans ?_
  have hl := isLocPt_snoc hh ht
  have hl' := isLocPt_snoc hh' ht

  set x2 := KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) hl.2 with hx2def
  set x2' := KB.slv p.T F (j + 1) hj w (h' ++ [(1, t)]) hl'.2 with hx2'def
  have hc2 : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl hF e
  have hc2' : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2
  obtain ⟨ε₂, hε₂, hx'⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2'
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)}, min ε₁ ε₂ ≤ ε' →
      JC.NiceCoef (p.T.bs (j + 1)) ε' G → JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) G :=
    fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2 e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2' e) := fun e => mono (min_le_right _ _) (hx' e)

  set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam0
  let b0 : Fin (JC.parLev P j).r := ⟨0, by change 0 < P.r - j; omega⟩
  let Φ2 := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ e)
  let Φ2' := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' e)
  have hpic : ∀ (hh₀ : C.LPt) (hhh : D.IsLocPt hh₀ j) (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
      (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T F j (by omega) w hh₀ hhh.2 e)) →
      ∀ e, ∀ y ∈ Q.DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        Subtype.val ((((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e)) y.1 y.2 =
          Q.resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _)
            (B.JF (p.T.bs jF) (KB.slv p.T F (j + 1) hj w (hh₀ ++ [(1, t)]) (isLocPt_snoc hhh ht).2 e)) y.1 y.2 := by
    intro hh₀ hhh Ψ hΨ e y hy
    have e1 := hT (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e) y.1 y.2
    have e2 := hHP Wp Wq P p F j hj w hh₀ hhh X μ L st Ψ hD hF hw hΨ t (isLocPt_snoc hhh ht) e y hy
    have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
    exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e2)).trans (hcl _)
  have hΦ2 := hpic h hh Φ hΦ
  have hΦ2' := hpic h' hh' Φ' hΦ'
  have hOne' := hOne Wp Wq P p.T jF Xs μs Ls sts p.l0 hDs hμs w x2 x2' Φ2 Φ2' (min ε₁ ε₂) hε hxn hxn' hΦ2 hΦ2'
  have hTΦ : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ a)) = fun a => ((lam : ℝ) : ℂ) • Φ2 a := by
    funext a
    simp only [Φ2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  have hTΦ' : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' a)) = fun a => ((lam : ℝ) : ℂ) • Φ2' a := by
    funext a
    simp only [Φ2', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  rw [hTΦ, hTΦ']
  have hRR : p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)]) = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := by
    unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hl, hl'⟩, dite_eq_left hj]
    rfl
  have key : P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := hOne'.symm
  calc _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0) :=
        congrArg _ (rrform_smul Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 (lam : ℂ))
    _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * D.formLev p.T (M.sgn P p.l0) jF w x2 x2') := by
        rw [key]
    _ = _ := by
        rw [hRR, ← levW_below P j hj ht, Complex.conj_ofReal, hlam]
        push_cast
        ring

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQ
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JAAssembleQQ : Prop :=
  JDHatOpQQ → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOpQQ → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTrQQ

theorem jAdjTrQQ_of_leaves (hA : JAAssembleQQ) (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp)
    (h12 : JAGroupAdj) (h13 : JALocCC) (h14 : JAFFStable) : JAdjTrQQ :=
  hA h1 hat_bounded_decay_holds transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable h7 transfer_star_bound_holds transfer_is_adjoint_holds phi_operator_transfer_holds h11
    h12 h13 h14

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjSCut
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def wsAdj {k r : ℕ} (L : List (ℂ × List (B.Mat k r))) (b : B.Mat k r → ℂ) (x : B.Mat k r) : ℂ :=
  (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x).sum

def CapAdjScalar : Prop :=
  ∀ (k r : ℕ) (Y : ℂ) (μ : Measure (Mt k r)), B.IsHaarOn (B.GV k r) μ → ∀ a b : B.Mat k r → ℂ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b →
    (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, a (Matrix.of x) * star (Q.CV k r (conj Y) b (Matrix.of x)) ∂μ

def CapAdjIntOfScalar : Prop := CapAdjScalar → CapAdjInt

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

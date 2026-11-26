module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.GeneratingFunctionPolynomial
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ProductMoment
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.EigStrOfMem
noncomputable section

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants
open CompanionTheory.LimBd.Main (GfPoly SpanPow CoefSmooth CoefCC CoefEig PhZero BetaInfZero ZuckT ZuckDualT Box KDecay Wsp
  Letters wsp_ckOn wsp_inCC wsp_eig wsp_orth smul_mem_iSup gap_of_box norm_capP_le)
open CompanionTheory.WaveGrid.Coef

section w

variable {k r : ℕ} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}

theorem w_inCC (hK : PI.KFinSmooth) (hC : CoefCC) {A h : ℝ} (hD : KDecay k r ε A h)
    (hg : PI.ZuckTensor.GapAtLeast ε μ h) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) (m : ℕ) :
    B.InCC A m F := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    exact hC hK k r ε A h hD μ φ _ T m hφ hg
  | zero => exact JCx2.sq_inCC_zero
  | add F F' _ _ h h' => exact JCx2.sq_inCC_add h h'
  | smul c F _ h => exact JCx2.sq_inCC_smul c h

theorem mul_mem_box (h2 : SpanPow) {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {h : ℝ} {d : ℕ}
    {q : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d) (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (ht : t _ ε + 1 + 2 * (d : ℝ) < h) (L : Wq' →L[ℂ] Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε μ) :
    (fun g => q g • (F g).comp L) ∈ ⨆ ν : Box μ (d : ℝ), Wsp k r Wp Wq' ε ν := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    have := smul_mem_iSup (h2 t hZ hZd k r ε μ h d q φ hq hφ hg ht) (T.comp L)
    convert this using 2 with g
    rw [ContinuousLinearMap.smul_comp, smul_smul, Pi.mul_apply]
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add F F' _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp [ContinuousLinearMap.add_comp]
  | smul c F _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_comp]
    rw [smul_comm]

end w

section place

variable {P : M.Par} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wq']

theorem w_ffkb (hK : PI.KFinSmooth) (hS : CoefSmooth) (hE : CoefEig) (hB : SmoothKB)
    (p : KB.Pl P Wp Wq) {ε : Fin (2 * P.r + P.k + 1) → Bool} {μ : Fin (2 * P.r + P.k + 1) → ℝ}
    {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hf : f ∈ Wsp P.k P.r Wp Wq ε μ) {A : ℝ}
    (hA : ∀ m, m ≤ CompanionTheory.JfS.NN P.k P.r → JF.TransportedAlt P.k P.r A m) (hcc : ∀ m : ℕ, B.InCC A m f) :
    B.JF p.T.base f ∈ FFKB p := by
  have hs := hB P Wp Wq p f A hA (wsp_ckOn hK hS hf) hcc fun Y => ⟨_, wsp_eig hK hS hE _ hf⟩
  exact EqShift.jf_ff_of_smooth p.T.base f (OmKB p) fun g₀ hg₀ =>
    hs g₀ ⟨hg₀.1, (CutMP.jdc_om_of _ _ hg₀.1.1 hg₀.2).2⟩

theorem eigStr_of_mem (h3 : CoefSmooth) (h4 : CoefCC) (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero)
    (hK : PI.KFinSmooth) (p : KB.Pl P Wp Wq) (F F₁ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ d : ℝ}
    (hF₁ : F₁ ∈ ⨆ ν : Box lam d, Wsp P.k P.r Wp Wq ε ν) (hFF : ∀ g ∈ B.GV P.k P.r, F g = F₁ g)
    (hgap : PI.ZuckTensor.GapAtLeast ε lam h) (hA : B.AB P.k P.r ≤ A) (hD : KDecay P.k P.r ε A h₀)
    (hh : h₀ + 2 * d ≤ h) (hnn : ∀ y, LetPt Y y → CompanionTheory.LimBd.Main.PStar lam d y ≤ nn y) : EigStr p nn F Y := by
  classical
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ F₁).1 hF₁
  let e := c.support.equivFin.symm
  have hgν : ∀ ν : Box lam d, PI.ZuckTensor.GapAtLeast ε ν.1 h₀ := fun ν => gap_of_box ν.2 hgap hh
  have hFs : ∀ g ∈ B.GV P.k P.r, F g = ∑ i, c (e i) g := by
    intro g hg
    rw [hFF g hg, ← hsum, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp e fun ν : c.support => c ν g).symm
  exact ⟨A, c.support.card, fun i => c (e i), fun i y => Formalism.QuantumDeterminants.capP (fun s => ((e i).1.1 s : ℂ)) (y : ℂ), hA,
    fun i => wsp_ckOn hK h3 (hc _), fun i => wsp_inCC hK h4 hD (hgν _) (hc _), hFs,
    fun i y _ => wsp_eig hK h3 h5 _ (hc _), fun i y hy => (norm_capP_le (e i).1.2 y).trans (hnn y hy),
    fun i j hij => wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _) (hgν _)
      (fun hh' => hij (e.injective (Subtype.ext (Subtype.ext hh')))) (hc _) (hc _)⟩

theorem eigStr_fpmW (h1 : GfPoly) (h2 : SpanPow) (h3 : CoefSmooth) (h4 : CoefCC)
    (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ : ℝ}
    (hf : f ∈ Wsp P.k P.r Wp Wq ε lam) (hgap : PI.ZuckTensor.GapAtLeast ε lam h)
    (ht : t _ ε + 1 + 2 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) < h) (hA : B.AB P.k P.r ≤ A) (hD : KDecay P.k P.r ε A h₀)
    (hh : h₀ + 2 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ h)
    (hnn : ∀ y, LetPt Y y → CompanionTheory.LimBd.Main.PStar lam (((2 * P.r + 2) * p₀ : ℕ) : ℝ) y ≤ nn y) :
    EigStr p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y :=
  eigStr_of_mem h3 h4 h5 h6 h7 hK p _ _ nn Y
    (mul_mem_box h2 hZ hZd (h1 P.k P.r p.T.base.z p.T.base.z' p₀) hgap ht (ContinuousLinearMap.id ℂ Wq) hf)
    (fun _ _ => rfl) hgap hA hD hh hnn

theorem eigStr_fpmShW {u u' : ℕ → ℝ} (h1 : GfPoly) (h2 : SpanPow) (h3 : CoefSmooth) (h4 : CoefCC)
    (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    (p : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq))
    (p₀ e₀ : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ : ℝ}
    (hf : f ∈ Wsp P.k P.r Wp Wq ε lam) (hAop : PolyOp e₀ Aop) (hgap : PI.ZuckTensor.GapAtLeast ε lam h)
    (ht : t _ ε + 1 + 2 * (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) < h) (hA : B.AB P.k P.r ≤ A)
    (hD : KDecay P.k P.r ε A h₀) (hh : h₀ + 2 * (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) ≤ h)
    (hnn : ∀ y, LetPt Y y → CompanionTheory.LimBd.Main.PStar lam (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) y ≤ nn y) :
    EigStr p nn (fpmSh p f Aop p₀) Y := by
  obtain ⟨n, cf, L, hcf, hAe⟩ := hAop
  set q : B.Mat P.k P.r → ℂ := fun g => ((Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) with hq
  refine eigStr_of_mem h3 h4 h5 h6 h7 hK p _ (∑ i, fun g => (q * cf i) g • (f g).comp (L i)) nn Y
    (Submodule.sum_mem _ fun i _ => mul_mem_box h2 hZ hZd
      (LimSh.mul_mem_letters_pow (h1 P.k P.r _ _ p₀) (LimSh.polyDeg_mem (hcf i))) hgap ht (L i) hf)
    (fun g _ => ?_) hgap hA hD hh hnn
  show q g • (f g).comp (Aop g) = _
  rw [hAe g, ContinuousLinearMap.comp_finsetSum, Finset.smul_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.comp_smul, smul_smul]
  rfl

end place

def EndDiffW (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ Cb C₃ CT C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CT → 1 / 2 ≤ C₀ →
    ∃ C₄ CA : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (p₀ : ℕ)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ε : Fin (2 * P.r + P.k + 1) → Bool) (c g e h : ℝ),
      f ∈ Wsp P.k P.r Wp Wq ε lam' → lam' ∈ Box lam e → e + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ c →
      PI.ZuckTensor.GapAtLeast ε lam' h → t _ ε + CA * thrX P.k P.r + 3 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) + 1 < h →
      HypLam P.k P.r lam c g b → HypType P.k P.r lam P.u b → HypType P.k P.r lam P.u' b →
      b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' → 1 ≤ Tq p →
      30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0| →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) → ThmBpAt p f b C₄ 0 p₀

def EndEqW (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ C₃ CT C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CT → 1 / 2 ≤ C₀ →
    ∃ C₄ CA : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (p₀ n₀ l : ℕ)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ε : Fin (2 * P.r + P.k + 1) → Bool) (c g e h : ℝ),
      f ∈ Wsp P.k P.r Wp Wq ε lam' → lam' ∈ Box lam e → e + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c →
      PI.ZuckTensor.GapAtLeast ε lam' h →
      t _ ε + CA * thrX P.k P.r + 3 * (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) + 1 < h →
      HypLam P.k P.r lam c g b → HypType P.k P.r lam P.u b → P.u = P.u' →
      b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' → 1 ≤ Tq p →
      n₀ = 30 * (P.r + 1) ^ 2 + 6 → 1 ≤ l → l < P.k → (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1) →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) → ThmBpAt p f b C₄ n₀ p₀

theorem endDiffW_of (hAsm : AsmDiff) (hS : LimSteps) (hB : SmoothKB) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) : EndDiffW t := by
  intro Cb C₃ CT C₀ hC₃ hCT hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', H⟩ := hAsm Cb C₃ (6 + CT) C₀ hC₃ (by linarith) hC₀
  set CA : ℝ := max (max (max c₃ Cc) (max Cc' Cc'')) 46 with hCA
  have k0 : 46 ≤ CA := le_max_right _ _
  have k1 : c₃ ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have k2 : Cc ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have k3 : Cc' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have k4 : Cc'' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  refine ⟨C₄, CA, ?_⟩
  intro Wp Wq _ _ _ _ _ _ _ P p f b p₀ lam lam' ε c g e h hfK hbox hec hgap hh hL hu hu' hTT hT hlen hN hp₀ hCb hexp
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hS
  have hd : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : 0 ≤ CA * thrX P.k P.r := mul_nonneg (by linarith) (thrX_nonneg _ _)
  have hD := kDecay_of_gap hZ P.k P.r ε hX hd hh
  have hfA := w_inCC hK s4 hD (gap_mono hgap (by linarith)) hfK
  have hXA : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hXA' : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    linarith
  have hc : 0 < c := by linarith [hL.c_ge]
  obtain ⟨hW, hLi⟩ := grids_diff p lam c g b hL hu hu' hlen
  obtain ⟨hΛ1, hΛ2⟩ := gridΛ_bounds p b CT hL.b_ge_three hCT hTT
  exact H Wp Wq P p f b _ _ p₀ Topx2.chi0 (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) 3 (3 * (P.r + 1)) hL.b_ge_three
    hΛ1 hΛ2 hT hp₀ le_rfl (by omega) Topx2.base_cutoff_is_truncation (PStar_pos lam hc) hCb (wsp_ckOn hK s3 hfK) hfA
    (w_ffkb hK s3 s5 hB p hfK (fun m hm => thr_JF _ _ m hm k0 hXA) hfA)
    (thr_conv _ _ k1 (by linarith) hXA') (thr_main _ _ k2 hXA') (thr_main _ _ k3 hXA') (thr_main _ _ k4 hXA') hN hexp
    hW hLi
    (limBd_of_eigStr p _ _ _ _ (eigStr_fpmW s1 s2 s3 s4 s5 s6 s7 hK hZ hZd p f p₀ _ _ hfK hgap (by linarith)
      (thr_AB _ _ k0 hXA) hD (by linarith) fun y _ => pStar_box hbox hd hec y))

theorem endEqW_of (hAsm : AsmEq) (hW : WigExists) (hS : LimSteps) (hB : SmoothKB) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) : EndEqW t := by
  intro C₃ CT C₀ hC₃ hCT hC₀
  obtain ⟨Cb, c₅, -, hSh⟩ := EqShift.shiftAtR_full hW
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', H⟩ := hAsm Cb C₃ (6 + CT) C₀ hC₃ (by linarith) hC₀
  set CA : ℝ := max (max (max c₃ Cc) (max Cc' Cc'')) (max 46 c₅) with hCA
  have k0 : 46 ≤ CA := le_max_of_le_right (le_max_left _ _)
  have k5 : c₅ ≤ CA := le_max_of_le_right (le_max_right _ _)
  have k1 : c₃ ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have k2 : Cc ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have k3 : Cc' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have k4 : Cc'' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  refine ⟨C₄, CA, ?_⟩
  intro Wp Wq _ _ _ _ _ _ _ P p f b p₀ n₀ l lam lam' ε c g e h hfK hbox hec hgap hh hL hu huu hTT hT hn₀ hl1 hlk hposition
    hN hp₀ hexp
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hS
  have hd : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : 0 ≤ CA * thrX P.k P.r := mul_nonneg (by linarith) (thrX_nonneg _ _)
  have hD := kDecay_of_gap hZ P.k P.r ε hX hd hh
  have hfA := w_inCC hK s4 hD (gap_mono hgap (by linarith)) hfK
  have hXA : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := by linarith
  have hXA' : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) -
      (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    linarith
  have hc : 0 < c := by linarith [hL.c_ge]
  have hJ := w_ffkb hK s3 s5 hB p hfK (fun m hm => thr_JF _ _ m hm k0 hXA) hfA
  obtain ⟨S, e1, e2, e3, e4, e5, e6, hDp, hDm, hJp, hJm⟩ := hSh P Wp Wq p f b n₀ l _ huu hl1 hlk (huu ▸ hposition)
    hL.b_ge_three (fun i hi => huu ▸ hu.u_le i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2)
    (thr_conv _ _ k5 (by linarith) hXA) (thr_JF _ _ _ (Nat.zero_le _) k0 hXA) (hfA 1) (hfA 0) hJ
  rw [← huu] at e2 e4
  obtain ⟨hWp, hLip⟩ := grids_plus S.pp lam c g b l n₀ hL hu hn₀ hl1 hlk hposition e1 e2 e5
  obtain ⟨hWm, hLim⟩ := grids_minus S.pm lam c g b l n₀ hL hu hn₀ hl1 hlk hposition e3 e4 e6
  obtain ⟨hΛ1, hΛ2⟩ := gridΛ_bounds p b CT hL.b_ge_three hCT hTT
  exact H P Wp Wq p f b n₀ S _ _ p₀ Topx2.chi0 (PStar lam c) (PStar lam c)
    (gridY (shP P S.up S.up') S.pp.l0 (3 * (P.r + 1))) (gridY (shP P S.um S.um') S.pm.l0 (3 * (P.r + 1))) 3
    (3 * (P.r + 1)) hL.b_ge_three hΛ1 hΛ2 hT hn₀.le hp₀ le_rfl (by omega) Topx2.base_cutoff_is_truncation (PStar_pos lam hc)
    (PStar_pos lam hc) hDp hDm (wsp_ckOn hK s3 hfK) hfA hJp hJm
    (thr_conv _ _ k1 (by linarith) hXA') (thr_main _ _ k2 hXA') (thr_main _ _ k3 hXA') (thr_main _ _ k4 hXA') hN hexp
    hWp hLip hWm hLim
    (limBd_of_eigStr S.pp _ _ _ _ (eigStr_fpmShW s1 s2 s3 s4 s5 s6 s7 hK hZ hZd S.pp f S.Ap p₀ _ _ _ hfK S.polyP
      hgap (by linarith) (thr_AB _ _ k0 hXA) hD (by linarith) fun y _ => pStar_box hbox hd hec y))
    (limBd_of_eigStr S.pm _ _ _ _ (eigStr_fpmShW s1 s2 s3 s4 s5 s6 s7 hK hZ hZd S.pm f S.Am p₀ _ _ _ hfK S.polyM
      hgap (by linarith) (thr_AB _ _ k0 hXA) hD (by linarith) fun y _ => pStar_box hbox hd hec y))

end CompanionTheory.WaveGrid
end
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.SpanBall
noncomputable section

namespace CompanionTheory.WaveGrid.SpanBall

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P PI.UpqRep Matrix CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace

def steps (n : ℕ) : Finset (Fin n → ℤ) :=
  insert 0 (Finset.univ.image (fun s : Fin n => (Pi.single s 1 : Fin n → ℤ)) ∪
    Finset.univ.image fun s : Fin n => -(Pi.single s 1 : Fin n → ℤ))

def ball (n : ℕ) : ℕ → Finset (Fin n → ℤ)
  | 0 => {0}
  | e + 1 => Finset.image₂ (· + ·) (ball n e) (steps n)

theorem zero_mem_steps (n : ℕ) : (0 : Fin n → ℤ) ∈ steps n := Finset.mem_insert_self _ _

theorem single_mem_steps {n : ℕ} (s : Fin n) : (Pi.single s 1 : Fin n → ℤ) ∈ steps n :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

theorem neg_single_mem_steps {n : ℕ} (s : Fin n) : -(Pi.single s 1 : Fin n → ℤ) ∈ steps n :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

theorem card_steps (n : ℕ) : (steps n).card ≤ 2 * n + 1 := by
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) 1)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun s : Fin n => (Pi.single s 1 : Fin n → ℤ))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
    (f := fun s : Fin n => -(Pi.single s 1 : Fin n → ℤ))
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

theorem card_ball (n : ℕ) : ∀ e, (ball n e).card ≤ (2 * n + 1) ^ e
  | 0 => by simp [ball]
  | e + 1 => by
    rw [pow_succ]
    exact Finset.card_image₂_le _ _ _ |>.trans (Nat.mul_le_mul (card_ball n e) (card_steps n))

theorem sum_natAbs_le_one_of_mem_unitShifts {n : ℕ} {s : Fin n → ℤ} (h : s ∈ steps n) : ∑ i, (s i).natAbs ≤ 1 := by
  have key : ∀ t : Fin n, ∑ i, ((Pi.single t 1 : Fin n → ℤ) i).natAbs = 1 := fun t => by
    rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [steps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp
  · exact (key t).le
  · simpa only [Pi.neg_apply, Int.natAbs_neg] using (key t).le

theorem sum_natAbs_le_of_mem_ball {n : ℕ} : ∀ e, ∀ ν ∈ ball n e, ∑ i, (ν i).natAbs ≤ e := by
  intro e
  induction e with
  | zero =>
    intro ν h
    rw [ball, Finset.mem_singleton] at h
    simp [h]
  | succ e ih =>
    intro ν h
    rw [ball, Finset.mem_image₂] at h
    obtain ⟨x, hx, s, hs, rfl⟩ := h
    have h1 := ih x hx
    have h2 := sum_natAbs_le_one_of_mem_unitShifts hs
    have h3 : ∑ i, ((x + s) i).natAbs ≤ ∑ i, (x i).natAbs + ∑ i, (s i).natAbs := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _
    omega

theorem abs_ball {n e : ℕ} {ν : Fin n → ℤ} (h : ν ∈ ball n e) (a : Fin n) : |(ν a : ℝ)| ≤ e := by
  have h1 : (ν a).natAbs ≤ e := le_trans
    (Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (sum_natAbs_le_of_mem_ball e ν h)
  have h2 : (((ν a).natAbs : ℕ) : ℝ) ≤ e := by exact_mod_cast h1
  rwa [Nat.cast_natAbs, Int.cast_abs] at h2

theorem add_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ + Pi.single s 1 = fun a => μ a + ((Pi.single s 1 : Fin n → ℤ) a : ℝ) := by
  funext a
  by_cases h : a = s
  · subst h; simp
  · simp [h]

theorem sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ - Pi.single s 1 = fun a => μ a + ((-(Pi.single s 1 : Fin n → ℤ)) a : ℝ) := by
  funext a
  by_cases h : a = s
  · subst h; simp [sub_eq_add_neg]
  · simp [h]

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def spanOn (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (S : Finset (Fin (2 * r + k + 1) → ℤ)) : Submodule ℂ (B.Mat k r → ℂ) :=
  Submodule.span ℂ {φ | ∃ ν ∈ S, IsCoef k r ε (fun a => lam a + (ν a : ℝ)) φ}

theorem mem_spanStep_of_eq {μ : Fin (2 * r + k + 1) → ℝ} {φ ψ ψ' : B.Mat k r → ℂ} (hφ : IsCoef k r ε μ φ)
    (hψ' : ψ' ∈ spanOn k r ε μ (steps _)) (h : ∀ g ∈ B.GV k r, ψ g = ψ' g) : ψ ∈ spanOn k r ε μ (steps _) := by
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, hw, -⟩ := hφ
  have h1 : IsCoef k r ε μ (ψ - ψ') :=
    ⟨H, i1, i2, i3, σ, 0, w, hμ, hσ, kfin_zero σ, hw, fun g hg => by simp [h g hg]⟩
  have h0 : ψ - ψ' ∈ spanOn k r ε μ (steps _) := Submodule.subset_span ⟨0, zero_mem_steps _, by simpa using h1⟩
  simpa using Submodule.add_mem _ h0 hψ'

theorem letterStep {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {μ : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} {q φ : B.Mat k r → ℂ} (hq : IsLetter k r q) (hφ : IsCoef k r ε μ φ) (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (hlt : t _ ε + 1 < h) : q * φ ∈ spanOn k r ε μ (steps _) := by
  rcases hq with rfl | ⟨x, y, hq⟩
  · rw [one_mul]
    exact Submodule.subset_span ⟨0, zero_mem_steps _, by simpa using hφ⟩
  have hφ' := hφ
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, ⟨P, hP, hτ⟩, hv, hw, hφG⟩ := hφ'
  rw [kfin_iff hP] at hv hw
  rcases hq with hq | hq
  · obtain ⟨X⟩ := hZ _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanStep_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, single_mem_steps (sI i),
        add_single μ (sI i) ▸ isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    simp only [back_forth hP.1, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]
  · obtain ⟨X⟩ := hZd _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanStep_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, neg_single_mem_steps (sI i),
        sub_single μ (sI i) ▸ isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    have hi : (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    simp only [back_forth hP.1, hi, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]

theorem spanBall {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {lam : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (d : ℕ) {q φ : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d) (hφ : IsCoef k r ε lam φ)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) :
    q * φ ∈ spanOn k r ε lam (ball _ d) := by
  induction d generalizing q with
  | zero =>
    rw [pow_zero, Submodule.mem_one] at hq
    obtain ⟨c, rfl⟩ := hq
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, Finset.mem_singleton_self _, by simpa using hφ⟩)
  | succ d ih =>
    push_cast at hlt
    have step : Letters k r * spanOn k r ε lam (ball _ d) ≤ spanOn k r ε lam (ball _ (d + 1)) := by
      unfold Letters
      rw [spanOn, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨ν, hν, hb⟩, rfl⟩
      have hgμ : PI.ZuckTensor.GapAtLeast ε (fun a => lam a + (ν a : ℝ)) (h - 2 * d) :=
        gap_of_box (lam := lam) (μ := fun a => lam a + (ν a : ℝ)) (c := d) (fun s => by simpa using abs_ball hν s) hg (by linarith)
      refine Submodule.span_mono ?_ (letterStep hZ hZd ha hb hgμ (by linarith))
      rintro ψ ⟨s, hs, hψ⟩
      refine ⟨ν + s, Finset.mem_image₂_of_mem hν hs, ?_⟩
      simpa only [Pi.add_apply, Int.cast_add, add_assoc] using hψ
    rw [pow_succ'] at hq
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [mul_assoc]
      exact step (Submodule.mul_mem_mul ha (ih hb (by linarith)))
    · rw [add_mul]
      exact Submodule.add_mem _ ha hb

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sumOn (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (S : Finset (Fin (2 * r + k + 1) → ℤ)) : Submodule ℂ (B.Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {G | ∃ F : (Fin (2 * r + k + 1) → ℤ) → B.Mat k r → (Wq →L[ℂ] Wp),
    (∀ ν, F ν ∈ Wsp k r Wp Wq ε fun a => lam a + (ν a : ℝ)) ∧ G = ∑ ν ∈ S, F ν}
  add_mem' := by
    rintro _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
    exact ⟨F + F', fun ν => Submodule.add_mem _ (hF ν) (hF' ν), by simp [Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
  smul_mem' := by
    rintro c _ ⟨F, hF, rfl⟩
    exact ⟨c • F, fun ν => Submodule.smul_mem _ c (hF ν), by simp [Finset.smul_sum]⟩

theorem smul_mem_sumOn {lam : Fin (2 * r + k + 1) → ℝ} {S : Finset (Fin (2 * r + k + 1) → ℤ)} {φ : B.Mat k r → ℂ}
    (hφ : φ ∈ spanOn k r ε lam S) (T : Wq →L[ℂ] Wp) : (fun g => φ g • T) ∈ sumOn k r Wp Wq ε lam S := by
  classical
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ν, hν, h⟩ := h
    refine ⟨fun ν' => if ν' = ν then fun g => φ g • T else 0, fun ν' => ?_, by simp [hν]⟩
    dsimp only
    split_ifs with e
    · subst e
      exact Submodule.subset_span ⟨φ, T, h, rfl⟩
    · exact Submodule.zero_mem _
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add φ ψ _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp [add_smul]
  | smul c φ _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp [smul_smul]

theorem mul_mem_sumOn {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} {d : ℕ} {q : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε lam) : (fun g => q g • F g) ∈ sumOn k r Wp Wq ε lam (ball _ d) := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    convert smul_mem_sumOn (spanBall hZ hZd d hq hφ hg hlt) T using 2 with g
    rw [smul_smul, Pi.mul_apply]
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add F F' _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp
  | smul c F _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp only [Pi.smul_apply]
    rw [smul_comm]

end CompanionTheory.WaveGrid.SpanBall
end
end

noncomputable section

namespace CompanionTheory.WaveGrid.WAt

open MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants CompanionTheory.WaveGrid CompanionTheory.WaveGrid.SpanBall
open CompanionTheory.WaveGrid.MomL (mnr momL ew_sum_le)
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT KDecay Wsp Letters IsCoef wsp_orth gap_of_box CoefCC CoefEig PhZero BetaInfZero)
open scoped InnerProductSpace ENNReal

def UniqG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), IsHCParam lam →
    ∀ h : ℝ, GapAtLeast ε lam h → ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 + 1 < h →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : B.Mat k r → (H' →L[ℂ] H')),
      PI.UpqRep.IsDSHpk k r ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UH (Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

section one

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem kfin_map {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {σ : B.Mat k r → (H →L[ℂ] H)} {σ' : B.Mat k r → (H' →L[ℂ] H')} (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ UH (Hpk k r), ∀ x, U (σ g x) = σ' g (U x)) {v : H} (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) :
    PI.UpqRep.IsKFinHpk (k := k) (r := r) σ' (U v) := by
  obtain ⟨S, hS, hvS, hst⟩ := hv
  refine ⟨S.map U.toLinearEquiv.toLinearMap, inferInstance, Submodule.mem_map_of_mem hvS, ?_⟩
  rintro g hg _ ⟨x, hx, rfl⟩
  exact ⟨σ g x, hst g hg x hx, hU g hg.1 x⟩

theorem coefOf_of_wsp (hU : UniqG) (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (hg : GapAtLeast ε μ h) (hh : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 + 1 < h) (R : BranchingSupport.Rep k r) (hR : R.IsDS ε μ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) : BallW.CoefOf R F := by
  have key : ∃ (ι : Type) (_ : Fintype ι) (x y : ι → R.H) (X : ι → (Wq →L[ℂ] Wp)),
      (∀ i, x i ∈ R.TK ∧ y i ∈ R.TK) ∧ ∀ g ∈ B.GV k r, F g = ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i := by
    have hTK := (GlobalTheory.rep_basic_of_isDS hK k r ε μ R hR).2.2.2.2.2.2.1
    induction hF using Submodule.span_induction with
    | mem F h' =>
      obtain ⟨φ, T, ⟨H, i1, i2, i3, σ, v, w, -, hσ, hv, hw, hφ⟩, rfl⟩ := h'
      obtain ⟨U, hUσ⟩ := hU k r ε μ hR.1 h hg hh H σ hσ R.H R.σ hR.2
      refine ⟨Unit, inferInstance, fun _ => U w, fun _ => U v, fun _ => T,
        fun _ => ⟨hTK _ (kfin_map U hUσ hw), hTK _ (kfin_map U hUσ hv)⟩, fun g hg => ?_⟩
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hφ g hg, ← hUσ g hg, U.inner_map_map]
    | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, Empty.elim, fun i => i.elim, fun g _ => by have : IsEmpty Empty := ⟨Empty.elim⟩; simp⟩
    | add F F' _ _ h h' =>
      obtain ⟨ι, _, x, y, X, h1, h2⟩ := h
      obtain ⟨ι', _, x', y', X', h1', h2'⟩ := h'
      refine ⟨ι ⊕ ι', inferInstance, Sum.elim x x', Sum.elim y y', Sum.elim X X', ?_, fun g hg => ?_⟩
      · rintro (i | i)
        exacts [h1 i, h1' i]
      · rw [Fintype.sum_sum_type, Pi.add_apply, h2 g hg, h2' g hg]
        rfl
    | smul c F _ h =>
      obtain ⟨ι, _, x, y, X, h1, h2⟩ := h
      refine ⟨ι, inferInstance, x, y, fun i => c • X i, h1, fun g hg => ?_⟩
      rw [Pi.smul_apply, h2 g hg, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  obtain ⟨ι, _, x, y, X, h1, h2⟩ := key
  intro l l'
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, Fintype.card ι, fun i => x (e i), fun i => y (e i), fun i => X (e i), fun i => h1 _, fun g hg => ?_, rfl⟩
  rw [h2 g hg]
  exact (Equiv.sum_comp e fun i => ⟪x i, R.σ g (y i)⟫_ℂ • X i).symm

theorem bound_of_inCC {A : ℝ} {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : B.InCC A m F) :
    ContinuousOn F (B.GV k r) ∧ ∃ c, 0 ≤ c ∧ ∀ g ∈ B.GV k r, ‖F g‖ ≤ c * B.gN g ^ (-A) := by
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨GlobalTheory.CoefZero.continuousOn_of_ckOn hc1, max c 0, le_max_right _ _, fun g hg => ?_⟩
  have h1 : B.gN g ^ A * ‖F g‖ ≤ c := hc2 [] [] (by simp) (by simp) (by simp) g hg
  have hp := BetaSesquilinearity.gN_pos hg
  rw [Real.rpow_neg hp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hp _), mul_comm]
  exact h1.trans (le_max_left _ _)

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem normSq_eq (hk : 2 ≤ k) (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A 5 F) : B.normSq D F = ENNReal.ofReal (B.beta D F F).re := by
  obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := b_any_of_xi k r Wp Wq D A hA
  obtain ⟨c, hc⟩ := JCx2.sq_inCC_mono le_rfl (by norm_num : 4 ≤ 5) hF
  have hfin := (hC F F c c hF hF hc hc).1
  set g : (Fin r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _)
  have hJ : StronglyMeasurable fun q : (Fin r → ℂ) × ℂ => B7.JM D F (1, 1) q :=
    (B7.sm_JM D (bound_of_inCC hF).1).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin r → ℂ) × ℂ => ‖B7.hsL (B7.JM D F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hgm : Measurable g := by
    have e : g = fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B7.hsL (B7.JM D F (1, 1) q)‖ ^ 2 := by
      funext q
      by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
      · simp only [hg, hw, zero_mul]
      have hw' := hw
      unfold bcWeight at hw'
      split_ifs at hw' with hle
      · have hq : q ∈ B7.Q0 D := by
          refine ⟨fun a ha => left_ne_zero_of_mul hw' (Finset.prod_eq_zero (Finset.mem_univ a) ?_), ?_⟩
          · rw [ha, norm_zero, zero_pow]
            unfold Mdim
            have := a.isLt
            omega
          · refine hle.lt_or_eq.resolve_right fun h => right_ne_zero_of_mul hw' ?_
            rw [← h, sub_self, zero_pow (by omega)]
        rw [B7.JM_eq D F (1, 1) hq, bessel_function_trivial_index k r Wp Wq D F, B7.hsL_apply]
      · exact absurd rfl hw'
    rw [e]
    exact (B7.measurable_bcWeight _ _).mul (hN.pow_const 2)
  have hβ : B.beta D F F = ((∫ q, g q : ℝ) : ℂ) := by
    unfold B.beta betaBig
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    rw [inner_self_eq_norm_sq_to_K]
    push_cast [hg]
    rfl
  rw [hβ, Complex.ofReal_re, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
    hgm.aestronglyMeasurable]
  exact (ENNReal.ofReal_toReal hfin).symm

theorem normSq_le_sum (hk : 2 ≤ k) (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type} (S : Finset ι)
    (F : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ i ∈ S, B.InCC A 5 (F i))
    (ho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → B.beta D (F i) (F j) = 0) {i : ι} (hi : i ∈ S) :
    B.normSq D (F i) ≤ B.normSq D (∑ j ∈ S, F j) := by
  classical
  have e : (∑ j ∈ S, F j) = fun g => ∑ j : S, F j g := by
    funext g
    rw [Finset.sum_apply, Finset.sum_coe_sort S (fun j => F j g)]
  have hS : B.InCC A 5 fun g => ∑ j : S, F j g := JCx2.sq_inCC_sum _ _ fun j _ => hF j j.2
  have h1 : ∀ j : S, B.beta D (fun g => ∑ l : S, F l g) (F j) = B.beta D (F j) (F j) := fun j => by
    have h := CutBP.beta_sum_left D hA (fun _ : S => (1 : ℂ)) (fun l : S => F l) (fun l => hF l l.2) (hF j j.2)
      Finset.univ
    simp only [one_smul, one_mul] at h
    exact h.trans (Finset.sum_eq_single j (fun l _ hl => ho l l.2 j j.2 fun e => hl (Subtype.ext e))
      fun h => absurd (Finset.mem_univ j) h)
  have h2 := (CutBP.beta_sum_right D hA (fun j : S => F j) (fun j => hF j j.2) hS Finset.univ).trans
    (Finset.sum_congr rfl fun j _ => h1 j)
  have h3 : ∀ j : S, 0 ≤ (B.beta D (F j) (F j)).re := fun j => by
    obtain ⟨t, ht, e⟩ := CutBP.beta_self_real D (F j)
    rw [e, Complex.ofReal_re]
    exact ht
  have h4 := normSq_eq hk D hA hS
  rw [h2, Complex.re_sum] at h4
  rw [e, h4, normSq_eq hk D hA (hF i hi)]
  have h5 := Finset.single_le_sum (f := fun j : S => (B.beta D (F j) (F j)).re) (fun j _ => h3 j)
    (Finset.mem_univ (⟨i, hi⟩ : S))
  exact ENNReal.ofReal_le_ofReal h5

end one

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem V_dmin (p : KB.Pl P Wp Wq) {f F₀ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (he : ∀ g ∈ B.GV P.k P.r, F₀ g = f g) {j : ℕ}
    (hj : j ≤ P.r) (a : ℕ) (γ : C.LPt) (h0 : mnr hj γ ^ a ≠ 0) :
    p.V (fun g => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ ^ a • F₀ g) γ = mnr hj γ ^ a • p.V f γ := by
  unfold KB.Pl.V D.vecV
  split_ifs with h1 h2
  · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ h0
    filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
    have hGq : Dmin P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) ⟨j + 1, by omega⟩ = mnr hj γ := by
      rw [BigCellZetaMinors.dmin_sgs _ hq]
      unfold Dmin mnr
      rw [h2.choose_spec.2.1]
    unfold D.orbIntegrand B.rho
    simp only [hGq, he _ (B7.sgs_mem p.T.base hq h2.choose_spec.1), ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
    rw [smul_comm]
  · simp
  · simp

theorem mnr_bigPt_ne {r j : ℕ} (hj : j ≤ r) (c : Fin (r + 1) → ℂ) (hc : D.IsLocPt (TBB.bigPt r c) (r + 1)) :
    mnr hj (TBB.bigPt r c) ≠ 0 := by
  unfold mnr
  rw [show D.ptMatN (TBB.bigPt r c) (r + 1) = _ from PBJ.Dens.ptMatN_bigPt c, PBM.hMat_one,
    Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun a _ =>
    (hc.1 (1, c _) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨_, rfl⟩)).2

end place

theorem V_sum : ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (A : ℝ), c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (ι : Type) (S : Finset ι) (F : ι → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (∀ i ∈ S, B.InCC A 5 (F i)) →
    ∀ γ, p.V (∑ i ∈ S, F i) γ = ∑ i ∈ S, p.V (F i) γ := by
  obtain ⟨c₃, H⟩ := PolTop.vector_valued_orbital_linear
  refine ⟨c₃, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p A hA ι S F hF γ
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := V_csmul p (fun _ => 0) 0 γ
    simp only [zero_smul] at this
    rw [Finset.sum_empty, Finset.sum_empty]
    exact this
  | insert i S hi ih =>
    have hS : B.InCC A 5 (∑ j ∈ S, F j) := by
      have := JCx2.sq_inCC_sum S F fun j hj => hF j (Finset.mem_insert_of_mem hj)
      convert this using 2 with g
      rw [Finset.sum_apply]
    obtain ⟨h1, c1, hc1, b1⟩ := bound_of_inCC (hF i (Finset.mem_insert_self _ _))
    obtain ⟨h2, c2, hc2, b2⟩ := bound_of_inCC hS
    have hpos : ∀ g ∈ B.GPos p.T.base, 0 ≤ B.gN g ^ (-A) := fun g hg => Real.rpow_nonneg (BetaSesquilinearity.gN_pos hg.1).le _
    have key := H P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ A hA (F i) (∑ j ∈ S, F j) (c1 + c2) (by linarith)
      (h1.mono fun g hg => hg.1) (h2.mono fun g hg => hg.1)
      (fun g hg => (b1 g hg.1).trans (mul_le_mul_of_nonneg_right (by linarith) (hpos g hg)))
      (fun g hg => (b2 g hg.1).trans (mul_le_mul_of_nonneg_right (by linarith) (hpos g hg))) 1 1
    simp only [one_smul] at key
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih fun j hj => hF j (Finset.mem_insert_of_mem hj)]
    exact key

theorem weighted : ∃ c₃ : ℝ, ∀ {t : ∀ n : ℕ, (Fin n → Bool) → ℝ}, ZuckT t → ZuckDualT t → PI.KFinSmooth → CoefCC →
    CoefEig → PhZero → BetaInfZero → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    [CompleteSpace Wp] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ε : Fin (2 * P.r + P.k + 1) → Bool)
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (j : ℕ) (hj : j ≤ P.r) (a : ℕ) (A h : ℝ) (K : C.LPt → ℝ≥0∞),
    KFinDSCoef ε lam f → PI.ZuckTensor.GapAtLeast ε lam h → t _ ε + 1 + 2 * (((P.r + 1) * a : ℕ) : ℝ) < h →
    KDecay P.k P.r ε A (h - 2 * (((P.r + 1) * a : ℕ) : ℝ)) → B.AB P.k P.r ≤ A →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
    (∀ ν ∈ ball _ ((P.r + 1) * a), ∀ F ∈ Wsp P.k P.r Wp Wq ε (fun s => lam s + (ν s : ℝ)),
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤ K γ * TBB.jN2 p F) →
    ENNReal.ofReal (‖mnr hj γ‖ ^ (2 * a) * TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
      ENNReal.ofReal (((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ (2 * ((P.r + 1) * a))) * K γ * momL p f hj a := by
  obtain ⟨c₃, HV⟩ := V_sum
  refine ⟨c₃, ?_⟩
  intro t hZ hZd hK h4 h5 h6 h7 P Wp Wq _ _ _ _ _ _ _ p f ε lam j hj a A h K hf hg ht hD hA hA3 γ hγ hG hB
  classical
  by_cases h0 : mnr hj γ ^ a = 0
  · rw [two_mul, pow_add, ← norm_pow, h0]
    simp
  obtain ⟨F₀, hF₀, he⟩ := Coef.kfin_wsp hf
  set q : B.Mat P.k P.r → ℂ := fun g => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ ^ a with hq
  have hqL : q ∈ Letters P.k P.r ^ ((P.r + 1) * a) := by
    have h1 : (fun g : B.Mat P.k P.r => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩) ∈
        Letters P.k P.r ^ (P.r + 1) :=
      CompanionTheory.LimBd.Main.letters_pow_mono (show j + 1 ≤ P.r + 1 by omega)
        (CompanionTheory.LimBd.Main.det_mem_pow _ fun a b => CompanionTheory.LimBd.Main.herm_letter _ _)
    rw [pow_mul]
    exact Submodule.pow_mem_pow _ h1 a
  obtain ⟨F, hF, hsum⟩ := mul_mem_sumOn hZ hZd hqL hg ht hF₀
  set S := ball (2 * P.r + P.k + 1) ((P.r + 1) * a) with hS
  have hgν : ∀ ν ∈ S, PI.ZuckTensor.GapAtLeast ε (fun s => lam s + (ν s : ℝ)) (h - 2 * (((P.r + 1) * a : ℕ) : ℝ)) :=
    fun ν hν => gap_of_box (lam := lam) (μ := fun s => lam s + (ν s : ℝ)) (c := (((P.r + 1) * a : ℕ) : ℝ)) (fun s => by simpa using abs_ball hν s) hg
      (by linarith)
  have hcc : ∀ ν ∈ S, B.InCC A 5 (F ν) := fun ν hν => w_inCC hK h4 hD (hgν ν hν) (hF ν) 5
  have hVd : ∀ γ', mnr hj γ' ^ a ≠ 0 → p.V (∑ ν ∈ S, F ν) γ' = mnr hj γ' ^ a • p.V f γ' := fun γ' h' => by
    rw [← hsum]
    exact V_dmin p he hj a γ' h'
  have hE : ∀ ν ∈ S, TBB.jN2 p (F ν) ≤ momL p f hj a := by
    intro ν hν
    have h1 := normSq_le_sum p.hl.2.2 p.T.base hA S F hcc (fun ν₁ h₁ ν₂ h₂ hne =>
      wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _ h₁) (hgν _ h₂) (fun e => hne (funext fun s => by
        have := congrFun e s
        simp only [add_right_inj, Int.cast_inj] at this
        exact this)) (hF _) (hF _)) hν
    rw [← GlobalTheory.T.jN2_eq_normSq_base, ← GlobalTheory.T.jN2_eq_normSq_base] at h1
    refine h1.trans (lintegral_mono fun c => ENNReal.ofReal_le_ofReal ?_)
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · have hne : mnr hj (TBB.bigPt P.r c) ^ a ≠ 0 := pow_ne_zero _ (mnr_bigPt_ne hj c hc.1)
      rw [TBBx2.Tri.Ew_top p _ hc.1, TBBx2.Tri.Ew_top p _ hc.1, hVd _ hne, TBBx2.Tri.hsVec_smul, norm_smul, norm_pow]
      refine le_of_eq ?_
      rw [mul_comm 2 a, pow_mul]
      ring
    · rw [TBBx4.ew_zero_of p _ hc, TBBx4.ew_zero_of p _ hc, mul_zero]
  have hpt := ew_sum_le p f S F (fun _ => 1) (mnr hj γ ^ a) γ fun _ _ => by
    rw [← hVd γ h0, HV P Wp Wq p A hA3 _ S F hcc γ]
    simp
  simp only [norm_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hpt
  rw [norm_pow, ← pow_mul, mul_comm a 2] at hpt
  have hcard : (S.card : ℝ) ≤ ((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ ((P.r + 1) * a) := by
    exact_mod_cast card_ball _ _
  refine (ENNReal.ofReal_le_ofReal hpt).trans ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_sum_of_nonneg fun ν _ => TBBx4.ew_nonneg p _ _]
  have h2 : ∑ ν ∈ S, ENNReal.ofReal (TBB.Ew p (fun _ => 1) (F ν) (P.r + 1) [] γ) ≤
      ENNReal.ofReal (S.card : ℝ) * (K γ * momL p f hj a) := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun ν hν =>
      (hB ν hν _ (hF ν)).trans (mul_le_mul' le_rfl (hE ν hν))).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, ENNReal.ofReal_natCast]
  refine (mul_le_mul' le_rfl h2).trans ?_
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), two_mul ((P.r + 1) * a), pow_add]
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul hcard hcard (Nat.cast_nonneg _) (by positivity))) le_rfl) le_rfl

end CompanionTheory.WaveGrid.WAt

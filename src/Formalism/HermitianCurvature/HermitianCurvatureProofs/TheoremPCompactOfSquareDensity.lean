module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SendsToAlgMulAlg

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepDensity
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivCombCongr
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ResidueSquareIntegrablePositiveRank
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section JF

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem residue_radial_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (a b : Ix S) :
    ((RRi L st 0 w) a b).1 Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 := by
  have hlc : Φ ∈ lcSub P.k P.r z z' π π' := jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ
  have hRRlc := RRi_lc X μ L st l0 hD 0 w hw.1.2.1
  refine ⟨(hRRlc a b).1 Φ hlc, fun c => ?_⟩
  subst hz hz' hπ hπ'
  obtain ⟨ε, hε, hG⟩ := hF.1.2
  have hN : JC.NiceCoef D ε F :=
    ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hF.1.1 0 m).choose_spec.1), hF.1.1, hG⟩
  let F' : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => if b' = b then F else fun _ => 0
  have hN' : ∀ b', JC.NiceCoef D ε (F' b') := by
    intro b'
    by_cases h : b' = b
    · simp only [F', if_pos h]; exact hN
    · simp only [F', if_neg h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let x : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => B.JF D (F' b')
  let Φv : Ix S → RadSp P.k P.r D.z D.z' D.π D.π' := fun b' => if b' = b then Φ else 0
  have hx : ∀ b', x b' ∈ FFl P.k P.r D.z D.z' D.π D.π' 0 (OmPlus P.k P.r D.z D.z') := fun b' =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq D (F' b') ε hε (hN' b')
  have hΦv : ∀ b', ∀ y ∈ DomR P.k P.r D.z D.z',
      (Φv b' : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (x b') y.1 y.2 := by
    intro b' y hy
    by_cases h : b' = b
    · simp only [Φv, x, F', if_pos h]; exact hΦ y hy
    · simp only [Φv, x, F', if_neg h]
      simp only [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero, smul_zero]
      rfl
  have key := Formalism.FourierDecayAlt.P.JCx2.rma_main D.z_mem D.z'_mem X L st (M.sgn P l0) hD.2.2.1 hD.2.2.2.1 w x Φv hx hΦv
  have hsingle : act (RRi L st 0 w) Φv a = ((RRi L st 0 w) a b).1 Φ := by
    unfold act
    rw [Finset.sum_eq_single b (fun b' _ hb' => by simp only [Φv, if_neg hb', map_zero])
      (fun h => absurd (Finset.mem_univ b) h)]
    simp only [Φv, if_pos rfl]
  have hR := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure Formalism.FourierDecayAlt.P.JCx2.bcGood_closed
    (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0))
    (fun Y p q => Formalism.FourierDecayAlt.P.JCx2.bcGood_tL (Bs := D) (ε := ε) (M.sgn P l0) Y p q) w
  let G : Mx P.k P.r → (Wq →L[ℂ] Wp) :=
    Formalism.FourierDecayAlt.D.actOp (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w) F' a
  have hGN : JC.NiceCoef D ε G := by
    show JC.NiceCoef D ε (∑ b', Formalism.FourierDecayAlt.D.ap (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w a b') (F' b'))
    exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' Finset.univ _ fun b' _ => (hR a b').1 (F' b') (hN' b')
  have hpic : ∀ y ∈ DomR P.k P.r D.z D.z',
      ((((RRi L st 0 w) a b).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
    intro y hy
    rw [← hsingle, key a y hy]
    have hGV : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ JF.Om P.k P.r D.z D.z' :=
      ⟨hGV, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hy.1 hy.2.1 hy.2.2⟩
    simp only [resG]
    congr 1
    exact (Formalism.FourierDecayAlt.P.JCx2.bc_core _ hR F' hN' a hh).symm
  have h := level_zero_form_integrable_compact (S := Empty) D μ hD.2.1 (fun _ => G) (fun _ => G)
    (fun _ => ((RRi L st 0 w) a b).1 Φ) (fun _ => ((RRi L st 0 w) a b).1 Φ)
    (fun _ => hGN.2.1) (fun _ => hGN.2.1) (fun _ => hpic) (fun _ => hpic) c
  unfold LevelZeroSquareIntegrable
  letI : Unique (Ix Empty) := { default := Empty.elim, uniq := fun _ => funext fun x => x.elim }
  simpa [wt0] using h

end JF

section Gd

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]


variable (S : Type) [Fintype S] [DecidableEq S] in
def gd0 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) : Submodule ℂ (RadSp P.k P.r z z' π π') where
  carrier := {v | v ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ ∧ ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
    ∀ a b, ((RRi L st 0 w) a b).1 v ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ}
  zero_mem' := ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).zero_mem, fun w _ a b => by
    rw [map_zero]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).zero_mem⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    exact ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).add_mem hu hv, fun w hw a b => by
      rw [map_add (f := _)]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).add_mem (Iu w hw a b) (Iv w hw a b)⟩
  smul_mem' := by
    rintro c u ⟨hu, Iu⟩
    exact ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).smul_mem c hu, fun w hw a b => by
      rw [map_smul]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).smul_mem c (Iu w hw a b)⟩

variable {S : Type} [Fintype S] [DecidableEq S]

theorem good_domain_plane_wave (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) (hl : l.castSucc = 0) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (h1 : multiplicationOperator Wv (fun c _ => fsv s (c l))) (h2 : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (v : RadSp P.k P.r z z' π π') (hv : v ∈ gd0 S P z z' π π' μ hD.2.1 L st l0) :
    Wv v ∈ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
  obtain ⟨hvl, hvR⟩ := hv
  refine ⟨unimodular_multiplier_preserves_L2 μ hD.2.1 h1 (fun c _ => norm_fsv _ _) v hvl, fun w hw a b => ?_⟩
  have hC := Formalism.FourierDecayAlt.P5.waveCommQQAll Wp Wq P z z' π π' X μ L st l0 hD l s Wv Wv' h1 h2
  have hWQ := waveQQ_castSucc X L st hD.2.2.1 l s Wv Wv' h1 h2 hC
  rw [hl] at hWQ
  obtain ⟨hWave, -⟩ := Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' h1 h2
  have hrr := rr_io_wave (QQi L st 0) (mkP Wv Wv') (mkP Wv' Wv) s w hWave hWQ hw.1.1
  have he := congrFun (congrFun hrr a) b
  rw [mul_io_apply, io_apply_mul] at he
  have hM : ((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b) ∈
      sendsTo (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1) v := by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨α, hα⟩ := mem_bot_alg (star_entSub (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w) a c)
    obtain ⟨β, hβ⟩ := mem_bot_alg (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w d b)
    rw [hα, hβ]
    exact sendsTo_alg_mul_alg _ v (hvR w hw c d) α β
  have e : ((RRi L st 0 w) a b).1 (Wv v) = Wv ((((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b)).1 v) :=
    congrArg (fun x : Pr (RadSp P.k P.r z z' π π') => x.1 v) he
  rw [e]
  exact unimodular_multiplier_preserves_L2 μ hD.2.1 h1 (fun c _ => norm_fsv _ _) _ hM

theorem compact_kernel_le_good_domain (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (hr : 0 < P.r) :
    herKc S P z z' π π' L st l0 D 0 ≤ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ =>
      exact fun _ => ⟨radial_transform_square_integrable P z z' π π' μ hD.2.1 D hD.1 hz hz' hπ hπ' F hF Φ hΦ,
        fun w hw a b => residue_radial_square_integrable P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' F hF Φ hΦ w hw a b⟩
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w' s Wv Wv' a' b' Φ _ h1 h2 _ ih =>
      intro h
      have hv := ih h
      have hVw : Vw (mkP Wv Wv') s w' a' b' = mkP Wv Wv' * UUiw s w' a' b' := by
        unfold Vw; exact io_apply_mul _ _ _ _
      obtain ⟨κ, hκ⟩ := mem_bot_alg (UUiw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w' a' b')
      have e : (Vw (mkP Wv Wv') s w' a' b').1 Φ = κ • Wv Φ := by
        rw [hVw, hκ, pr_fst_mul, pr_fst_algebraMap, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
        rfl
      rw [e]
      exact (gd0 S P z z' π π' μ hD.2.1 L st l0).smul_mem κ
        (good_domain_plane_wave P z z' π π' X μ L st l0 hD l h s Wv Wv' h1 h2 Φ hv)
    | waveZ w s Wv Wv' a b Φ _ _ _ _ _ =>
      intro h
      exfalso
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
  exact key 0 Φ hΦ rfl

def ResidueSquareIntegrablePositiveRank : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D 0) x → ∀ (a : Ix S) (c : Fin P.r → ℂ), c ∈ OmX P.r →
        LevelSquareIntegrable μ 0 (act (RRi L st 0 w) x a) c

theorem rRL2Lev0Pos : ResidueSquareIntegrablePositiveRank := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' hr w hw x hx a c _
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hle := compact_kernel_le_good_domain (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' hr
  have hm : act (RRi L st 0 w) x a ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 :=
    (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1).sum_mem fun b _ => (hle (hx b)).2 w hw a b
  exact hm.2 c

def HermitianLevelZeroPositiveRank : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D 0

theorem hermitian_level_zero_positive_rank : HermitianLevelZeroPositiveRank := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  refine ⟨fun u hu => ?_, fun w hw x hx a =>
    rRL2Lev0Pos Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr w hw x hx a c hc⟩
  exact (compact_kernel_le_L2 (S := S) P z z' π π' μ hD.2.1 L st l0 D hD.1 hz hz' hπ hπ' hu).2 c

theorem hermitian_all_of_transport (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) : HermitianSquareIntegrableAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
  obtain ⟨Di, Xi, μi, Li, sti, T, hDi, ⟨-, ⟨κ, hκ, hpair⟩, -, hw⟩, hHer⟩ :=
    hT Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i c (fun l _ => hc l)
  have hlow := hermitian_level_zero_positive_rank Wp Wq S (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 Di hDi h1 h2 rfl rfl rfl rfl
    (by show 0 < P.r - (i : ℕ); omega) (fun _ => 1) (fun _ => one_ne_zero)
  refine ⟨fun u hu => ?_, fun w hwo x hx a => ?_⟩
  · exact level_square_integrable_of_transport μ i c μi T κ hκ hpair u _ (hlow.1 (T u) (hHer S u hu))
  · obtain ⟨-, hRR, hWO⟩ := hw S w
    have hA := hRR 0 (by omega)
    have e1 : (⟨0 + i.val, by omega⟩ : Fin (P.r + 1)) = i := Fin.ext (by simp)
    have e0 : (⟨0, by omega⟩ : Fin (P.r - i + 1)) = 0 := rfl
    rw [e1, e0] at hA
    refine level_square_integrable_of_transport μ i c μi T κ hκ hpair _ (fun _ => 1) ?_
    rw [act_tr T hA x a]
    exact hlow.2 w (hWO hwo) _ (fun b => hHer S (x b) (hx b)) a

theorem formIntOuterCpt_of_levT (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) : FormIntOuterCpt :=
  outer_form_compact_of_square (hermitian_all_of_transport hT)

end Gd

end Formalism.FourierDecayAlt.P5.HerD
end
end

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section ShiftJ

variable {r : ℕ}

def shIdxJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) :
    {m : Fin (r - i) // jl.val ≤ m.val} ≃ {p : Fin r // j.val ≤ p.val} where
  toFun m := ⟨⟨m.1.val + i.val, by have := m.1.isLt; have := i.isLt; omega⟩, by
    have := m.2; show j.val ≤ m.1.val + i.val; omega⟩
  invFun p := ⟨⟨p.1.val - i.val, by have := p.1.isLt; have := p.2; omega⟩, by
    have := p.2; show jl.val ≤ p.1.val - i.val; omega⟩
  left_inv m := by
    apply Subtype.ext; apply Fin.ext
    show m.1.val + i.val - i.val = m.1.val
    omega
  right_inv p := by
    apply Subtype.ext; apply Fin.ext
    show p.1.val - i.val + i.val = p.1.val
    have := p.2; omega

def shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : Cf (r - i) (jl) ≃ᵐ Cf r j :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_mp (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : MeasurePreserving (shEqJ i j jl hjl) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_apply (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c' : Cf (r - i) (jl))
    (p : {p : Fin r // j.val ≤ p.val}) : shEqJ i j jl hjl c' p = c' ((shIdxJ i j jl hjl).symm p) := by
  unfold shEqJ
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

def shiftV (i : Fin (r + 1)) (c' : Fin r → ℂ) : Fin (r - i) → ℂ :=
  fun m => c' ⟨m.val + i.val, by have := m.isLt; have := i.isLt; omega⟩

theorem glue_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) (c'' : Cf (r - i) (jl)) :
    glue j c' (shEqJ i j jl hjl c'') =
      glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue (jl) (shiftV i c') c'')) := by
  funext p
  by_cases h1 : j.val ≤ p.val
  · have h2 : i.val ≤ p.val := by omega
    have h3 : (jl).val ≤ p.val - i.val := by omega
    simp only [glue, dif_pos h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_pos h3, shEqJ_apply]
    rfl
  · by_cases h2 : i.val ≤ p.val
    · have h3 : ¬ (jl).val ≤ p.val - i.val := by omega
      simp only [glue, dif_neg h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_neg h3, shiftV]
      congr 1
      apply Fin.ext
      show p.val = p.val - i.val + i.val
      omega
    · simp only [glue, dif_neg h1, dif_neg h2]
      exact hc p (by omega)

theorem wtI_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') = wtI (jl) c'' := by
  unfold wtI
  congr 1
  simp_rw [shEqJ_apply]
  exact Fintype.prod_equiv (shIdxJ i j jl hjl).symm _ _ fun l => rfl

end ShiftJ

section Tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem integrand_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') * ∑ a, pairAt μ (u a) (v a) (glue j c' (shEqJ i j jl hjl c'')) =
      (κ : ℂ)⁻¹ * (wtI (jl) c'' *
        ∑ a, pairAt μi (T (u a)) (T (v a)) (glue (jl) (shiftV i c') c'')) := by
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [wtI_shEqJ, glue_shEqJ i j jl hjl c c' hc]
  simp_rw [hT]
  rw [← Finset.mul_sum]
  field_simp

theorem form_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') :
    form μ j u v c' = (κ : ℂ)⁻¹ * form μi (jl) (fun a => T (u a)) (fun a => T (v a)) (shiftV i c') := by
  unfold form
  rw [← (shEqJ_mp i j jl hjl).integral_comp', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c'' => ?_)
  exact integrand_tr μ i j jl hjl c c' hc μi T κ hκ hT u v c''

end Tr

theorem arel_star {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {S : Type}
    [Fintype S] [DecidableEq S] {T : V →ₗ[ℂ] V'} {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')}
    (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M') : Formalism.FourierDecayAlt.P.PBH.ARel T (star M) (star M') := fun a b => by
  rw [Matrix.star_apply, Matrix.star_apply]
  exact Formalism.FourierDecayAlt.P.PBH.rel_star (h b a)

end Formalism.FourierDecayAlt.P5.HerD
end
end

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

def DerivCombInt (f : ℂ → ℂ) (I : ℂ) : Prop :=
  ∃ (n K : ℕ) (C : ℝ) (Dd : Fin K → ℂ → ℂ) (j : Fin K → ℕ) (v : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
    (∀ i, j i ≤ n) ∧ (∀ i, DecayData n C (Dd i)) ∧
    (∀ t, t ≠ 0 → f t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dd i) t (v i)) ∧
    ∑ i, a i * (if j i = 0 then ∫ t, Dd i t else 0) = I

theorem iteratedFDeriv_apply_of_eq_zero (m : ℕ) (u : Fin m → ℂ) (G : ℂ → ℂ) (hm : m = 0) (t : ℂ) :
    iteratedFDeriv ℝ m G t u = G t := by
  subst hm
  simp

theorem ae_ne_zero_C : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  have hset : {a : ℂ | ¬a ≠ 0} = {0} := by
    ext a
    simp
  rw [hset]
  exact measure_singleton 0

theorem ext_of_derivCombInt {f : ℂ → ℂ} {I : ℂ} (hf : DerivCombInt f I) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = f t) ∧
      (∃ C' : ℝ, ∀ t, ‖φ t‖ ≤ C' * (1 + ‖t‖) ^ (-4 : ℤ)) ∧ ∫ t, φ t = I := by
  obtain ⟨n, K, C, Dd, j, v, a, hjn, hdat, hf, hI⟩ := hf
  have hc := fun i => Fou.smooth_extension_of_fourier_decay (Dd i) n C (hdat i).1 (hdat i).2.1 (hdat i).2.2.1 (hdat i).2.2.2.1 (hdat i).2.2.2.2
  choose D' hD'c hD'e hD'i hdec hder using hc
  choose Cd hCd using hdec
  refine ⟨fun t => ∑ i, a i * iteratedFDeriv ℝ (j i) (D' i) t (v i), ?_, fun t ht => ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact (continuous_eval_const (v i)).comp ((hD'c i).continuous_iteratedFDeriv (by exact_mod_cast hjn i))
  · rw [hf t ht]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    have hev : D' i =ᶠ[𝓝[Set.univ] t] Dd i := by
      rw [nhdsWithin_univ]
      filter_upwards [isOpen_compl_singleton.mem_nhds ht] with u hu
      exact hD'e i u hu
    have := hev.iteratedFDerivWithin_eq (hD'e i t ht) (j i) (𝕜 := ℝ)
    rwa [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at this
  · refine ⟨∑ i, ‖a i‖ * (Cd i * ∏ k, ‖v i k‖), fun t => ?_⟩
    have hpow : (1 + ‖t‖) ^ (-(4 : ℝ)) = (1 + ‖t‖) ^ (-4 : ℤ) := by
      rw [← Real.rpow_intCast]; norm_num
    have hp0 : 0 ≤ (1 + ‖t‖) ^ (-4 : ℤ) := by positivity
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul]
    have h1 := (iteratedFDeriv ℝ (j i) (D' i) t).le_opNorm (v i)
    have h2 := hCd i (j i) (hjn i) t
    rw [hpow] at h2
    have hv0 : 0 ≤ ∏ k, ‖v i k‖ := Finset.prod_nonneg fun k _ => norm_nonneg _
    calc ‖a i‖ * ‖iteratedFDeriv ℝ (j i) (D' i) t (v i)‖
        ≤ ‖a i‖ * ((Cd i * (1 + ‖t‖) ^ (-4 : ℤ)) * ∏ k, ‖v i k‖) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 hv0)) (norm_nonneg _)
      _ = ‖a i‖ * (Cd i * ∏ k, ‖v i k‖) * (1 + ‖t‖) ^ (-4 : ℤ) := by ring
  · have hterm : ∀ i, Integrable (fun t => a i * iteratedFDeriv ℝ (j i) (D' i) t (v i)) ∧
        ∫ t, a i * iteratedFDeriv ℝ (j i) (D' i) t (v i) = a i * (if j i = 0 then ∫ t, Dd i t else 0) := by
      intro i
      by_cases h0 : j i = 0
      · have e : (fun t => a i * iteratedFDeriv ℝ (j i) (D' i) t (v i)) = fun t => a i * D' i t := by
          funext t; rw [iteratedFDeriv_apply_of_eq_zero (j i) (v i) (D' i) h0 t]
        have hInt : Integrable (D' i) :=
          (hdat i).1.congr (ae_ne_zero_C.mono fun t ht => (hD'e i t ht).symm)
        rw [e, if_pos h0]
        exact ⟨hInt.const_mul _, by rw [integral_const_mul, hD'i i]⟩
      · have hj1 : 1 ≤ j i := Nat.one_le_iff_ne_zero.mpr h0
        obtain ⟨hIi, hzero⟩ := hder i (j i) hj1 (hjn i)
        have hIv : Integrable (fun t => iteratedFDeriv ℝ (j i) (D' i) t (v i)) :=
          (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j i) => ℂ) ℂ (v i)).integrable_comp hIi
        have hz : ∫ t, iteratedFDeriv ℝ (j i) (D' i) t (v i) = 0 := by
          have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j i) => ℂ) ℂ (v i)).integral_comp_comm hIi
          simp only [ContinuousMultilinearMap.apply_apply] at this
          rw [this, hzero]
          simp
        rw [if_neg h0]
        exact ⟨hIv.const_mul _, by rw [integral_const_mul, hz, mul_zero]⟩
    rw [integral_finsetSum _ fun i _ => (hterm i).1]
    rw [← hI]
    exact Finset.sum_congr rfl fun i _ => (hterm i).2

theorem derivCombInt_congr {f g : ℂ → ℂ} {I : ℂ} (c : ℂ) (hf : DerivCombInt f I) (h : ∀ t, t ≠ 0 → g t = c * f t) :
    DerivCombInt g (c * I) := by
  obtain ⟨n, K, C, Dd, j, v, a, hj, hD, hfa, hI⟩ := hf
  refine ⟨n, K, C, Dd, j, v, fun i => c * a i, hj, hD, ?_, ?_⟩
  · intro t ht
    rw [h t ht, hfa t ht, Finset.mul_sum]
    simp only [mul_assoc]
  · rw [← hI, Finset.mul_sum]
    simp only [mul_assoc]

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem stepDens_of_exp (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (h : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
      DerivCombInt (ph L st μ l w x y c) (RRform L st μ l.castSucc w x y c)) :
    StepDens (S := S) P z z' π π' μ L st K l0 := by
  unfold StepDens
  intro w hw l x y hx hy c hc
  exact ext_of_derivCombInt (h w hw l x y hx hy c hc)

end Gen

def StepExp0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r, DerivCombInt (ph L st μ l w x y c) (RRform L st μ l.castSucc w x y c)

theorem stepDensCptAll_of_levT (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) (h0 : StepExp0) : StepDensCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine stepDens_of_exp P z z' π π' μ L st _ l0 fun w hw l x y hx hy c hc => ?_
  obtain ⟨Di, Xi, μi, Li, sti, T, hDi, ⟨-, ⟨κ, hκ, hpair⟩, -, hwT⟩, hHer⟩ :=
    hT Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l.castSucc c (fun p _ => hc p)
  obtain ⟨hbT, hRR, hWO⟩ := hwT S w
  have hpos : 0 < P.r - (l.castSucc : Fin (P.r + 1)).val := by simp only [Fin.val_castSucc]; omega
  set l' : Fin (P.r - (l.castSucc : Fin (P.r + 1)).val) := ⟨0, hpos⟩ with hl'
  have hl'v : l'.val = 0 := by rw [hl']
  have e0 : ∀ h : l'.val + (l.castSucc : Fin (P.r + 1)).val < P.r,
      (⟨l'.val + (l.castSucc : Fin (P.r + 1)).val, h⟩ : Fin P.r) = l := fun h => by
    apply Fin.ext
    show l'.val + (l.castSucc : Fin (P.r + 1)).val = l.val
    rw [hl'v, Fin.val_castSucc, zero_add]
  have e1 : ∀ h : 1 + (l.castSucc : Fin (P.r + 1)).val < P.r + 1,
      (⟨1 + (l.castSucc : Fin (P.r + 1)).val, h⟩ : Fin (P.r + 1)) = l.succ := fun h => by
    apply Fin.ext
    show 1 + (l.castSucc : Fin (P.r + 1)).val = l.succ.val
    rw [Fin.val_castSucc, Fin.val_succ, add_comm]
  have e2 : ∀ h : 1 < P.r - (l.castSucc : Fin (P.r + 1)).val + 1,
      (⟨1, h⟩ : Fin (P.r - (l.castSucc : Fin (P.r + 1)).val + 1)) = l'.succ := fun h => by
    apply Fin.ext
    show 1 = l'.succ.val
    rw [Fin.val_succ, hl'v]
  have hb : Formalism.FourierDecayAlt.P.PBH.ARel T (bTl L l w) (bTl Li l' w) := by
    have := hbT l'
    simp only [e0] at this
    exact this
  have hR1 : Formalism.FourierDecayAlt.P.PBH.ARel T (RRi L st l.succ w) (RRi Li sti l'.succ w) := by
    have := hRR 1 (by simp only [Fin.val_castSucc]; omega)
    simp only [e1, e2] at this
    exact this
  have hM := Formalism.FourierDecayAlt.P.PBH.arel_mul hR1 hb
  have hSM := Formalism.FourierDecayAlt.P.PBH.arel_mul (arel_star hb) hM
  have hl0 : l'.castSucc = 0 := Fin.ext rfl
  have hx' : InK (herKc S (JC.parLev P (l.castSucc : Fin (P.r + 1))) Di.z Di.z' Di.π Di.π' Li sti l0 Di l'.castSucc)
      (fun a => T (x a)) := by
    rw [hl0]; exact fun a => hHer S (x a) (hx a)
  have hy' : InK (herKc S (JC.parLev P (l.castSucc : Fin (P.r + 1))) Di.z Di.z' Di.π Di.π' Li sti l0 Di l'.castSucc)
      (fun a => T (y a)) := by
    rw [hl0]; exact fun a => hHer S (y a) (hy a)
  have hc0 : shiftV l.castSucc c ∈ OmX (P.r - (l.castSucc : Fin (P.r + 1)).val) := fun m => hc _

  have e3 : ∀ h : 0 + (l.castSucc : Fin (P.r + 1)).val < P.r + 1,
      (⟨0 + (l.castSucc : Fin (P.r + 1)).val, h⟩ : Fin (P.r + 1)) = l.castSucc := fun h => by
    apply Fin.ext
    show 0 + (l.castSucc : Fin (P.r + 1)).val = (l.castSucc : Fin (P.r + 1)).val
    rw [zero_add]
  have e4 : ∀ h : 0 < P.r - (l.castSucc : Fin (P.r + 1)).val + 1,
      (⟨0, h⟩ : Fin (P.r - (l.castSucc : Fin (P.r + 1)).val + 1)) = l'.castSucc := fun h => by
    apply Fin.ext
    show 0 = l'.castSucc.val
    rw [Fin.val_castSucc, hl'v]
  have hR0 : Formalism.FourierDecayAlt.P.PBH.ARel T (RRi L st l.castSucc w) (RRi Li sti l'.castSucc w) := by
    have := hRR 0 (by simp only [Fin.val_castSucc]; omega)
    simp only [e3, e4] at this
    exact this
  have hD0 := h0 Wp Wq S (JC.parLev P (l.castSucc : Fin (P.r + 1))) Di.z Di.z' Di.π Di.π' Xi μi Li sti
    l0 Di hDi h1 h2 rfl rfl rfl rfl w (hWO hw) l' rfl _ _ hx' hy' _ hc0
  have hjl0 : l'.castSucc.val + (l.castSucc : Fin (P.r + 1)).val = (l.castSucc : Fin (P.r + 1)).val := by
    simp only [Fin.val_castSucc, hl'v]; omega
  have hRRf : RRform L st μ l.castSucc w x y c =
      (κ : ℂ)⁻¹ * RRform Li sti μi l'.castSucc w (fun a => T (x a)) (fun a => T (y a)) (shiftV l.castSucc c) := by
    unfold RRform
    rw [form_tr μ l.castSucc l.castSucc l'.castSucc hjl0 c c (fun _ _ => rfl) μi T κ hκ hpair]
    have eX0 : (fun a => T (act (RRi L st l.castSucc w) x a)) = act (RRi Li sti l'.castSucc w) (fun b => T (x b)) := by
      funext a; exact act_tr T hR0 x a
    rw [eX0]
  rw [hRRf]
  refine derivCombInt_congr ((κ : ℂ)⁻¹) hD0 fun t _ => ?_
  have hjl1 : l'.succ.val + (l.castSucc : Fin (P.r + 1)).val = l.succ.val := by
    simp only [Fin.val_succ, Fin.val_castSucc, hl'v]; omega
  have hupd : ∀ p : Fin P.r, p.val < (l.castSucc : Fin (P.r + 1)).val → Function.update c l t p = c p := by
    intro p hp
    rw [Function.update_of_ne]
    intro h; rw [h] at hp; simp at hp
  have eX : (fun a => T (act (RRi L st l.succ w) (act (bTl L l w) x) a)) =
      act (RRi Li sti l'.succ w) (act (bTl Li l' w) (fun b => T (x b))) := by
    funext a
    rw [act_tr T hR1 (act (bTl L l w) x) a]
    congr 1
    funext b
    exact act_tr T hb x b
  have eY : (fun a => T (act (bTl L l w) y a)) = act (bTl Li l' w) (fun b => T (y b)) := by
    funext a
    exact act_tr T hb y a
  unfold ph RRform
  rw [form_tr μ l.castSucc l.succ l'.succ hjl1 c (Function.update c l t) hupd μi T κ hκ hpair, eX, eY, mul_left_comm]
  congr 3
  change shiftV l.castSucc (Function.update c l t) =
    Function.update (shiftV l.castSucc c) l' t
  funext m
  by_cases hm : m = l'
  · subst m
    simp only [shiftV, e0, Function.update_self]
  · rw [Function.update_of_ne hm]
    unfold shiftV
    rw [Function.update_of_ne]
    intro he
    apply hm
    apply Fin.ext
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc] at hv
    rw [hl'v]
    omega

theorem theorem_P_compact_of_step_density (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) (h0 : StepExp0) : ThmPActualCpt :=
  thmPActualCpt_of_outer (stepDensCptAll_of_levT hT h0) (formIntOuterCpt_of_levT hT)

end Formalism.FourierDecayAlt.P5.HerD
end
end

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Dens

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S]
  [DecidableEq S]

def Dens (μ : Measure (Mt k r)) (l : Fin r) (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) : ℂ :=
  ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ u v (Function.update c l t)

theorem dens_int (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r)
    (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ HerC.lcSub k r z z' π π') (hv : ∀ a, v a ∈ HerC.lcSub k r z z' π π')
    (c : Fin r → ℂ) (Iu : ∀ a, LevelSquareIntegrable μ l.castSucc (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ l.castSucc (v a) c) :
    Integrable (Dens μ l u v c) ∧ ∫ t, Dens μ l u v c t = form μ l.castSucc u v c := by
  have hint := formIntOuter_of_l2I μ hμ l.castSucc u v hu hv c Iu Iv
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (u a) (v a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) :=
    (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
  have h2 := hF.integral_prod_left
  refine ⟨h2.congr (Filter.Eventually.of_forall fun t => ?_), (form_split μ l u v c hint).symm⟩
  show ∫ c'', f ((coordinateSplit (r := r) l).symm (t, c'')) = Dens μ l u v c t
  simp only [hval, Dens, form]
  rw [integral_const_mul]

end Dens

def DecayRest (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def LevelDensitySquareIntegrable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      ∃ (n K : ℕ) (C : ℝ) (u v : Fin K → Ix S → RadSp P.k P.r z z' π π') (j : Fin K → ℕ)
        (vv : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
        (∀ i b, u i b ∈ HerC.lcSub P.k P.r z z' π π' ∧ LevelSquareIntegrable μ l.castSucc (u i b) c ∧
          v i b ∈ HerC.lcSub P.k P.r z z' π π' ∧ LevelSquareIntegrable μ l.castSucc (v i b) c) ∧
        (∀ i, j i ≤ n) ∧ (∀ i, DecayRest n C (Dens μ l (u i) (v i) c)) ∧
        (∀ t, t ≠ 0 → ph L st μ l w x y c t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dens μ l (u i) (v i) c) t (vv i)) ∧
        ∑ i, a i * (if j i = 0 then form μ l.castSucc (u i) (v i) c else 0) = RRform L st μ l.castSucc w x y c

theorem step_density_of_square (h : LevelDensitySquareIntegrable) : StepExp0 := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  obtain ⟨n, K, C, u, v, j, vv, a, hL2, hjn, hrest, hexp, hI⟩ :=
    h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have hdi := fun i => dens_int μ hD.2.1 l (u i) (v i) (fun b => (hL2 i b).1) (fun b => (hL2 i b).2.2.1) c
    (fun b => (hL2 i b).2.1) (fun b => (hL2 i b).2.2.2)
  refine ⟨n, K, C, fun i => Dens μ l (u i) (v i) c, j, vv, a, hjn, fun i => ⟨(hdi i).1, hrest i⟩, hexp, ?_⟩
  rw [← hI]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [(hdi i).2]
  · rfl

end Formalism.FourierDecayAlt.P5.HerD

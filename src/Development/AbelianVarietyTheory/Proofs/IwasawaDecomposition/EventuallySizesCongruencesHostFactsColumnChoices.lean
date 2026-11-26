module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinct
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinct
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.TwInputs.PlacesAt

theorem evLgG_placesOk : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (GlobalTheory.TwInputs.SmallField.lg_lam K).imp fun B f _ hO _ _ T w Z => ?_
  have hq := GlobalTheory.TwInputs.SmallField.auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact B.toPre.host).1
  obtain ⟨w0, hw0⟩ := GlobalTheory.TwInputs.SmallField.exists_over B.toPre.host.E hqp
  have hmod : ∀ p ∈ [B.toPre.host.g 0, B.toPre.host.g 1, B.toPre.host.pde, B.toPre.host.pde', GlobalTheory.EX.DC.q0H B.toPre.host],
      p ≡ 1 [MOD B.toPre.host.QS * B.toPre.host.q * B.toPre.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (GlobalTheory.TwInputs.SmallField.one_lt_cond B.toPre)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [B.toPre.g_cond 0, B.toPre.g_cond 1, B.toPre.pde_cond.1, B.toPre.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  exact ⟨w0, (GlobalTheory.LamTie.placesOk_of_modEq_one B.toPre.R B.toPre.host _ w0 hqp hmod hq
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0).1⟩

end GlobalTheory.TwInputs.PlacesAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinctStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_auxiliary_places_split_distinct : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  first | exact @GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk | exact GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk | (intros; apply GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoices
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HypCMRec

theorem hypCM_all (D : D7) : SphericalInertData.HypCM D := by
  refine ⟨?_, GlobalTheory.DesignBC.two_le_finrank D, fun w hw h2 => hw (GlobalTheory.DesignBC.isSplitPl_of_two_mem D w h2)⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem hypCM_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) :=
  evG_all fun K => lg_all K fun _ _ _ _ _ _ _ _ => hypCM_all _

end GlobalTheory.Mem.HypCMRec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) := by
  first | exact @GlobalTheory.Mem.HypCMRec.hypCM_at_record | exact GlobalTheory.Mem.HypCMRec.hypCM_at_record | (intros; apply GlobalTheory.Mem.HypCMRec.hypCM_at_record <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.RankSize

theorem rank_ge_hundred : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r := by
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨100, fun K _ _ _ _ hx _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp_all, by simp_all,
    fun B f _ hO _ _ _ _ T w Z => ?_⟩
  show 100 ≤ B.R.r
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hRK : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hR : GlobalTheory.EX.RankVal K.s B.toPre.R := hRK ▸ K.ok.rank
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1 := K.s.one_lt_alt
  have he := K.s.eps_pos
  have hk1 : K.s.x ≤ (B.toPre.R.k : ℝ) := by
    calc K.s.x = K.s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K.s.x ^ (9 / 2 + 10 * K.s.eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ ≤ _ := hk
  have h100 : (100 : ℝ) ≤ (B.toPre.R.k : ℝ) := hx.trans hk1
  have hk100 : 100 ≤ B.toPre.R.k := by exact_mod_cast h100
  have h2m := B.toPre.R.two_le_m
  have hmk := B.toPre.R.m_add_three_le_k
  have hkr : B.toPre.R.k ≤ B.toPre.R.r := by unfold Ranks.r; omega
  exact hk100.trans hkr

end GlobalTheory.Mem.RankSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r := by
  first | exact @GlobalTheory.Mem.RankSize.rank_ge_hundred | exact GlobalTheory.Mem.RankSize.rank_ge_hundred | (intros; apply GlobalTheory.Mem.RankSize.rank_ge_hundred <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.Top.Bl

theorem two_mul_r_le_g_level : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ k,
    2 * (w.D Z).R.r ≤ (w.D Z).host.g k := by
  refine evG_all fun K => lg_all K fun B f T hO _ T' w Z k => ?_
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hR' : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hg : B.toPre.host.g = K.P.H.g := by rw [hB]; rfl
  show 2 * B.R.r ≤ B.host.g k
  rw [show B.host.g k = K.P.H.g k from congrFun hg k, show B.R.r = K.P.R.r from by rw [hR']]
  have hgk : ((K.P.R.k : ℝ) * K.s.b) ^ 8 ≤ (K.P.H.g k : ℝ) := (K.ok.val.2.2.2.2.1 k).1
  have hb : 1 ≤ K.s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [K.s.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
  have hkb : (K.P.R.k : ℝ) ^ 8 ≤ (K.P.H.g k : ℝ) :=
    le_trans (pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8) hgk
  have hk8 : (K.P.R.k) ^ 8 ≤ K.P.H.g k := by exact_mod_cast hkb
  have h2k : 2 ≤ K.P.R.k := by
    have := K.P.R.f_le_k
    have : 0 < K.P.R.ord := K.P.R.ord_pos
    omega
  have hr : 2 * K.P.R.r ≤ 4 * K.P.R.k := by
    have := K.P.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h4 : 4 * K.P.R.k ≤ K.P.R.k ^ 8 := by
    calc 4 * K.P.R.k ≤ K.P.R.k ^ 7 * K.P.R.k := by
          apply Nat.mul_le_mul_right
          calc 4 ≤ 2 ^ 7 := by norm_num
            _ ≤ K.P.R.k ^ 7 := Nat.pow_le_pow_left h2k 7
      _ = K.P.R.k ^ 8 := by ring
  omega

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_two_mul_rank_le_levelPrime : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k := by
  first | exact @GlobalTheory.Mem.Top.Bl.two_mul_r_le_g_level | exact GlobalTheory.Mem.Top.Bl.two_mul_r_le_g_level | (intros; apply GlobalTheory.Mem.Top.Bl.two_mul_r_le_g_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrde
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrde
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem isAlgebraic_exp_two_pi_div (n : ℕ) (hn : 0 < n) :
    IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / n)) :=
  (((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top (A := ℚ)).isAlgebraic

theorem rootsLL_evLgG :
    EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  have hLg : ∀ K : Ctx, large₂ K fun B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
    intro K
    refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
      fun B _ _ _ _ => {Complex.exp (2 * Real.pi * Complex.I / B.restRowsFiniteGroupCard)}, by simp, ?_, ?_⟩
    · intro B _ _ _ _ z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      exact isAlgebraic_exp_two_pi_div _ B.restRowsFiniteGroupCard_pos
    · intro B f T₀ _ hH _ _ _ T w Z
      obtain ⟨x, hx⟩ : ∃ x : B.LL, B.embLL x = Complex.exp (2 * Real.pi * Complex.I / B.toPre.restRowsFiniteGroupCard) :=
        hH.2 _ (Finset.mem_singleton_self _)
      refine ⟨x, ?_⟩
      show IsPrimitiveRoot x B.toPre.restRowsFiniteGroupCard
      rw [← IsPrimitiveRoot.map_iff_of_injective (f := B.embLL) B.embLL.injective, hx]
      exact Complex.isPrimitiveRoot_exp _ B.toPre.restRowsFiniteGroupCard_pos.ne'
  exact EvG.imp evG_good fun K _ _ _ _ _ => hLg K

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrdeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  first | exact @GlobalTheory.HeightCounting.Up.rootsLL_evLgG | exact GlobalTheory.HeightCounting.Up.rootsLL_evLgG | (intros; apply GlobalTheory.HeightCounting.Up.rootsLL_evLgG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.DefSpaces

theorem v_isDefinite : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f _ hO _ T w Z j hj1 hj2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  have hm : (w.st Z).toD7.R.m = (w.D Z).R.m := rfl
  have hp := GlobalTheory.RepsObj.isPosDef_of_vStd (D := (w.st Z).toD7) ⟨j - 1, by omega⟩ (hV ⟨j - 1, by omega⟩)
  change ((w.st Z).toD7.sp.V j).IsDefinite
  intro τ
  left
  have e : j - 1 + 1 = j := by omega
  have := hp τ
  simp only [Formalism.IndefR.Links.Vc, e] at this
  exact this

end GlobalTheory.Mem.DefSpaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_spacesV_definite_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  first | exact @GlobalTheory.Mem.DefSpaces.v_isDefinite | exact GlobalTheory.Mem.DefSpaces.v_isDefinite | (intros; apply GlobalTheory.Mem.DefSpaces.v_isDefinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadrat
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadrat
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HostEFK

theorem hypEFK_ev : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) :=
  evG_all fun K => lg_all K fun B f T _ _ T' w Z => GlobalTheory.DesignBC.hypEFK (w.D Z)

end GlobalTheory.Mem.HostEFK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadratStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) := by
  first | exact @GlobalTheory.Mem.HostEFK.hypEFK_ev | exact GlobalTheory.Mem.HostEFK.hypEFK_ev | (intros; apply GlobalTheory.Mem.HostEFK.hypEFK_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem sizes_host_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine EvG.imp (GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices.inter (GlobalTheory.T.eventually_two_mul_rank_le_levelPrime.inter (GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder.inter (GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic.inter (GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices.inter (GlobalTheory.T.eventually_spacesV_definite_columnChoices.inter GlobalTheory.T.eventually_auxiliary_places_split_distinct)))))) fun K _ _ _ _ H => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))).imp fun B f T _ G hk T' w Z =>
    ⟨G.1 hk T' w Z, G.2.1 hk T' w Z, G.2.2.1 hk T' w Z, G.2.2.2.1 hk T' w Z, G.2.2.2.2.1 hk T' w Z, G.2.2.2.2.2.1 hk T' w Z,
      G.2.2.2.2.2.2 hk T' w Z⟩

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  first | exact @GlobalTheory.HeightCounting.Up.sizes_host_at_record | exact GlobalTheory.HeightCounting.Up.sizes_host_at_record | (intros; apply GlobalTheory.HeightCounting.Up.sizes_host_at_record <;> assumption)
end

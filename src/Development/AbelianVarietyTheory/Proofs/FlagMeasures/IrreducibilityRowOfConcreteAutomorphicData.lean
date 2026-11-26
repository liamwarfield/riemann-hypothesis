module

public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountConstantsOfSiegelWeil
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsPCount

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountClausesClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountParameterConditionsOfSizeHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountParameterConditionsOfSizeHypotheses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem countClauses_of_sizeHyp : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ),
    0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl →
    Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  intro D L C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hAr hH
  have d1 := data1 L
  have d11 : SplitsE D (D.host.g 0) := hAr.2.1
  have d13 : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := hAr.2.2.2
  obtain ⟨-, -, -, -, H5, -, H7, H8, -, -, H11, H12, H13, ContinuousCyclotomicCharacter₂, ContinuityOfCyclotomicCharacter, CyclotomicCharacterContinuous, -, -, H19, LocalHeightDeterminant, H21, -, -, -, -⟩ := hH
  have hk5 := Formalism.MainNotions.S.five_le_k (D := D)
  have hf1 := Formalism.MainNotions.S.one_le_f (D := D)
  have hkr := Formalism.MainNotions.S.k_le_r (D := D)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL1 := one_lt_scL L
  have hlogb := log_scb L
  have hb2 := two_le_scb L
  have hb0 : 0 < L.sc.b := lt_of_lt_of_le two_pos hb2
  refine ⟨?_, ?_⟩
  swap
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 1 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k ContinuousCyclotomicCharacter₂
    exact_mod_cast h5
  have hlr : 1 ≤ Real.log (D.R.r : ℝ) := one_le_log_of_five_le (le_trans hk5 hkr)
  obtain ⟨hmsq, hLk, hClL⟩ := k_ge_of_chain_bound hm2 hL1 hCl2 H7
  have hrd2 : 2 ≤ D.host.rdE := by
    have h : D.host.v = D.host.rdE / 2 := rfl
    rw [h] at H19; linarith only [H19]
  have hlrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg (by linarith only [hrd2])
  have hDel0 : 0 ≤ (D.s.Del : ℝ) := le_trans (Real.rpow_nonneg (by positivity) _) LocalHeightDeterminant
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hb1nn : ∀ τ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ bOne D τ j := fun τ j h1 h2 =>
    le_trans (by positivity) (H8 τ j h1 h2)
  have hbsq : ∀ τ j, 1 ≤ j → j ≤ D.R.m → bOne D τ j ≤ L.sc.b ^ 2 := fun τ j h1 h2 => by
    have := (CyclotomicCharacterContinuous τ j h1 h2).2
    rwa [Real.rpow_two] at this
  refine ⟨d13, ?_, ?_, ?_, ?_, ?_, ?_, d11, ?_, ?_, hb2, ?_⟩
  · have h2 : n0 ≤ D.R.k := by exact_mod_cast hn0
    have h3 := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  · have h1 : D.R.m ^ 2 ≤ D.R.k := by exact_mod_cast hmsq
    have h2 : D.R.rS + 1 ≤ D.R.m := by
      have := D.R.two_le_m
      unfold Ranks.rS; omega
    have h3 : (D.R.rS + 1) ^ 2 ≤ D.R.m ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : D.R.k ≤ D.R.r := by exact_mod_cast hkr
    omega
  · have h1 := Real.log_le_self hlrd0
    have h2 : L.sc.L / Cl ≤ L.sc.L := div_le_self (by linarith only [hL1]) (by linarith only [hCl2])
    linarith only [h1, h2, H11, hLk, hkr]
  · intro τ i
    refine lamS_abs_le τ _ (fun l h1 h2 => ⟨(d1 τ l h1 h2).1, ?_⟩) (fun j h1 h2 => ⟨hb1nn τ j h1 h2, hbsq τ j h1 h2⟩) i
    exact le_of_le_four_mul_of_mul_le_chain (by linarith only [hk5]) hDel0 hCl2 hm2 (d1 τ l h1 h2).2 (H8 τ 1 le_rfl hm1) (hbsq τ 1 le_rfl hm1)
  · unfold gg
    have h1 : (D.host.g 0 : ℝ) * D.host.g 1 ≤ L.sc.b ^ Cg * L.sc.b ^ Cg :=
      mul_le_mul H13 ContinuityOfCyclotomicCharacter (by positivity) (by positivity)
    rw [← Real.rpow_add hb0] at h1
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by linarith only [hb2]) (by linarith only [hA]))
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 0 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k H12
    exact_mod_cast h5
  · intro τ a c hac
    have hX : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by positivity
    have hle := gap_product_le_of_bounds hC hX hL1 hCl2 hCl3 H11
    have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by positivity
    have hg := gapAtLeast_of τ _ hG0 (fun l h1 h2 => (d1 τ l h1 h2).1) (hb1nn τ 1 le_rfl hm1) (H21 τ) a c hac
    rw [Real.log_mul hb0.ne' (by linarith only [hrd2]), hlogb]
    linarith only [hle, hg]
  · refine le_trans H5 (Real.sqrt_le_sqrt ?_)
    have : D.R.rS ≤ D.R.r := by
      have h4 := D.R.m_add_three_le_k
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      unfold Ranks.rS; omega
    exact_mod_cast this
  · rw [hlogb]
    have h1 := mul_le_mul_of_nonneg_left (k_le_rank_product hk5 hkr hf1 hlr) hcb.le
    linarith only [h1, hll]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountParameterConditionsOfSizeHypothesesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countParameterConditions_of_sizeHypotheses : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ), 0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl → Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT → AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  first | exact @GlobalTheory.countClauses_of_sizeHyp | exact GlobalTheory.countClauses_of_sizeHyp | (intros; apply GlobalTheory.countClauses_of_sizeHyp <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.IrrCountEv

theorem k_ge_of_hypLine {D : D7} (L : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D L C' Cl Cg cb Cu cT CT) :
    8 * L.CGam * L.sc.L ≤ D.R.k := by
  have h8 : 8 * L.CGam ≤ C' := hH.1
  have hk : C' * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L ≤ D.R.k := hH.2.1
  have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _
  have hmfL : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L := by positivity
  have h1 : 8 * L.CGam * ((D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L) :=
    mul_le_mul_of_nonneg_right h8 hmfL
  have h2 := logGam_ge L
  linarith

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem hypLine_ev (hR : ResidualStandingConditions Fm) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    Fm.x1 < x ∧ ArithmeticConditionsOfDatum (Fm.D x i) ∧
      StandingHypotheses (Fm.D x i) (Fm.L x i) Fm.CkLow (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu := by
  obtain ⟨r1, ⟨x5, HT⟩, x0, HR⟩ := hR
  have he := eps_pos' Fm
  obtain ⟨x4, hx4⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < eps / 100)).eventually_ge_atTop
      (max (2 * sCl Fm) (max 2 (5 / (eps / 100)))))
  refine ⟨max (Fm.x1 + 1) (max x0 (max x4 x5)), fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hx
    linarith
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx45 : max x4 x5 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx4' := hx4 x (le_trans (le_max_left _ _) hx45)
  obtain ⟨r2, hA⟩ := HR x hx0 i
  obtain ⟨t1, t2⟩ := HT x (le_trans (le_max_right _ _) hx45) i
  have r3 := tuWin_of (Fm.L x i) Fm.CTu t1 t2
  have hth : szTh (Fm.L x i) = eps / 100 := by unfold szTh; rw [Fm.L_eps]
  have hXX : XX (Fm.L x i) = x ^ (eps / 100) := by unfold XX; rw [hth, Fm.L_x x i hx1]
  have hH := standing_hypotheses_of_bounds (Fm.L x i) (Fm.params x hx1 i) (Fm.sizes x hx1 i) (sCl Fm) (1 / 2) Fm.CTu (sCl_pos Fm)
    (by rw [Fm.params_CCount]; exact sCl_le_CCount Fm) (by rw [Fm.params_Cgap]; exact sCl_le_Cgap Fm)
    (by rw [hXX]; exact le_trans (le_max_left _ _) hx4')
    (by rw [hXX]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx4')
    (by rw [hXX, hth]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx4')
    (by rw [Fm.params_CkLow, Fm.CGam_eq]; exact r1) r2 r3
  rw [Fm.params_CkLow, Fm.params_CYL] at hH
  exact ⟨hx1, hA, hH⟩

end Fam

theorem countClauses_closed : ∀ (𝒞 : FamClass) (c30 : List ℝ → CountingConstants),
    (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) →
    (∀ {eps : ℝ} (Fm : FamP eps), 0 < (c30 Fm.cOut).cb) →
    (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) →
    Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      AdmissibleBoundsFromSource.CountTheoremHypotheses (Fm.D x i) (Fm.L x i) (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).cb ∧
        4 * (Fm.D x i).R.r < (Fm.D x i).host.g 1 := by
  intro 𝒞 c30 hc30 hcb hTu
  refine Formalism.MainNotions.Pk.Closed.large (linkThresholds (fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) c30)
    (Formalism.MainNotions.Pk.Closed.of_class (P := fun Fm _ => TuSize Fm) fun Fm _ hc => hTu Fm hc) ?_
  intro eps Fm CH hL hT
  obtain ⟨-, hCl2, hCl3, h8⟩ := link_thresholds_spec Fm CH _ c30 hL
  have hR : ResidualStandingConditions Fm := ⟨h8, hT, Formalism.L2.SG.ResidEvFree.residEv_free Fm⟩
  obtain ⟨hC, hA⟩ := hc30 Fm
  have hcb7 := hcb Fm
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) ((c30 Fm.cOut).n0 : ℝ) (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually ((c30 Fm.cOut).cb * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  obtain ⟨x3, hx3⟩ := GlobalTheory.IrrCountEv.hypLine_ev Fm hR
  refine ⟨max x3 x4, fun x hx i => ?_⟩
  obtain ⟨hx1, hAr, hH⟩ := hx3 x (le_trans (le_max_left _ _) hx) i
  have hy := hx4 x (le_trans (le_max_right _ _) hx)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hLx := scL_eq Fm x hx1 i
  have hk8 := GlobalTheory.IrrCountEv.k_ge_of_hypLine (Fm.L x i) hH
  rw [hLx, Fm.CGam_eq x i] at hk8
  refine GlobalTheory.T.countParameterConditions_of_sizeHypotheses (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
    (c30 Fm.cOut).cb hC hcb7 hA ?_ hCl2 hCl3 ?_ hAr hH
  · have : ((c30 Fm.cOut).n0 : ℝ) ≤ (c30 Fm.cOut).n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hLx, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : (c30 Fm.cOut).cb * (8 * Fm.CGam * y ^ 8) ≤ (c30 Fm.cOut).cb * ((Fm.D x i).R.k : ℝ) :=
      mul_le_mul_of_nonneg_left hk8 hcb7.le
    push_cast
    nlinarith

end GlobalTheory.IrrCountEv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AllRowsAtRecord
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

noncomputable section

namespace GlobalTheory.AllRowsAtRecord

open Formalism.L2.SG.AllRowsOf

def stdChar (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  ZMod.stdAddChar

theorem stdChar_ne (D : D7) (k : Fin 2) : stdChar D k ≠ 1 := by
  intro hk
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
  change (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) = 1 at hk
  have h1 : (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 1 = (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 0 := by
    rw [hk, AddChar.one_apply, AddChar.map_zero_eq_one]
  exact one_ne_zero (ZMod.injective_stdAddChar h1)

theorem countAllRows_of {D : D7} (A : AllRows D) {c c₃ : ℝ} (hc : 0 < c) (hcc : c ≤ c₃) (hN : 2 ≤ D.R.r)
    (hf : 1 ≤ D.R.f) (hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D A.toAt c₃) (hpos : 0 < DstarE A A.B.e) :
    CountAllRows A (epsC c D.R.r D.R.f) := by
  have hL : 0 < Real.log (D.R.r : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hN0 : (0 : ℝ) < D.R.r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hf)
  have hP : 0 < (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by positivity
  refine ⟨(Real.exp_pos _).le, ?_, hpos, fun k S => ?_⟩
  · unfold epsC
    have h0 : 0 < c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by
      have := mul_pos hc hP
      linarith [this, show c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r) = c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r by ring]
    have h1 := Real.exp_lt_exp.mpr (show -(c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r) < 0 by linarith)
    rwa [Real.exp_zero] at h1
  · have h := hC k S
    change |((A.dimT (cyl D k S) : ℕ) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) * DstarE A (A.eT (cyl D k S)) at h
    rw [A.n_eq, A.f_eq] at h
    have hDs : 0 ≤ DstarE A (A.eT (cyl D k S)) :=
      (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (le_trans (abs_nonneg _) h)
    have hexp : Real.exp (-c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) ≤ epsC c D.R.r D.R.f := by
      unfold epsC
      apply Real.exp_le_exp.mpr
      have e1 : -c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) = -(c₃ * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      have e2 : -(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) = -(c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_right hcc hP.le
      linarith
    exact le_trans h (mul_le_mul_of_nonneg_right hexp hDs)

theorem allRows_at_record : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (G : GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (n₀ : ℕ) (Alev C₃ c₃ cb c : ℝ), 0 < c → c ≤ c₃ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    AutTie D X.B X.pl → RowDictTie X G ι → GlobalTheory.LabPin.LabTie X ι → (∀ P, CountE.CountIdempotentsClass P D n₀ Alev C₃ c₃ cb) →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n₀ Alev C₃ cb → 4 * D.R.r < D.host.g 1 →
    ∃ A : AllRows D, LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC c D.R.r D.R.f) := by
  intro hRF D large₂ X G ι n₀ Alev C₃ c₃ cb c hc hcc hG hAut hT hLab hCnt hp hg1
  have hL : RowsLab X := Formalism.L2.SG.Pf.AllRowsLab.rowsLab_holds X hRF hG G ι hT hLab hAut
  have hψ : ∀ k, stdChar D k ≠ 1 := stdChar_ne D
  have hB : CountBase X n₀ Alev C₃ cb := Formalism.L2.SG.Pf.AllRowsCountBase.countBase_of X hAut hp hg1
  refine ⟨Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact thirdTie_allRows (hI := etInt_holds X)
  · refine ⟨⟨X.pl, hAut⟩, fun v => Formalism.L2.SG.Pf.AllRowsCountBase.hc_X X hAut v, fun _ => ?_⟩
    change Formalism.MainNotions.S.SplitsCompl X.B.I.E X.B.g₀
    rw [X.g0_eq]
    exact Formalism.L2.SG.Pf.AllRowsCountBase.splits_X X 0
  · exact ⟨stdChar D, hψ, fun _ _ => rfl⟩
  · have hN : 2 ≤ D.R.r := le_trans (by norm_num) hG.1
    have hf : 1 ≤ D.R.f := by exact_mod_cast Formalism.MainNotions.S.one_le_f (D := D)
    have hTC := tieCountAt_allRowsOf (X := X) (ψ₀ := stdChar D) (hJ := ejIdem_holds D (stdChar D))
      (hU := etUniv_of X (redKer_of X (redKerOne_of X (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0)
        (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))))
      (hO := Formalism.L2.SG.Pf.AllRowsClosed.etOne_holds X (stdChar D) hψ) (hI := etInt_holds X) (hL := hL) hB
      (fun _ _ => Formalism.L2.SG.Pf.AllRowsClosed.etAlg_holds X _)
      (fun k S => Formalism.L2.SG.Pf.AllRowsClosed.etUnip_holds X k S)
    have hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D (Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL).toAt c₃ :=
      Formalism.MainNotions.N.CylinderCountFamily.countCylAt_of D _ (hCnt Formalism.MainNotions.S.CountE.PCount) hTC
        (Formalism.L2.SG.Pf.AllRowsPCount.pCountTie_holds X (stdChar D) hψ hL)
    obtain ⟨-, -, -, -, -, -, -, hpos⟩ := hB
    exact countAllRows_of _ hc hcc hN hf hC hpos

end GlobalTheory.AllRowsAtRecord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.IrrRowConcrete

theorem irr_row_closed : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  intro hSW hRF
  obtain ⟨c30, cIc, hc30, hcI, hcle, hP⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  refine ⟨cIc, hcI, fun 𝒞 hT hX => ?_⟩
  have hcb : ∀ {eps : ℝ} (Fm : FamP eps), 0 < (c30 Fm.cOut).cb := fun Fm =>
    (hP (fun _ _ _ _ => True) Fm).2.1
  have hEv := GlobalTheory.IrrCountEv.countClauses_closed 𝒞 c30 hc30 hcb hT
  have hGap := Formalism.L2.SG.GapClosed.gapEv_closed_of 𝒞 hT
  obtain ⟨a1, ha1, H1⟩ := (hX.and hEv).and hGap
  refine ⟨a1, ha1, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H1 e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hx, hev⟩, hg⟩ := hK Fm CH hc hL
  obtain ⟨x1, hx1⟩ := hx hc
  obtain ⟨x2, hx2⟩ := hev
  obtain ⟨y, hy⟩ := hg hc
  refine ⟨max (max x1 x2) (max y (Fm.x1 + 1)), fun x hxge i => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := (max_le_iff.mp hxge).imp max_le_iff.mp max_le_iff.mp
  have hxlt : Fm.x1 < x := (lt_add_of_pos_right _ zero_lt_one).trans_le b4
  obtain ⟨X, G, ι, hA, hR, hLab⟩ := hx1 x hxlt b1 i
  obtain ⟨hpar, h4⟩ := hx2 x b2 i
  exact GlobalTheory.AllRowsAtRecord.allRows_at_record hRF (Fm.D x i) (Fm.L x i) X G ι (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
    (c30 Fm.cOut).c (c30 Fm.cOut).cb cIc hcI (hcle Fm) (hy x b3 i) hA hR hLab (fun P => (hP P Fm).2.2 x i) hpar h4

end GlobalTheory.IrrRowConcrete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  exact GlobalTheory.IrrRowConcrete.irr_row_closed
end

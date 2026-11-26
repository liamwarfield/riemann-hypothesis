module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
namespace GlobalTheory

theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := GlobalTheory.T.binaryHermitianForm_represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevel
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem mu0Tie_of_colsTiedSym : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u :=
  fun _ C u => Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevelStatement
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u := by
  first | exact @GlobalTheory.mu0Tie_of_colsTiedSym | exact GlobalTheory.mu0Tie_of_colsTiedSym | (intros; apply GlobalTheory.mu0Tie_of_colsTiedSym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchingTranslateSameRowDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchingTranslateSameRowDoubleCoset
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgKey

theorem translate_key : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', ∀ s : TauC Y u u', s.lam = t₀.lam → s.lam' = t₀.lam' → (∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (a * t₀.lin * a'⁻¹) * n') → key s = key t := by
  intro D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨hl, hl', a, ha, a', ha', K1⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  refine ⟨a, ha, a', ha', ?_⟩
  rintro s hs hs' ⟨n, hn, n', hn', hsl⟩
  rw [GlobalTheory.Unfold.KeyIff.key_eq_iff]
  refine ⟨hs.trans hl.symm, hs'.trans hl'.symm, ?_⟩
  rw [hs, hsl]
  have hI : ∀ {x y : GV D}, x ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      x * y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun hx hy => (Formalism.HermitianLatticesTheory.isom _).mul_mem hx hy
  have ht : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have htΛ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have ha'i : a'⁻¹ ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := (GlobalTheory.KeyGroup.flagLatticeAutomorphismGroup _ _).inv_mem ha'
  have hγ : a * t₀.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI (hI ha.1.1 ht) ha'i.1.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹) t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, GlobalTheory.Unfold.Model.gmap_mul, ha'i.2, htΛ, ha.2]
  have hγn : a * t₀.lin * a'⁻¹ * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI hγ hn'.1.1
  have hγnΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹ * n') t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, hn'.1.2, hγΛ]
  have hs3 : n * (a * t₀.lin * a'⁻¹) * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [mul_assoc]; exact hI hn.1.1 hγn
  have hs3Λ : Formalism.HermitianLatticesTheory.gmap (n * (a * t₀.lin * a'⁻¹) * n') t₀.lam' = t₀.lam := by
    rw [mul_assoc, GlobalTheory.Unfold.Model.gmap_mul, hγnΛ, hn.1.2]
  have K2 := GlobalTheory.KeyGroup.keyEq_right (F := lf D (X.Fu u)) (F0' := X.Fu u') hγ hγΛ hn'
  have K3 := GlobalTheory.KeyGroup.keyEq_left (F0' := X.Fu u') hγn hn
  rw [← mul_assoc] at K3
  have K4 := GlobalTheory.KeyGroup.keyEq_trans hγ hγn hγΛ hγnΛ K2 K3
  have K5 := GlobalTheory.KeyGroup.keyEq_symm hγ hs3 hγΛ hs3Λ K4
  exact GlobalTheory.KeyGroup.keyEq_trans hs3 hγ hs3Λ hγΛ K5 K1

end GlobalTheory.Unfold.TgKey
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchingTranslateSameRowDoubleCosetStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_translate_same_row_double_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', ∀ s : TauC Y u u', s.lam = t₀.lam → s.lam' = t₀.lam' → (∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (a * t₀.lin * a'⁻¹) * n') → key s = key t := by
  first | exact @GlobalTheory.Unfold.TgKey.translate_key | exact GlobalTheory.Unfold.TgKey.translate_key | (intros; apply GlobalTheory.Unfold.TgKey.translate_key <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFunctionBlockExistsOfBesselCoef
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WlocExistsReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem wlocExists_real : WlocExists :=
  scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapBigOfComparison
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.GapAtRealPlaces

theorem gapBig_of_comparison (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ

  have hr : PI.ScGapBig.rk48 D.R.k D.R.rS = D.R.r := by
    simp only [PI.ScGapBig.rk48, Formalism.BasicNotions.Ranks.r]
    omega

  have hgaps : ∀ (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2),
      16 * (PI.ScGapBig.rk48 D.R.k D.R.rS : ℝ) ^ 19 ≤
        ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
    intro j hj
    have hlt : (Fin.cast hm.symm j).val + 1 < D.R.m := by
      rw [Fin.val_cast]
      omega
    have key := hG.2 τ (Fin.cast hm.symm j) hlt
    have hidx : (⟨(Fin.cast hm.symm j).val + 1, hlt⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.val + 1, hj⟩ :=
      Fin.ext rfl
    rw [hidx] at key
    rw [hr]
    exact_mod_cast key
  obtain ⟨t, hto, ht5, ht1801, hgap⟩ :=
    h D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)) (hr ▸ hG.1) hgaps
  exact ⟨t, hto, ht5, ht1801, hgap⟩

theorem gapBigOfGapHyp : ∀ D : D7, GapBigOfGapHyp D := by
  intro D
  exact gapBig_of_comparison scGapBig D

end GlobalTheory.GapAtRealPlaces
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.WBlockExists

theorem nUnimodLoc : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem realPlaceFunctionBlockExists_of_bessel_coef : BesselNVGap → CoefWeightedLoc → ∀ D : D7, GlobalTheory.St.WBlkExists D :=
  by
    intro hB hCW D hG A L Ps Rf Bu Pi Mu
    obtain ⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ := A
    exact Formalism.L2.SG.Pf.WFL.wblk_core quotient_product_compact
      Formalism.L2.SG.Pf.WFL.locHNProps_holds nUnimodLoc
      Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply hB hCW
      GlobalTheory.wlocExists_real (GlobalTheory.GapAtRealPlaces.gapBigOfGapHyp D)
      hG I ιE ιE_conj ιE_F bas J_eq L_eq pl φ_eq n_eq eps_eq L Ps Rf Bu Pi Mu

end GlobalTheory.WBlockExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsoluteHermitianVolumeBoundArith
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsoluteHermitianVolumeBoundArith
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.VolArith

theorem volU_two : volU 2 = 8 * Real.pi ^ 3 := by
  unfold volU sphV
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  norm_num
  ring

theorem one_le_fDeg (E : Type) [Field E] [NumberField E] : 1 ≤ Formalism.HermitianLatticesTheory.fDeg E :=
  Fintype.card_pos

theorem one_le_rd (E : Type) [Field E] [NumberField E] : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have h : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E)) (by positivity)
  linarith

theorem sum_half (n : ℕ) (hn : 2 ≤ n) :
    ∑ M ∈ Finset.Ioc 2 n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - 4) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, ih]
    push_cast
    ring

theorem lVal_le (E : Type) [Field E] [NumberField E] [StarRing E] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (M : ℕ) (hM : 3 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      Formalism.HermitianLatticesTheory.lValEta E M ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  obtain ⟨-, h0, h1⟩ := Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound E hE M hM
  refine ⟨h0, ?_⟩
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
    simpa using this
  have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
    hs.tsum_pos (fun m => by positivity) 0 (by positivity)
  rw [← Real.log_le_log_iff h0 (pow_pos hz _), Real.log_pow]
  exact (le_abs_self _).trans h1

theorem prod_rankFac_le (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ ∏ M ∈ Finset.Ioc 2 n, rankFac E M ∧
    ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) *
        1.4 ^ Formalism.HermitianLatticesTheory.fDeg E := by
  have hr := one_le_rd E
  have hr0 : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E := by linarith
  have hL : ∀ M ∈ Finset.Ioc 2 n, 0 ≤ Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).1.le
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr0, ← Finset.mul_sum, sum_half n hn]
  refine ⟨mul_nonneg (Real.rpow_nonneg hr0.le _) (Finset.prod_nonneg hL), ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)
  refine (Finset.prod_le_prod₀ hL (fun M hM => (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).2)).trans ?_
  rw [Finset.prod_pow]
  refine pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l) ?_ _
  have e : Finset.Ioc 2 n = Finset.Icc 3 n := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [e]
  exact (GlobalTheory.zetaProd_sphereVolume_bounds.2.1 n).le

theorem volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE n X hn hX hrX hfX
  obtain ⟨hP0, hP⟩ := prod_rankFac_le E hE n (by omega)
  have hr := one_le_rd E
  have hf := one_le_fDeg E
  set r := 2 * Formalism.HermitianLatticesTheory.vInv E with hrdef
  set f := Formalism.HermitianLatticesTheory.fDeg E with hfdef
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlog1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA : 1 + f * Real.log r ≤ X ^ 2 := by nlinarith
  have hA0 : 0 ≤ 1 + f * Real.log r := by positivity
  have hpi : Real.pi ^ 3 ≤ 3.15 ^ 3 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3
  have hc : 8 * Real.pi ^ 3 * 4 * 1.4 ≤ X ^ 11 := by
    have : (2 : ℝ) ^ 11 ≤ X ^ 11 := pow_le_pow_left₀ (by norm_num) hX 11
    nlinarith
  have hpi0 := Real.pi_pos
  have he0 : 0 ≤ (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2) := mul_nonneg (by linarith) (by nlinarith)
  have h1 : (8 * Real.pi ^ 3 * 4 * 1.4) ^ f ≤ (X ^ 11) ^ f := pow_le_pow_left₀ (by positivity) hc f
  have h2 : r ^ (5 * f) ≤ X ^ (5 * f) := pow_le_pow_left₀ (by linarith) hrX _
  have h3 : (1 + f * Real.log r) ^ (5 * f) ≤ (X ^ 2) ^ (5 * f) := pow_le_pow_left₀ hA0 hA _
  have h4 : r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) ≤ X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) :=
    Real.rpow_le_rpow (by linarith) hrX he0
  have hr0 : 0 < r := by linarith
  rw [volU_two]
  calc (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        ∏ M ∈ Finset.Ioc 2 n, rankFac E M
      ≤ (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        (r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) * 1.4 ^ f) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = (8 * Real.pi ^ 3 * 4 * 1.4) ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f) *
        r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [mul_pow (8 * Real.pi ^ 3 * 4), mul_pow (8 * Real.pi ^ 3)]
        ring
    _ ≤ (X ^ 11) ^ f * X ^ (5 * f) * (X ^ 2) ^ (5 * f) *
        X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        gcongr
    _ = X ^ (((26 * f : ℕ) : ℝ) + (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [Real.rpow_add hX0, Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 2
        ring
    _ ≤ X ^ ((n ^ 2 * f : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        push_cast
        have : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith
    _ = X ^ (n ^ 2 * f) := Real.rpow_natCast _ _

end GlobalTheory.VolArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsoluteHermitianVolumeBoundArithStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_hermitian_volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  first | exact @GlobalTheory.VolArith.volume_bound_arith | exact GlobalTheory.VolArith.volume_bound_arith | (intros; apply GlobalTheory.VolArith.volume_bound_arith <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInduction
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.AbsVol

theorem fDeg_congr {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) :
    Formalism.HermitianLatticesTheory.fDeg K = Formalism.HermitianLatticesTheory.fDeg L := by
  unfold Formalism.HermitianLatticesTheory.fDeg
  refine Fintype.card_congr
    { toFun := fun w => w.comap (e.symm : L →+* K)
      invFun := fun w => w.comap (e : K →+* L)
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · ext x
    simp
  · ext x
    simp

theorem vInv_congr {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) :
    Formalism.HermitianLatticesTheory.vInv K = Formalism.HermitianLatticesTheory.vInv L := by
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [fDeg_congr e, NumberField.discr_eq_discr_of_ringEquiv K e]

theorem volU_nonneg (i : ℕ) : 0 ≤ volU i := by
  unfold volU sphV
  positivity

theorem absoluteVolume_of_volumeStep : VolumeStep → AbsoluteVolume := by
  intro hstep I p q hsig hq hn X hX hrd hfrd c μf _ _ hc
  obtain ⟨hf, hv, -, -, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq' := hpq p q hsig
  have hp : 2 ≤ p := by
    by_contra h
    have h1 : 7 ≤ q := by omega
    have h2 : 7 * q ≤ q ^ 2 := by nlinarith
    omega
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hrat⟩ :=
    GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q 2 0 hsig hp (Nat.zero_le _) le_rfl
  obtain ⟨μ₀, hH, hS⟩ := GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary I₀
  choose c₀ _ hc₀ _ using fun v : InfinitePlace I₀.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  have hg₀ : IsGaugeAll I₀ c₀ := hc₀
  have hE := hrat I₀ hsame hsig₀ c μf c₀ μ₀ hc hg₀
  have hD := GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite I₀ 2 hsig₀ c₀ μ₀ hg₀
  have hV := GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound I₀.E I₀.cm.cmUnram
  obtain ⟨e, -⟩ := hsame
  obtain ⟨hf₀, -, -, -, -, -⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I₀
  rw [← hf₀, fDeg_congr e] at hD
  rw [fDeg_congr e, vInv_congr e] at hV
  have hA := GlobalTheory.T.absolute_hermitian_volume_bound_arith I.E I.cm.cmUnram I.n X hn hX (hv ▸ hrd) (by rw [hf, hv]; exact hfrd)
  have hv0 : 0 ≤ 2 * Formalism.HermitianLatticesTheory.vInv I.E := by
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  have hv1 : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv I.E := hv ▸ (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).2.2.1
  have hlog : 0 ≤ Real.log (2 * Formalism.HermitianLatticesTheory.vInv I.E) := Real.log_nonneg hv1
  have hU : 0 ≤ volU 2 ^ Formalism.HermitianLatticesTheory.fDeg I.E := pow_nonneg (volU_nonneg 2) _
  rw [hE, hpq', ← hf]
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hA)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hU]
  gcongr
  exact hD.trans (by gcongr)

end GlobalTheory.FlagMeas.AbsVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInductionStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction : VolumeStep → AbsoluteVolume := by
  first | exact @GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | exact GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLine
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LineMass

theorem sum_encard_fibre_le {α ι : Type*} (S : Set α) (f : α → ι) (s : Finset ι) :
    ∑ n ∈ s, (S ∩ {a | f a = n}).encard ≤ (S ∩ {a | f a ∈ s}).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : S ∩ {x | f x ∈ insert a s} = (S ∩ {x | f x = a}) ∪ (S ∩ {x | f x ∈ s}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, Set.mem_union]
      tauto
    rw [e, Set.encard_union_eq]
    · gcongr
    · rw [Set.disjoint_left]
      rintro x ⟨-, h1⟩ ⟨-, h2⟩
      exact ha (by rw [← show f x = a from h1]; exact h2)

theorem orbSum_finsetSum {G α ι : Type} [Group G] [MulAction G α] (X : Set α) (N : ι → α → ℝ≥0∞)
    (s : Finset ι) : ∑ n ∈ s, orbSum G X (N n) = orbSum G X (fun x => ∑ n ∈ s, N n x) := by
  obtain ⟨-, hconst, -, -, hadd⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive G α
  induction s using Finset.induction_on with
  | empty => simp [hconst]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hadd, ih]

theorem sub_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h1 : Module.finrank K V = 1)
    (M : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (X : ℕ) :
    {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N ≠ 0 ∧ idxN M N ≤ X}.encard ≤
      {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.encard := by
  by_cases hbot : M = ⊥
  · subst M
    by_cases hX : X = 0
    · subst X
      simp
    · have htop : (⊤ : Ideal (𝓞 K)) ∈ {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X} := by
        simp [Nat.one_le_iff_ne_zero.mpr hX]
      calc
        _ ≤ 1 := by
          apply Set.encard_le_one_iff.mpr
          intro a b ha hb
          exact (le_bot_iff.mp ha.1).trans (le_bot_iff.mp hb.1).symm
        _ ≤ _ := Set.one_le_encard_iff_nonempty.mpr ⟨⊤, htop⟩
  obtain ⟨e⟩ : Nonempty (V ≃ₗ[K] K) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simp [h1])
  let e' : V →ₗ[𝓞 K] K := (e : V →ₗ[K] K).restrictScalars (𝓞 K)
  obtain ⟨a, ha, hint⟩ : IsFractional (nonZeroDivisors (𝓞 K)) (M.map e') :=
    FractionalIdeal.isFractional_of_fg (hM.fg.map e')
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  let ψ : V →ₗ[𝓞 K] K := a • e'
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : a • e x = 0 := hx
    rw [smul_eq_zero] at this
    exact e.map_eq_zero_iff.1 (this.resolve_left ha0)
  let ι : 𝓞 K →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let J : Submodule (𝓞 K) V → Ideal (𝓞 K) := fun N => (N.map ψ).comap ι
  have hJ : ∀ N ≤ M, Submodule.map ι (J N) = N.map ψ := by
    intro N hN
    refine Submodule.map_comap_eq_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hint (e' x) ⟨x, hN hx, rfl⟩
    exact ⟨y, hy⟩
  have hle : ∀ N ≤ M, J N ≤ J M := fun N hN => Submodule.comap_mono (Submodule.map_mono hN)
  have hidx : ∀ N ≤ M, idxN M N * Ideal.absNorm (J M) = Ideal.absNorm (J N) := by
    intro N hN
    have e1 : idxN M N = (J N).toAddSubgroup.relIndex (J M).toAddSubgroup := by
      unfold idxN
      rw [← AddSubgroup.relIndex_map_map_of_injective (f := ψ.toAddMonoidHom) _ _ hψ,
        ← AddSubgroup.relIndex_map_map_of_injective (f := ι.toAddMonoidHom) (J N).toAddSubgroup _ hι]
      change (N.map ψ).toAddSubgroup.relIndex (M.map ψ).toAddSubgroup =
        (Submodule.map ι (J N)).toAddSubgroup.relIndex (Submodule.map ι (J M)).toAddSubgroup
      rw [hJ N hN, hJ M le_rfl]
    rw [e1]
    simpa only [Ideal.absNorm_eq_index] using
      AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono (hle N hN))
  have hJM : J M ≠ ⊥ := by
    intro h0
    have h2 := hJ M le_rfl
    rw [h0, Submodule.map_bot] at h2
    have h3 : M = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : ψ x ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ ⟨x, hx, rfl⟩
      exact (injective_iff_map_eq_zero ψ).1 hψ x this
    exact hbot h3
  have hq : ∀ N : Submodule (𝓞 K) V, ∃ I : Ideal (𝓞 K), N ≤ M → J N = J M * I := by
    intro N
    by_cases hN : N ≤ M
    · obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 (hle N hN)
      exact ⟨I, fun _ => hI⟩
    · exact ⟨⊥, fun h => (hN h).elim⟩
  choose q hq using hq
  refine Set.encard_le_encard_of_injOn (f := q) ?_ ?_
  · rintro N ⟨hN, h0, hX⟩
    have h2 := hidx N hN
    rw [hq N hN, map_mul, mul_comm] at h2
    have h3 := Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hJM)) h2
    refine ⟨fun hb => h0 (by rw [h3, hb, Ideal.absNorm_bot]), ?_⟩
    rw [← h3]
    exact_mod_cast hX
  · rintro N ⟨hN, -⟩ N' ⟨hN', -⟩ hqq
    apply Submodule.map_injective_of_injective hψ
    rw [← hJ N hN, ← hJ N' hN', hq N hN, hq N' hN', hqq]

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ 1 → ∀ X : ℕ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 (X ^ 2), orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h₁ I₁ * (X : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' I hs' hI X hX
  have hnd := SpaceMass.nondeg_of_PD h hp
  have hp' := SpaceMass.PD_of_ortho h' hK I _ hI
  have hnd' := SpaceMass.nondeg_of_PD h' hp'
  by_cases hE : ∃ M₁ : Submodule (𝓞 K) V, IsIntLat h M₁
  swap
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun n _ => ?_) zero_le
    unfold orbMass orbSum
    exact ENNReal.tsum_eq_zero.2 fun q => (hE ⟨_, q.2.1⟩).elim
  obtain ⟨M₁, hM₁⟩ := hE
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨M₀, hM₀, -⟩ := hex M₁ hM₁
  obtain ⟨c, hc⟩ := hMM K hK 1 le_rfl
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  have hIfull : Submodule.IsFullLattice K I := by
    refine { toIsLattice := hIl, span_eq_top := ?_ }
    obtain ⟨e, -, hspan, rfl, -⟩ := hI
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIfull hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  have hm₀ : mass h M₀ = c := by
    have : lamMax h M₀ = 1 := by
      unfold lamMax
      refine finprod_mem_of_eqOn_one fun P _ => ?_
      have : (qIn P : ℝ) + 1 ≠ 0 := by positivity
      simp only [hj, pow_one, sub_neg_eq_add, Pi.one_apply]
      exact div_self this
    rw [hc V h hs hp hj M₀ hM₀, this, mul_one]
  obtain ⟨mono, hconst, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have key : ∀ n : ℕ, orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbSum (isom h) (genus h M₀)
      (fun M' => ((({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard : ℕ∞) :
        ℝ≥0∞)) := by
    intro n
    have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
      intro g M hM
      have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M
        (SpaceMass.mem_genus_self h M hM.1.1)
      have h2 := (hdisc M hM.1).2.2.2.1 _ h1
      exact ⟨h2.1, h2.2.trans hM.2⟩
    let Y : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
      {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
    have hXst : Stable (isom h) Y := by
      rintro g p ⟨h1, h2, h3⟩
      exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
    have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
      (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
    have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
      (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
    have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) Y := by
      rw [f1]
      refine mono _ _ _ _ subset_rfl fun M hM => ?_
      obtain ⟨M', hM', hle⟩ := hex M hM.1
      have hne : (Y ∩ Prod.fst ⁻¹' {M}).Nonempty :=
        ⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
      have := Set.one_le_encard_iff_nonempty.2 hne
      exact_mod_cast this
    refine s1.trans ?_
    rw [f2]
    refine mono _ _ _ _ subset_rfl fun M' _ => ?_
    have : (Y ∩ Prod.snd ⁻¹' {M'}).encard ≤
        ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        exact ⟨⟨h1.1, h3⟩, h1.2⟩
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine (Finset.sum_le_sum fun n _ => key n).trans ?_
  rw [orbSum_finsetSum]
  obtain ⟨hIfin, hIcard⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K (X : ℝ) (by exact_mod_cast hX)
  have hexp : 1 + Real.logb 2 (Module.finrank ℚ K) = 2 + Real.logb 2 (fDeg K) := by
    have := hK.1
    have h2 : Module.finrank ℚ K = 2 * fDeg K := by
      unfold fDeg
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.finrank,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have h3 : (fDeg K : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := InfinitePlace K)).ne'
    rw [h2]
    push_cast
    rw [Real.logb_mul two_ne_zero h3, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [hexp] at hIcard
  rw [hcI, ← hm₀, mul_comm, ENNReal.ofReal_mul (by positivity), hmass, ← hconst]
  refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
  have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
  have a1 := sum_encard_fibre_le {N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} (fun N => discN h N)
    (Finset.Icc 1 (X ^ 2))
  have a2 : ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩
      {N | discN h N ∈ Finset.Icc 1 (X ^ 2)}).encard ≤
      {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N ≠ 0 ∧ idxN M' N ≤ X}.encard := by
    refine Set.encard_le_encard ?_
    rintro N ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨h4, h5⟩ := (hdisc N h1).2.2.1 M' hM''.1 h2
    refine ⟨h2, h4, ?_⟩
    have h6 : discN h N ≤ X ^ 2 := (Finset.mem_Icc.1 h3).2
    have h7 := Nat.pos_of_ne_zero (hdisc M' hM''.1).1
    have h8 : idxN M' N ^ 2 ≤ X ^ 2 := (Nat.le_mul_of_pos_left _ h7).trans (h5 ▸ h6)
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h8
  have a3 := (a1.trans a2).trans (sub_count hj M' hM'.1.toIsLattice X)
  rw [← hIfin.cast_ncard_eq] at a3
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hIcard)
  rw [ENNReal.ofReal_natCast]
  have a4 := ENat.toENNReal_le.2 a3
  rw [ENat.toENNReal_coe] at a4
  refine le_trans (le_of_eq ?_) a4
  exact (map_sum ENat.toENNRealRingHom _ _).symm

end GlobalTheory.Mass.LineMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLineStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalMass_integralLattices_bounded_det_line : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ 1 → ∀ X : ℕ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 (X ^ 2), orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h₁ I₁ * (X : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  first | exact @GlobalTheory.Mass.LineMass.main | exact GlobalTheory.Mass.LineMass.main | (intros; apply GlobalTheory.Mass.LineMass.main <;> assumption)
end
end

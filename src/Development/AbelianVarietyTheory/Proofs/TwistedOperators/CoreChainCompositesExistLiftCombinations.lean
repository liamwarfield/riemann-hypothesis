module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridStageLatticesPropertiesProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CongAssemble

open Matrix

variable {D : D7}

theorem isIntM_of_smul_maps {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (s : Lev.EAf D) (M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (h : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, s • (M *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsIntM (s • ((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1)) := by
  intro i j
  have h1 := (hfr _).1 (h _ (GlobalTheory.FrameIdeal.col_mem_hatL hfr j)) i
  have e1 : (β⁻¹ : GL (Fin n) (Lev.EAf D)).1 *ᵥ (s • (M *ᵥ (β.1 *ᵥ Pi.single j 1))) =
      s • (((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1) *ᵥ Pi.single j 1) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, Matrix.mulVec_single_one] at h1
  simpa [Matrix.smul_apply] using h1


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cong_assemble : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  classical
  intro D V Λ hsd Z e hZe 𝔪 h𝔪 g hg hx
  obtain ⟨β, hfr⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hsd)
  have hUA := GlobalTheory.LevSplit.finE_mem_UA V g
  have hγ : (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * (Lev.finE V g).1 * β.1 := by
    simp only [Units.val_mul]
  have hγi : ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * ((Lev.finE V g)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * β.1 := by
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have h1 : IsIntM (toEAf D e • (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγ]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').1
  have h2 : IsIntM (toEAf D e • ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγi]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').2.1
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral V Λ β hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, -, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element V (GlobalTheory.LevelNbhd.finPartG V g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC V g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame V β _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction V.rank β _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG V g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch V _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr k).1 hSt
  have hgSt : Lev.finE V g ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv
  have hfw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr hgSt
  have hbw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr (inv_mem hgSt)

  have h𝔪0 : 𝔪 ≠ ⊥ := by
    intro h0
    haveI := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.E
    exact Set.infinite_univ (Z.finite_toSet.subset fun PP _ => h𝔪 PP (by rw [h0]; exact bot_le))
  have hrad : (∏ PP ∈ Z, PP.asIdeal) ≤ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪0 (le_bot_iff.1 (h ▸ hJ))
    have hQ := h𝔪 ⟨J, hJp, hJ0⟩ hJ
    calc (∏ PP ∈ Z, PP.asIdeal) = (∏ PP ∈ Z.erase ⟨J, hJp, hJ0⟩, PP.asIdeal) * J := (Finset.prod_erase_mul _ _ hQ).symm
      _ ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right | exact Ideal.mul_le_left'
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg 𝔪 (IsNoetherian.noetherian _)
  have hle : (∏ PP ∈ Z, PP.asIdeal ^ N) ≤ 𝔪 := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_right_mono hrad N).trans hN
  obtain ⟨t, ht, htv⟩ := (GlobalTheory.IdemSumIdeal.isIdemSum_props e Z (fun _ => N) hZe).2.2
  refine GlobalTheory.ChiGrid.mem_congLev.2 ⟨hUA, fun x => ⟨fun hx' => hfw x hx', fun hx' => ?_⟩, fun x hx' => ?_⟩
  · have := hbw _ hx'
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  · have hw : (Lev.finE V g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := Submodule.sub_mem _ (hfw x hx') hx'
    have e1 : (Lev.finE V g).1 *ᵥ x - x = toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) +
        (1 - toEAf D e) • ((Lev.finE V g).1 *ᵥ x - x) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [e1]
    refine Submodule.add_mem _ (hx x hx').2.2 ?_
    rw [← htv]
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) (GlobalTheory.FrameIdeal.idS_smul_mem_hatL Λ ht hw)

end GlobalTheory.CongAssemble
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.CongAssemble.cong_assemble | exact GlobalTheory.CongAssemble.cong_assemble | (intros; apply GlobalTheory.CongAssemble.cong_assemble <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.TargetCoef

theorem coef_zero_of_target_eigen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  intro D ψ S T χS χT om hw m X hm F hF g y a b ha hb hab
  have hψ := hw.std
  have hG : IsThetaFunO ψ S T (om (1, g) F) := hw.om_pres _ F hF
  have hact : actO S T 1 g (actO S T 1 g⁻¹ y) = y := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 g y
    rwa [inv_one] at this
  have hy : heisO ψ S T y (om (1, g) F) = ψ b • om (1, g) F := by
    have e := hw.om_heis 1 g (actO S T 1 g⁻¹ y) F hF
    rw [hb, map_smul, hact] at e
    exact e.symm
  have hU := ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T m X hψ hm _ _ hG hF).2.2.2.2.2.2.1 y).1
  rw [hy, ha] at hU
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO at hU
  have hI : (∫ w in X, (ψ b • om (1, g) F) w * conj ((ψ a • F) w) ∂m) =
      (ψ b * conj (ψ a)) * ∫ w in X, om (1, g) F w * conj (F w) ∂m := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hI] at hU
  have hn : conj (ψ a) * ψ a = 1 := by
    rw [Complex.conj_mul', hψ.1.2.1 a]
    simp
  by_contra hne
  have hc : ψ b * conj (ψ a) = 1 := by
    have := congrArg (· / ∫ w in X, om (1, g) F w * conj (F w) ∂m) hU
    simpa [mul_div_assoc, div_self hne] using this
  apply hab
  calc ψ a = (ψ b * conj (ψ a)) * ψ a := by rw [hc, one_mul]
    _ = ψ b * (conj (ψ a) * ψ a) := by ring
    _ = ψ b := by rw [hn, mul_one]

end GlobalTheory.TargetCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.TargetCoef.coef_zero_of_target_eigen | exact GlobalTheory.TargetCoef.coef_zero_of_target_eigen | (intros; apply GlobalTheory.TargetCoef.coef_zero_of_target_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CosSupport

theorem isHalf_actO_one {D : D7} (S T : HSp D) (c : AE D) (h : GA D T) (y : WO S T) (hy : IsHalf c y) :
    IsHalf c (actO S T 1 h y) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hy k l]
  ring

theorem cosSupp : CosSupp := by
  classical
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ Φ hΦ m X hm g hg hne
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hw := W.om_is (.core i) (by show Node.InRange D.R.m (.core (i + 1)); simp [Node.InRange]; omega)
  have hth : IsThetaFunO W.ψ _ _ Φ := hΦ.1.1
  have hchar : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y)) := by
    intro y h1 h2 h3
    by_contra hne'
    exact hne (GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters D W.ψ _ _ _ _ (W.om (.core i)) hw m X hm Φ hth g y _ _ (hΦ.2 e he y h1 h2)
      (hΦ.2 e he _ (isHalf_actO_one _ _ _ _ y h1) h3) hne')
  have hloc := GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hchar
  refine GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent D (G.V (.core i)) (G.Λ (.core i)) (G.sp.P_is i (by omega)).sd G.pl.W0 e he G.modul ?_ g ?_ hloc
  · intro PP hPP
    have hprime : PP.asIdeal.IsPrime := PP.isPrime
    obtain ⟨v, hv, hle⟩ := hprime.prod_le.1 hPP
    have hle' : (G.pl.w v).asIdeal ≤ PP.asIdeal := hprime.le_of_pow_le hle
    have heq : G.pl.w v = PP := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hprime.ne_top hle')
    unfold Places.W0
    exact Finset.mem_image.2 ⟨v, hv, heq⟩
  · intro v hv
    apply hg v
    intro hvS
    exact hv _ (by unfold Places.W0; exact Finset.mem_image.2 ⟨v, hvS, rfl⟩) (G.pl.under_w hvS)

end GlobalTheory.CosSupport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup : CosSupp := by
  first | exact @GlobalTheory.CosSupport.cosSupp | exact GlobalTheory.CosSupport.cosSupp | (intros; apply GlobalTheory.CosSupport.cosSupp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainRealParametersCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainRealParametersCorrespond
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreOntoPar
open GlobalTheory.SignedHC GlobalTheory.PairLift Finset

theorem mem_dualPar' {S : SPar} {x : ℚ × Bool} : x ∈ dualPar S ↔ (-x.1, x.2) ∈ S := by
  simp only [dualPar, mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, h, he⟩
    rw [← he]; simpa using h
  · intro h; exact ⟨_, _, h, by simp⟩

theorem mem_block_neg {c y : ℚ} {t : ℕ} : y ∈ TPar.block (-c) t ↔ -y ∈ TPar.block c t := by
  rw [mem_block, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  · rintro ⟨a, ha, h⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith

theorem dual_partner (t : ℕ) (c : ℚ) (P : SPar) (hc : ∀ x ∈ P, x.1 ≠ c) :
    partner t true (-c) (-c) (dualPar P) = dualPar (GlobalTheory.SignedHC.flip (partner t false c c P)) := by
  ext ⟨y, b⟩
  rw [mem_dualPar', GlobalTheory.SignedHC.mem_flip]
  simp only [partner, mem_union, mem_image, Prod.exists, Prod.mk.injEq, mem_dualPar', sub_neg_eq_add,
    add_neg_cancel_right, sub_add_cancel]
  constructor
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, rfl, rfl⟩)
    · left
      refine ⟨-a, b', h, rfl, ?_⟩
      have hne : -a ≠ c := hc _ h
      by_cases h1 : a < -c
      · have h3 : ¬ (-a < c) := by linarith
        rw [if_pos h1] at h2; rw [if_neg h3]; subst h2; simp
      · have h3 : -a < c := lt_of_le_of_ne (by linarith) hne
        rw [if_neg h1] at h2; rw [if_pos h3]; subst h2; simp
    · right; exact ⟨-a, mem_block_neg.1 ha, rfl, rfl⟩
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, ha', hb⟩)
    · left
      have hne : -y ≠ c := hc _ h
      refine ⟨y, b', h, rfl, ?_⟩
      by_cases h1 : y < -c
      · have h3 : ¬ (-y < c) := by linarith
        rw [if_neg h3] at h2; rw [if_pos h1]; subst h2; simp
      · have h3 : -y < c := lt_of_le_of_ne (by linarith) hne
        rw [if_pos h3] at h2; rw [if_neg h1]; exact Bool.not_inj h2
    · right
      subst ha'
      refine ⟨y, mem_block_neg.2 ha, rfl, ?_⟩
      cases b
      · exact absurd hb (by decide)
      · rfl

theorem parOK_core : ParOK := by
  intro D hS i hi τ
  show GlobalTheory.EvenOnto.UpPair (GlobalTheory.ChiGrid.sLen D - 1) ((GlobalTheory.ChiGrid.num D 1 τ).parPi i) ((GlobalTheory.ChiGrid.num D 1 τ).parPi (i + 1)) _ _
  set G := GlobalTheory.ChiGrid.num D 1 τ with hGdef
  set c : ℚ := (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) : ℚ) with hc
  have hN : G.NearMid := GlobalTheory.ChiGrid.num_nearMid D 1 τ
  have hgp := (GlobalTheory.ChiGrid.isLeast_gap D 1).1
  have hγ : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 + 2 * GlobalTheory.ChiGrid.sLen D + 2 < GlobalTheory.ChiGrid.gap D 1 := hgp.2.1
  have hr := hS.1
  have hsl : GlobalTheory.ChiGrid.sLen D = D.R.r + 6 := rfl
  have hrk : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hkm := D.R.m_add_three_le_k
  have hs1 : 1 ≤ G.s := show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega
  have hq : G.s = 2 * (a + b + 2) + 1 := show GlobalTheory.ChiGrid.sLen D = _ by rw [hsl, hrk]; omega
  have hmN : D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN1 : 1800 < GlobalTheory.ChiGrid.bigN D := by unfold GlobalTheory.ChiGrid.bigN; omega
  have hγq : (G.s : ℚ) + 4 ≤ G.ga := by
    show (GlobalTheory.ChiGrid.sLen D : ℚ) + 4 ≤ (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : GlobalTheory.ChiGrid.sLen D + 4 ≤ GlobalTheory.ChiGrid.gap D 1)
  have hγ2 : 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < G.ga := by
    show 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 < GlobalTheory.ChiGrid.gap D 1)
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hsγ : (G.s : ℚ) ≤ G.ga := by linarith
  have hsq : (G.s : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) := rfl
  have hcastT : ((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega)]; simp
  have hfar : FarFrom c (((GlobalTheory.ChiGrid.sLen D : ℚ) + 2) / 2) (G.parPi i) :=
    GlobalTheory.ParPairArrows.far_parPi G hN hs1 hγq hi
  have hpart : partner (GlobalTheory.ChiGrid.sLen D - 1) false c c (G.parPi i) = GlobalTheory.SignedHC.flip (G.parPi (i + 1)) :=
    GlobalTheory.ParPairArrows.partner_parPi G hN hs1 hγq hi
  have hcne : ∀ x ∈ G.parPi i, x.1 ≠ c := fun x hx e => by
    have := hfar x.1 (fst_mem_entries hx)
    rw [e, sub_self, abs_zero] at this
    linarith
  have hflip : ∀ S : SPar, GlobalTheory.SignedHC.flip (GlobalTheory.SignedHC.flip S) = S := fun S => by
    ext ⟨x, s⟩; simp [mem_flip]
  have hP1 : partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i)) = dualPar (G.parPi (i + 1)) := by
    rw [dual_partner _ _ _ hcne, hpart, hflip]
  have hgapP : ∀ j, j ≤ D.R.m → GapOver (dualPar (G.parPi j)) (2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3) := by
    intro j hj x hx y hy hne
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hj _ hx _ hy hne
    have e : |(-x.1) - (-y.1)| = |x.1 - y.1| := by rw [show (-x.1) - (-y.1) = -(x.1 - y.1) by ring, abs_neg]
    rw [e] at this
    linarith
  have hne : (dualPar (G.parPi i)).Nonempty := by
    have h0 : (G.parPi i).Nonempty := ⟨_, GridData.mem_parPi.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)⟩
    exact h0.image _
  have hreg : IsRegular (dualPar (G.parPi i)) := by
    intro x hx y hy e
    by_contra hne'
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hi.le _ hx _ hy hne'
    rw [e, sub_self, abs_zero] at this
    linarith
  have hco : InCoset (-c + (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries (dualPar (G.parPi i))) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    obtain ⟨z, hz⟩ := GlobalTheory.ParPairArrows.inCoset_parPi G hq (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) - GlobalTheory.ChiGrid.sLen D) i (-x)
      (fst_mem_entries hs')
    have hcastG : ((G.s - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := hcastT
    rw [hcastG] at hz
    push_cast at hz
    refine ⟨-z, ?_⟩
    rw [hcastT]; push_cast
    linarith
  have hfar' : FarFrom (-c) ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (dualPar (G.parPi i)) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    have := hfar _ (fst_mem_entries hs')
    simp only at this
    have e : |x - -c| = |-x - c| := by rw [show x - -c = -(-x - c) by ring, abs_neg]
    rw [hcastT, e]
    linarith
  have hcard : (dualPar (G.parPi i)).card + (GlobalTheory.ChiGrid.sLen D - 1) ≤ GlobalTheory.ChiGrid.bigN D := by
    have hc0 : (dualPar (G.parPi i)).card ≤ (G.parPi i).card := card_image_le
    have hc := GlobalTheory.ParPairArrows.card_parPi G i
    have h1 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) ≤ D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) = i * (GlobalTheory.ChiGrid.sLen D - 1) + (GlobalTheory.ChiGrid.sLen D - 1) := Nat.succ_mul _ _
    have h3 : D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    change _ ≤ (D.R.m + 1) + (D.R.k - 1) + i * (GlobalTheory.ChiGrid.sLen D - 1) at hc
    show _ ≤ D.R.k + D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1)
    omega
  have hth := GlobalTheory.PairLift.FromSigned.thetaPar_partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i))
    (GlobalTheory.ChiGrid.bigN D) (by omega) hne hreg hco hfar' hcard hN1 (hgapP i hi.le) (by rw [hP1]; exact hgapP (i + 1) hi)
  obtain ⟨al, be, ga, de, hPe, (⟨hD, hP'⟩ | ⟨_, hP'⟩)⟩ := hth
  · refine ⟨al, be, ga, de, hD, ?_, ?_, ?_⟩
    · intro e he
      have hmem : ∃ s, (e + -c, s) ∈ dualPar (G.parPi i) := by
        rw [hPe]
        simp only [List.mem_append] at he
        rcases he with ((h | h) | h) | h
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
      obtain ⟨s, hs⟩ := hmem
      rw [mem_dualPar'] at hs
      simp only at hs
      have := hfar _ (fst_mem_entries hs)
      simp only at this
      have e1 : |-(e + -c) - c| = |e| := by rw [show -(e + -c) - c = -e by ring, abs_neg]
      rw [e1] at this
      rw [hcastT]
      linarith
    · rw [← hPe, dualPar_dualPar]
    · rw [← hP', hP1, dualPar_dualPar]
  · exfalso
    have hg := hgapP (i + 1) hi
    rw [← hP1, hP'] at hg
    have e0m : (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 ∈ block (GlobalTheory.ChiGrid.sLen D - 1) :=
      GlobalTheory.PairLift.FromSigned.mem_blockList.2 ⟨0, by omega, by simp⟩
    have hf : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, false) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) :=
      GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [e0m]⟩)
    have ht : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, true) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) := by
      rw [← hP']
      refine mem_union.2 (Or.inr (mem_image.2 ⟨_, mem_block.2 ⟨0, by omega, ?_⟩, rfl⟩))
      push_cast; ring
    have := hg _ ht _ hf (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.CoreOntoPar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainRealParametersCorrespondStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreChain_realParameters_correspond : ParOK := by
  first | exact @GlobalTheory.CoreOntoPar.parOK_core | exact GlobalTheory.CoreOntoPar.parOK_core | (intros; apply GlobalTheory.CoreOntoPar.parOK_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.CoreOnto.PreSteps

theorem preOK (hDF : DepFixed) : PreOK := by
  intro D hQ hS T L μ0 hL sc hc G W Mv hM i hi r r' hr hr' v M M'
  obtain ⟨hth, -, -, hbij, hmeas, hweil⟩ := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D W.ψ (G.V (.core i)) (G.V (.core (i + 1))) W.ψ_std
  have hom := W.om_is (.core i) (show i + 1 ≤ D.R.m by omega)
  obtain ⟨hcS, hcT⟩ := G.chr_core (i := i) (by omega)
  rw [hcS, hcT] at hom
  obtain ⟨ω, hω, hωx⟩ := hweil _ _ _ hom
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal D hQ T L μ0 hL sc G W Mv hM i hi
  obtain ⟨f, hvac, hsph, hcos⟩ := GlobalTheory.T.exists_cosetFockVacuumDatum D hQ T L μ0 hL sc G W Mv hM i hi r r' hr hr' _ _ (r.mod M) (r'.mod M') x₀ hx₀.1
  have hRL := (GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r'
  have hinj : Function.Injective (exch (G.V (.core i)) (G.V (.core (i + 1)))) := by
    intro F₁ F₂ h
    funext w
    obtain ⟨x, rfl⟩ := hbij.2 w
    exact congrFun h x
  refine ⟨ω, f, ⟨(hRL.2 _ _ ω).2 hω, fun τ => ?_, hvac, hsph, ?_, ?_⟩, hωx, fun φ => (hcos φ).1⟩
  · show GlobalTheory.EvenOnto.UpPair (sLen D - 1) (Node.par D sc.cGap (.core i) τ) (Node.par D sc.cGap (.core (i + 1)) τ)
      (-(cen D sc.cGap τ (D.R.m - i) : ℚ)) (-(cen D sc.cGap τ (D.R.m - i) : ℚ))
    rw [hc]
    exact GlobalTheory.T.coreChain_realParameters_correspond D hS i hi τ
  · intro φ κ hκ κ' hκ'
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    exact hinj ((hωx _ hthF κ κ').symm.trans (hDF D hQ T L μ0 hL sc G W Mv hM i hi (.core i) (Or.inr rfl) _ hD κ hκ κ' hκ'))
  · intro m X hX φ g hg hgb
    by_contra hne
    apply hgb
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    obtain ⟨m', X', hX', heq⟩ := hmeas m X hX
    have hne' : (∫ w in X', W.om (.core i) (1, g) (exch (G.V (.core i)) (G.V (.core (i + 1)))
        (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ)) w *
        conj (exch (G.V (.core i)) (G.V (.core (i + 1)))
          (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ) w) ∂m') ≠ 0 := by
      have h1 := hωx _ hthF g 1
      rw [map_one] at h1
      rw [h1, ← heq]
      exact hne
    have hsd := (G.sp.P_is i (by omega)).sd
    have hstab : ∀ w ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
        GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) w := by
      intro w hw
      have h0 := hg w hw
      have h1 : GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
          GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (GlobalTheory.AdelicU.frameLat r.sp) w := h0
      have hΛ : GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i)) := hr
      rw [hΛ, (GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i).2.1 w] at h1
      exact h1
    have hfin := GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup D hQ T L μ0 hL sc G W Mv hM i hi x₀ hx₀ _ (hcos φ) m' X' hX' g hstab hne'
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (G.V (.core i))).1 g
    refine ⟨⟨a, ha⟩, k, Subgroup.mem_inf.2 ⟨hk, ?_⟩, rfl⟩
    have ha' : Lev.finE (G.V (.core i)) a = 1 := by
      have h : finHom (G.V (.core i)) a = 1 := ha
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.core i)) a) = 1
      rw [h, map_one]
    show Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i)
    rw [map_mul, ha', one_mul] at hfin
    exact hfin

end GlobalTheory.CoreOnto.PreSteps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruenceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence : DepFixed → PreOK := by
  first | exact @GlobalTheory.CoreOnto.PreSteps.preOK | exact GlobalTheory.CoreOnto.PreSteps.preOK | (intros; apply GlobalTheory.CoreOnto.PreSteps.preOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStep
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.StepExists


set_option maxHeartbeats 1000000 in
theorem stepEx : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' ω f hpre
  obtain ⟨X, hX, -, -, hX3, hX4, hX5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties h1 h2
  have I : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries h1 h2 h3 h4 D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I)))
  have hrule : ∀ τ, RulePar X (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) := fun τ =>
    ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions h1 h2 D c.t _ _ _ _ (hpre.par τ)).2 X hX3 hX4 hX5).1
  have hwe : IsWeilExp c.ψ s.V s'.V (c.a k) (c.a k) ω :=
    ⟨c.χ k, c.χ k, hpre.weil, fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair h1 h2 D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf
    hpre.par).1
  have hItW := hIt ω f hwe hpre.vac
  have hL := hPL s.par s'.par (c.a k) (c.a k) hrule s.V s'.V s.M s'.M c.θ c.ψ hc.inf ω hwe f It hpre.vac hItW
    s'.ν s'.fd hs'.haar hs'.fund f (isVacF_of_isVacVec hpre.vac)

  have hlev : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v h,
      IntegrableOn (fun g => thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) *
        (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g) s'.fd s'.ν ∧
      ∫ g in s'.fd, thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) * (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g ∂s'.ν =
        u (It φ v) h := by
    intro F
    obtain ⟨F', hF', hint⟩ := hL _ (GlobalTheory.ChainOnto.multT_le_noLevel c.θ s'.M _ _ F.2)
    refine ⟨F', ?_, hint⟩
    have hlaw : ∀ P v, ∀ κ ∈ s.J, ∀ g, F' (It P v) (g * κ) = F' (It P v) g := by
      intro P v κ hκ g
      rw [← (hint P v (g * κ)).2, ← (hint P v g).2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
      have hm : ((g * κ, g') : GA D s.V × GA D s'.V) = (g, g') * (κ, 1) := by simp
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, hpre.law P κ hκ 1 (one_mem _)]
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s.V s.par s.M c.θ hc.inf _ _ (fun κ hκ => hs.fin hκ) F' hF' ?_
    intro w hw κ hκ g
    have hx := GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values h1 h2 D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.a k) (c.a k) ω f It hc.inf hwe
      hpre.vac hItW hw
    suffices e : F' w (g * κ) = F' w g by rw [e]; simp
    clear hw
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨P, v, _, rfl⟩ := hx; exact hlaw P v κ hκ g
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
    | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]

  let pt : PolF D s'.V.rank s.V.rank →ₗ[ℂ] (WO s.V s'.V → ℂ) :=
    pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f
  have hp : ptOf c.ψ c.θ s.M s'.M f = pt := rfl
  have hint : ∀ F : s'.CC c, ∀ φ v g, IntegrableOn (fun h => (LinearMap.proj 0 ∘ₗ ω (g, h)) (pt φ) *
      (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v h) s'.fd s'.ν := fun F φ v g => by
    obtain ⟨u, -, hu⟩ := hlev F
    exact (hu φ v g).1
  obtain ⟨B, hB⟩ := GlobalTheory.Chain.IoLift.exists_trilinear s'.ν s'.fd (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt
    (s'.CC c) hint
  have hex : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v, u (It φ v) = B φ v F := fun F => by
    obtain ⟨u, hu, he⟩ := hlev F
    refine ⟨u, hu, fun φ v => ?_⟩
    rw [hB]
    funext g
    exact ((he φ v g).2).symm
  have hun : ∀ u ∈ s.CC c, (∀ φ v, u (It φ v) = 0) → u = 0 := fun u hu h0 => by
    obtain ⟨φ, v, hne⟩ : ∃ φ v, It φ v ≠ 0 := by
      by_contra hn
      exact hItW.ne (LinearMap.ext₂ fun φ v => by_contra fun h => hn ⟨φ, v, h⟩)
    exact GlobalTheory.Grid.Sep.multT_eq_zero hu hne (h0 φ v)
  obtain ⟨io, hio⟩ := GlobalTheory.Chain.IoLift.ioExists_of_forall (T := It) (C' := s.CC c) hint B hB hex hun
  exact ⟨⟨ω, f, It, io⟩, rfl, rfl, ⟨hpre, hItW, hio⟩⟩

end GlobalTheory.EvenOnto.StepExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  first | exact @GlobalTheory.EvenOnto.StepExists.stepEx | exact GlobalTheory.EvenOnto.StepExists.stepEx | (intros; apply GlobalTheory.EvenOnto.StepExists.stepEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainCompositesExistLiftCombinations
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.ChainLifts

theorem chainEx (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hCW : GlobalTheory.Published.CasselmanWallach) (hDF : DepFixed) (hCM : CoreModels) : ChainEx := by
  intro D hq hsz T L μ0 hL sc hgap G W Mv hM v r₀ M₀ hr₀
  have hCom : (gridCom W).Is := GlobalTheory.T.testGridCommonData_properties_hold D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hStage := GlobalTheory.T.testGridStageLatticesProperties_proof D hq T L μ0 hL sc G W Mv hM
  have hPre := GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence hDF D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hCM' := hCM D hq T L μ0 hL sc G W Mv hM
  have hStep := GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step hDS hHC hCR hCW D
  have hConj := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCR D
  have hEx := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D

  have rapid : ∀ i, i ≤ D.R.m → ∀ r, IsCoreLat G i r → ∀ M (y : (gridStage G v i r M).CC (gridCom W)) w,
      GlobalTheory.Grow.RapidDec (G.V (.core i)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
    intro i hi r hr M y w
    have hs := (hStage i hi).2 r hr v M
    have h1 := (hConj (gridCom W) hCom i hi _ hs).1 y w
    exact ((hRL.2.1 _ r W.θ _ M ∅).2.2.2.2 _).1 h1.2.2.2.2

  have ext : ∀ k (F₀ : Fn G (.core 0)) (F : Fn G (.core (k + 1))) (f : Sch G (.coreDown k)), Dep W (.core k) f →
      GlobalTheory.Grow.RapidDec (G.V (.core (k + 1))) F → F₀ ∈ Below W v k (dn W v k f F) → F₀ ∈ Below W v (k + 1) F := by
    rintro k F₀ F f hf hF ⟨Ψ, h1, h2, h3, h4⟩
    refine ⟨Function.update Ψ (k + 1) F, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases eq_or_ne i (k + 1) with rfl | hne
      · rw [Function.update_self]; exact hF
      · rw [Function.update_of_ne hne]; exact h1 i (by omega)
    · intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨f', hf', e⟩ := h2 i hik
        refine ⟨f', hf', ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact e
      · obtain rfl : i = k := by omega
        refine ⟨f, hf, ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
        exact h4
    · rw [Function.update_of_ne (by omega)]; exact h3
    · exact Function.update_self _ _ _
  have key : ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧ ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k
      (gridStage G v k r M) Θ ∧ ∃ (I : Type) (N : I → SmT (gridStage G v k r M).M →ₗ[ℂ] SmT (gridStage G v 0 r₀ M₀).M),
      (∀ ι y w, GlobalTheory.EvenOnto.PiLocalization₂.val (Θ y) (N ι w) ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)) ∧
      (gridStage G v 0 r₀ M₀).KF ≤ Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w} := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨r₀, M₀, hr₀, LinearMap.id, GlobalTheory.EvenOnto.Reach.zero, PUnit, fun _ => LinearMap.id, ?_, ?_⟩
      · intro _ y w
        refine ⟨Function.update (fun i => (0 : Fn G (.core i))) 0 (GlobalTheory.EvenOnto.PiLocalization₂.val y w), ?_, ?_, ?_, ?_⟩
        · intro i hi
          obtain rfl : i = 0 := by omega
          show GlobalTheory.Grow.RapidDec _ (GlobalTheory.EvenOnto.PiLocalization₂.val y w)
          exact rapid 0 (Nat.zero_le _) r₀ hr₀ M₀ y w
        · intro i hi; omega
        · exact Function.update_self _ _ _
        · exact Function.update_self _ _ _
      · intro x hx
        exact Submodule.subset_span ⟨PUnit.unit, x, hx, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := ih (by omega)
      obtain ⟨r', hr'⟩ := (hStage (k + 1) hk).1
      obtain ⟨M', -⟩ := hCM' (k + 1) hk
      have hs := (hStage k (by omega)).2 r hr v M
      have hs' := (hStage (k + 1) hk).2 r' hr' v M'
      obtain ⟨ω, f, hpre, hexch, hdep⟩ := hPre k (by omega) r r' hr hr' v M M'
      have hkm : k < (gridCom W).m := by show k < D.R.m; omega
      obtain ⟨p, hpω, hpf, hp⟩ := hStep (gridCom W) hCom k hkm _ _ hs hs' ω f hpre
      subst hpω hpf
      refine ⟨r', M', hr', Θ ∘ₗ p.io, GlobalTheory.EvenOnto.Reach.step hΘ hs' p hp, I × PolF D _ _,
        fun q => N q.1 ∘ₗ p.It q.2, ?_, ?_⟩
      · rintro ⟨ι, P⟩ y w
        have h1 := ha ι (p.io y) (p.It P w)
        have hth : IsThetaFunO W.ψ (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P) :=
          ((hEx W.ψ (G.V (.core k)) (G.V (.core (k + 1))) W.ψ_std).1 _).2 (hdep P).1
        have heq : GlobalTheory.EvenOnto.PiLocalization₂.val (p.io y) (p.It P w) =
            dn W v k (exch (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
          funext g
          refine (hp.io.eq y P w g).symm.trans ?_
          simp only [Formalism.IndefR.Lift.liftInt, dn]
          congr 1
          funext h
          congr 1
          show _ = thetaKO (W.om (.core k)) (negGA _ h) g _
          unfold thetaKO
          rw [hexch _ hth g h]
          have hadj : GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0 = 0 := by
            simp [GlobalTheory.PairLift.adjO]
          show _ = (p.ω (g, h) (p.pt P)) (GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0)
          rw [hadj]
        rw [heq] at h1
        exact ext k _ _ _ (hdep P) (rapid (k + 1) hk r' hr' M' y w) h1
      · intro x hx
        have hx' := hb hx
        refine (Submodule.span_le.2 ?_) hx'
        rintro _ ⟨ι, w, hw, rfl⟩
        have hon := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ _ _ W.θ W.ψ ((gridCom W).a k) ((gridCom W).a k) p.ω p.f p.It
          hCom.inf ⟨(gridCom W).χ k, (gridCom W).χ k, hp.pre.weil, fun τ => ⟨hCom.exp k hkm τ, hCom.exp k hkm τ⟩⟩
          hp.pre.vac hp.it hw
        have hmap : (Submodule.span ℂ {w' | ∃ P, ∃ v' ∈ (gridStage G v (k + 1) r' M').KF, w' = p.It P v'}).map (N ι) ≤
            Submodule.span ℂ {x | ∃ q : I × PolF D _ _, ∃ w ∈ (gridStage G v (k + 1) r' M').KF, x = (N q.1 ∘ₗ p.It q.2) w} := by
          rw [Submodule.map_span]
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨P, v', hv', rfl⟩, rfl⟩
          exact Submodule.subset_span ⟨(ι, P), v', hv', rfl⟩
        exact hmap (Submodule.mem_map_of_mem hon)
  intro k hk
  obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := key k hk
  refine ⟨r, M, hr, Θ, hΘ, fun y x hx => ?_⟩
  let φ : SmT (gridStage G v 0 r₀ M₀).M →ₗ[ℂ] Fn G (.core 0) := (Θ y).1
  have hmap : (Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w}).map φ ≤
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)} := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨ι, w, -, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨w, ha ι y w⟩
  exact hmap (Submodule.mem_map_of_mem (hb hx))

end GlobalTheory.ChainLifts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainCompositesExistLiftCombinationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_composites_exist_lift_combinations : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → DepFixed → CoreModels → ChainEx := by
  first | exact @GlobalTheory.ChainLifts.chainEx | exact GlobalTheory.ChainLifts.chainEx | (intros; apply GlobalTheory.ChainLifts.chainEx <;> assumption)
end

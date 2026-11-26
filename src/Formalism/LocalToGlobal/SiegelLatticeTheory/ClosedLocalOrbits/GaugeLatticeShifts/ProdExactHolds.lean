module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsBox
noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

section Fac

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

theorem exists_box_alt (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) :
    ∃ S : ∀ i, Set (α i), (∀ i, MeasurableSet (S i)) ∧ (∀ i, μ i (S i) ≠ 0) ∧ ∀ i, μ i (S i) ≠ ∞ := by
  have key : ∀ i, ∃ s : Set (α i), MeasurableSet s ∧ μ i s ≠ 0 ∧ μ i s ≠ ∞ := by
    intro i
    by_contra hc
    push_neg at hc
    apply hne i
    have hz : ∀ n, μ i (spanningSets (μ i) n) = 0 := fun n => by
      by_contra h0
      exact (measure_spanningSets_lt_top (μ i) n).ne (hc _ (measurableSet_spanningSets _ n) h0)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ i)]
    exact measure_iUnion_null hz
  choose S hS1 hS2 hS3 using key
  exact ⟨S, hS1, hS2, hS3⟩

theorem pi_box_eval (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (S : ∀ i, Set (α i)) (v : ι) (A : Set (α v)) :
    Measure.pi μ (Set.univ.pi (Function.update S v A)) = μ v A * ∏ w ∈ Finset.univ.erase v, μ w (S w) := by
  rw [Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem factor_eq (μ μ' : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μ' i)]
    (hne : ∀ i, μ i ≠ 0) (v : ι) (hw : ∀ w, w ≠ v → μ' w = μ w) (h : Measure.pi μ' = Measure.pi μ) : μ' v = μ v := by
  obtain ⟨S, -, hS0, hSt⟩ := exists_box_alt μ hne
  ext A _
  have h1 := pi_box_eval μ' S v A
  have h2 := pi_box_eval μ S v A
  have hP : ∏ w ∈ Finset.univ.erase v, μ' w (S w) = ∏ w ∈ Finset.univ.erase v, μ w (S w) :=
    Finset.prod_congr rfl fun w hm => by rw [hw w (Finset.ne_of_mem_erase hm)]
  rw [h, h2, hP] at h1
  have hP0 : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hS0 w
  have hPt : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ ∞ := ENNReal.prod_ne_top fun w _ => hSt w
  exact ((ENNReal.mul_left_inj hP0 hPt).mp h1).symm

theorem factor_conc (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) (N : ∀ i, Set (α i))
    (hc : Measure.pi μ (Set.univ.pi N)ᶜ = 0) (v : ι) : μ v (N v)ᶜ = 0 := by
  have hsub : Set.univ.pi (Function.update (fun w => (Set.univ : Set (α w))) v (N v)ᶜ) ⊆
      (Set.univ.pi N)ᶜ := by
    intro x hx hxN
    have hv := hx v (Set.mem_univ v)
    rw [Function.update_self] at hv
    exact hv (hxN v (Set.mem_univ v))
  have h0 := measure_mono_null hsub hc
  rw [pi_box_eval] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exfalso
    obtain ⟨w, -, hw⟩ := Finset.prod_eq_zero_iff.mp h
    exact hne w (Measure.measure_univ_eq_zero.mp hw)

theorem factor_ne (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (h : Measure.pi μ ≠ 0) (v : ι) : μ v ≠ 0 := by
  intro hv
  apply h
  rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ Set.univ, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

end Fac

section FacG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, SecondCountableTopology (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, BorelSpace (G v)]

theorem factor_uniq (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (H : ∀ v, Subgroup (G v))
    (hH : ∀ v, IsClosed (H v : Set (G v))) (ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (ν v)]
    (hνc : ∀ v, ν v (H v : Set (G v))ᶜ = 0) (hνi : ∀ v, ∀ h ∈ H v, (ν v).map (fun x => h * x) = ν v)
    (hν0 : ∀ v, ν v ≠ 0) (h0 : Measure.pi μ ≠ 0)
    (hc : Measure.pi μ (Set.univ.pi fun v => (H v : Set (G v)))ᶜ = 0)
    (hi : ∀ g : (v : ι) → G v, (∀ v, g v ∈ H v) → (Measure.pi μ).map (fun x => g * x) = Measure.pi μ) (v : ι) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • ν v := by
  have hne : ∀ w, μ w ≠ 0 := fun w => factor_ne μ h0 w
  have hμc : μ v (H v : Set (G v))ᶜ = 0 := factor_conc μ hne (fun w => (H w : Set (G w))) hc v
  have hμi : ∀ h ∈ H v, (μ v).map (fun x => h * x) = μ v := by
    intro h hh
    let g : (w : ι) → G w := Pi.mulSingle v h
    have hg : ∀ w, g w ∈ H w := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [g] using hh
      · simp [g, Pi.mulSingle_eq_of_ne hw, (H w).one_mem]
    let μ' : ∀ w, Measure (G w) := fun w => (μ w).map (fun x => g w * x)
    haveI hσ : ∀ w, SigmaFinite (μ' w) := fun w =>
      (MeasurableEquiv.mulLeft (g w)).sigmaFinite_map (μ := μ w)
    have hpi : Measure.pi μ' = Measure.pi μ := by
      rw [← Measure.pi_map_pi (fun w => (measurable_const_mul (g w)).aemeasurable)]
      exact hi g hg
    have hw : ∀ w, w ≠ v → μ' w = μ w := by
      intro w hw
      simp [μ', g, Pi.mulSingle_eq_of_ne hw]
    have := factor_eq μ μ' hne v hw hpi
    simpa [μ', g] using this
  exact uniq_on_closed (H v) (hH v) (μ v) (ν v) hμc (hνc v) hμi (hνi v) (hne v) (hν0 v)

end FacG

end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
end
end

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sf_smul {β : Type*} [MeasurableSpace β] (μ : Measure β) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    SigmaFinite (c • μ) := by
  rw [← ENNReal.coe_toNNReal hc, ← ENNReal.smul_def]
  infer_instance

theorem ProdExact_holds : Formalism.L2.SG.Pf.NcReal.ProdExact := by
  classical
  intro D X u u' μN μN' μH μH' C hσN hσN' hσH hσH' hC hN hN' hH hH' hDis
  haveI : ∀ v, SigmaFinite (μN v) := hσN
  haveI : ∀ v, SigmaFinite (μN' v) := hσN'
  haveI : ∀ v, SigmaFinite (μH v) := hσH
  haveI : ∀ v, SigmaFinite (μH' v) := hσH'
  have hU : UnimodLoc := JL.rightInvS_of JL.setCorr_holds (JL.haarCorr_of JL.setCorr_holds)
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    NilradicalHermitianFrames.NH.NHLoc_holds _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _
      (muNv_haar X w v) (muHv_haar X w v)

  have fN : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muN w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muNv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muN_haar w
    rw [← NinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [NinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (NGv X w) (fun v => NilradicalHermitianFrames.NH.NG_closed _ _ _) (muNv X w)
      (fun v => (muNv_haar X w v).1.2.2.1) (fun v => (muNv_haar X w v).1.2.2.2) (fun v => (muNv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  have fH : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muH w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muHv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muH_haar w
    rw [← HinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [HinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (HGv X w) (fun v => NilradicalHermitianFrames.NH.HG_closed _ _ _ _) (muHv X w)
      (fun v => (muHv_haar X w v).1.2.2.1) (fun v => (muHv_haar X w v).1.2.2.2) (fun v => (muHv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  choose κN hκN0 hκNT hκN using fN u μN hN
  choose κN' hκN'0 hκN'T hκN' using fN u' μN' hN'
  choose κH hκH0 hκHT hκH using fH u μH hH
  choose κH' hκH'0 hκH'T hκH' using fH u' μH' hH'
  have hSL : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) = (κN v * κH v) • muSv X u v := fun v => by
    haveI : SigmaFinite (muHv X u v) := inferInstance
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN v, hκH v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    all_goals exact measurable_mul.aemeasurable
  have hSL' : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) = (κN' v * κH' v) • muSv X u' v := fun v => by
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN' v, hκH' v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    all_goals exact measurable_mul.aemeasurable
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  haveI hσS : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) := fun v => by
    rw [hSL v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκNT v) (hκHT v))
  haveI hσS' : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) := fun v => by
    rw [hSL' v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκN'T v) (hκH'T v))

  have hmS : ∀ (w : D.what₂.Word) (ρN ρH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (ρN v)]
      [∀ v, SigmaFinite (ρH v)] [∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v))],
      X.muN w = Measure.pi ρN → X.muH w = Measure.pi ρH →
      muS X w = Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v) := by
    intro w ρN ρH _ _ hσ h1 h2
    unfold muS
    rw [h1, h2]
    have mp := measurePreserving_piProd ρN ρH
    rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
      mp.measurable]
    haveI : ∀ v, SigmaFinite (((ρN v).prod (ρH v)).map
        (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hσ
    exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
      (fun v => measurable_mul.aemeasurable)
  have hmu := hmS u μN μH hN hH
  have hmu' := hmS u' μN' μH' hN' hH'

  have hsec := fun v => SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) one_pos
  choose hs hsm hss using hsec
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)).prod ((Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)).prod
        (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)))).map (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v (hs v) (hss v))
  intro φ hφ
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v))
    (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]
  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := Measurable.of_eval fun v => (hsm v).comp (measurable_pi_apply v)
  set μP := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) with hμP
  set μP' := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) with hμP'
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂μP' ∂μP with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂μP' ∂μP
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v
  have hW : ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)) =
      ENNReal.ofReal ((∏ v, C v) * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hC v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl
  have hex := StepReal_holds D X u u' 1 one_pos c hc
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hdc := fun v => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) (c v)
    (hcv v) (hs v (c v)) (hOf X u u' 1 c v) (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' 1 c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : μP.map (fun x => x * t) = μP :=
    PiM.pi_map_mul_right _ t fun v => by
      rw [hSL v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)]
      exact (measurable_id.mul measurable_const).aemeasurable
  have hrt' : μP'.map (fun x => x * t') = μP' :=
    PiM.pi_map_mul_right _ t' fun v => by
      rw [hSL' v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)]
      exact (measurable_id.mul measurable_const).aemeasurable
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' 1 c * s'⁻¹) ∂μP' ∂μP = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'
  rw [hW, hmu, hmu', hsw]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness

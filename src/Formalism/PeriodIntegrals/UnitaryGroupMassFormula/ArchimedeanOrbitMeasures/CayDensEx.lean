module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SumLPresHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HuaInvOfTauDeriv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HasFDerivAtTauR

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHaar
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PreimageSubsetImage
noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

instance instT2SpaceUnitaryPQ (P Q : ℕ) : T2Space (UpqT P Q) := (isClosedEmbedding_mat P Q).isEmbedding.t2Space

section SlopeTestRemainingChoices

variable {P Q : ℕ}

theorem continuousOn_cayInv : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by
  have e : cayInv P Q = fun g => ⟨cayCand P Q g, cayCand_mem P Q g⟩ :=
    funext (cayInv_eq P Q)
  rw [e]
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  show ContinuousOn (cayCand P Q) (cayS (D0 P Q))
  intro g hg
  have hdet : IsUnit (g.mat + 1).det := by
    rw [cayley_domain_eq] at hg
    exact hg
  unfold cayCand
  have hc : ContinuousAt (fun g : UpqT P Q => g.mat) g := continuous_mat.continuousAt
  have hinv : ContinuousAt (fun g : UpqT P Q => (g.mat + 1)⁻¹) g := by
    have hdet_cont : ContinuousAt Ring.inverse (g.mat + 1).det := by
      obtain ⟨u, hu⟩ := hdet
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    have hadd : ContinuousAt (fun x : UpqT P Q => x.mat + 1) g :=
      hc.add continuousAt_const
    exact (continuousAt_matrix_inv (g.mat + 1) hdet_cont).comp
      (f := fun x : UpqT P Q => x.mat + 1) (x := g) hadd
  exact ((continuousAt_const.mul hinv).mul (hc.sub continuousAt_const)).continuousWithinAt

theorem betaH_apply (lam : Measure (lieU P Q)) (S : Set (UpqT P Q)) (hS : MeasurableSet S) :
    betaH P Q lam S = ∫⁻ X in cayF P Q ⁻¹' S ∩ D0 P Q, rhoH P Q X ∂lam := by
  unfold betaH
  rw [Measure.map_apply measurable_cayF hS, withDensity_apply _ (measurable_cayF hS),
    Measure.restrict_restrict (measurable_cayF hS)]

theorem preimage_subset_image (S : Set (UpqT P Q)) :
    cayF P Q ⁻¹' S ∩ D0 P Q ⊆ cayInv P Q '' S := by
  rintro X ⟨hXS, hXD⟩
  exact ⟨cayF P Q X, hXS, cayInv_cayF X hXD⟩

end SlopeTestRemainingChoices

end HcInf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExLHU
noncomputable section

namespace HcInf

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise

section LHU

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lhu_right (m : Measure G) [m.IsHaarMeasure] (z : G) :
    ∃ r : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → m {x | x * z ∈ B} = r * m B := by
  have hmeas : Measurable (fun x : G => x * z) := measurable_mul_const z
  haveI : (m.map (fun x : G => x * z)).IsMulLeftInvariant := ⟨fun g => by
    rw [Measure.map_map (measurable_const_mul g) hmeas]
    have hc : ((fun x : G => g * x) ∘ fun x => x * z) = (fun x => x * z) ∘ fun x => g * x := by
      funext x; simp [mul_assoc]
    rw [hc, ← Measure.map_map hmeas (measurable_const_mul g), map_mul_left_eq_self]⟩
  haveI : IsFiniteMeasureOnCompacts (m.map (fun x : G => x * z)) := ⟨fun K hK => by
    rw [Measure.map_apply hmeas hK.measurableSet]
    exact ((Homeomorph.mulRight z).isCompact_preimage.2 hK).measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, m.map (fun x : G => x * z) = c • m :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun B hB => ?_⟩
  show m ((fun x : G => x * z) ⁻¹' B) = _
  rw [← Measure.map_apply hmeas hB, hc, Measure.coe_nnreal_smul_apply]

theorem lhu_key (m : Measure G) [m.IsHaarMeasure] (β : Measure G) (W V : Set G)
    (hinv : ∀ (h : G) (S : Set G), MeasurableSet S → S ⊆ W → (fun g => h * g) '' S ⊆ W →
      β ((fun g => h * g) '' S) = β S)
    (hVc : IsCompact V) (hVW : V ⊆ W) (hVW' : ∀ v ∈ V, v⁻¹ ∈ W) (hβV : β V ≠ ⊤) (hβVi : β V⁻¹ ≠ ⊤) :
    ∃ K : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → B ⊆ V → m V * β B = K * m B := by

  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hVim : MeasurableSet V⁻¹ := hVc.inv.isClosed.measurableSet
  have hViW : V⁻¹ ⊆ W := fun x hx => by simpa using hVW' x⁻¹ hx
  choose r hr using fun z => lhu_right m z
  refine ⟨∫⁻ x in V⁻¹, r x ∂β, fun B hB hBV => ?_⟩
  haveI : IsFiniteMeasure (β.restrict V⁻¹) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hβVi⟩
  haveI : IsFiniteMeasure (β.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hBV) (lt_top_iff_ne_top.2 hβV)⟩
  have hmB : m B ≠ ⊤ := ne_top_of_le_ne_top hVc.measure_lt_top.ne (measure_mono hBV)
  have hE : MeasurableSet {p : G × G | p.2 * p.1 ∈ B} := (measurable_snd.mul measurable_fst) hB
  have hF : MeasurableSet {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} :=
    (measurable_snd.inv.mul measurable_fst) hVim
  have ha : ((β.restrict V⁻¹).prod m) {p : G × G | p.2 * p.1 ∈ B}
      = (∫⁻ x in V⁻¹, r x ∂β) * m B := by
    rw [Measure.prod_apply hE]
    calc _ = ∫⁻ x, r x * m B ∂(β.restrict V⁻¹) := lintegral_congr (fun x => hr x B hB)
      _ = (∫⁻ x in V⁻¹, r x ∂β) * m B := lintegral_mul_const' _ _ hmB
  have h1 : ∀ t : G, (β.restrict V⁻¹) ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B})
      = (β.restrict B) ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) := by
    intro t
    have hS : MeasurableSet ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B}) :=
      measurable_const_mul t hB
    have hT : MeasurableSet ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) :=
      measurable_const_mul t⁻¹ hVim
    rw [Measure.restrict_apply hS, Measure.restrict_apply hT]
    have himg : (fun g => t * g) '' ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B} ∩ V⁻¹)
        = (fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} ∩ B := by
      ext y
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        refine ⟨?_, hx1⟩
        show t⁻¹ * (t * x) ∈ V⁻¹
        rwa [inv_mul_cancel_left]
      · rintro ⟨hy1, hy2⟩
        refine ⟨t⁻¹ * y, ⟨?_, hy1⟩, mul_inv_cancel_left t y⟩
        show t * (t⁻¹ * y) ∈ B
        rwa [mul_inv_cancel_left]
    have hsub : (fun g => t * g) '' ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B} ∩ V⁻¹) ⊆ W := by
      rw [himg]; exact fun y hy => hVW (hBV hy.2)
    rw [← himg]
    exact (hinv t _ (hS.inter hVim) (fun x hx => hViW hx.2) hsub).symm
  have hb : ((β.restrict V⁻¹).prod m) {p : G × G | p.2 * p.1 ∈ B} = m V * β B := by
    rw [Measure.prod_apply_symm hE]
    calc _ = ∫⁻ t, (β.restrict B) ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) ∂m :=
          lintegral_congr h1
      _ = ((β.restrict B).prod m) {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} :=
          (Measure.prod_apply_symm hF).symm
      _ = ∫⁻ y, m (Prod.mk y ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) ∂(β.restrict B) :=
          Measure.prod_apply hF
      _ = ∫⁻ y, m V ∂(β.restrict B) := by
          refine lintegral_congr (fun y => ?_)
          have hpre : Prod.mk y ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} = (fun t => y⁻¹ * t) ⁻¹' V := by
            ext t; simp [mul_inv_rev]
          rw [hpre, measure_preimage_mul]
      _ = m V * β B := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact hb.symm.trans ha

theorem local_haar_unique : LocalHaarUnique := by
  intro G _ _ _ _ _ _ _ _ m hm β W hWo h1W hinv hfin hβW
  have hU : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (hWo.mem_nhds h1W) (hWo.inv.mem_nhds (by simpa using h1W))
  obtain ⟨V, hV1, hVsub, hVc⟩ := local_compact_nhds hU
  have hVW : V ⊆ W := fun x hx => (hVsub hx).1
  have hVW' : ∀ v ∈ V, v⁻¹ ∈ W := fun v hv => (hVsub hv).2
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hβV : β V ≠ ⊤ := hfin V hVc hVW
  have hβVi : β V⁻¹ ≠ ⊤ := hfin V⁻¹ hVc.inv (fun x hx => by simpa using hVW' x⁻¹ hx)
  have h1V : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.2 hV1
  have hmV0 : m V ≠ 0 :=
    ((isOpen_interior.measure_pos m ⟨1, h1V⟩).trans_le (measure_mono interior_subset)).ne'
  have hmVt : m V ≠ ⊤ := hVc.measure_lt_top.ne

  have hβV0 : β V ≠ 0 := by
    intro h0
    apply hβW
    let U : G → Set G := fun w => W ∩ (fun x => w⁻¹ * x) ⁻¹' interior V
    have hUo : ∀ w, IsOpen (U w) := fun w =>
      hWo.inter (isOpen_interior.preimage (continuous_const.mul continuous_id))
    have hU0 : ∀ w, β (U w) = 0 := by
      intro w
      have hSm : MeasurableSet ((fun x => w * x) ⁻¹' U w) :=
        measurable_const_mul w (hUo w).measurableSet
      have hSV : (fun x => w * x) ⁻¹' U w ⊆ V := by
        intro x hx
        have hx2 := hx.2
        simp only [Set.mem_preimage, inv_mul_cancel_left] at hx2
        exact interior_subset hx2
      have himg : (fun g => w * g) '' ((fun x => w * x) ⁻¹' U w) = U w :=
        Set.image_preimage_eq _ (mul_left_surjective w)
      have h := hinv w _ hSm (hSV.trans hVW) (by rw [himg]; exact fun y hy => hy.1)
      rw [himg] at h
      rw [h]
      exact measure_mono_null hSV h0
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
    have hWU : W ⊆ ⋃ w ∈ T, U w := by
      rw [hTU]
      intro x hx
      exact Set.mem_iUnion.2 ⟨x, hx, by simpa using h1V⟩
    exact measure_mono_null hWU ((measure_biUnion_null_iff hTc).2 (fun w _ => hU0 w))
  obtain ⟨K, hK⟩ := lhu_key m β W V hinv hVc hVW hVW' hβV hβVi
  refine ⟨β V / m V, (ENNReal.div_pos hβV0 hmVt).ne', ENNReal.div_ne_top hβV hmV0, V, hV1, hVW, ?_⟩
  ext s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have h1 := hK (s ∩ V) (hs.inter hVm) (fun x hx => hx.2)
  have h2 := hK V hVm subset_rfl
  have e1 : β (s ∩ V) = (m V)⁻¹ * (K * m (s ∩ V)) := by
    rw [← h1, ← mul_assoc, ENNReal.inv_mul_cancel hmV0 hmVt, one_mul]
  have e2 : β V = (m V)⁻¹ * (K * m V) := by
    rw [← h2, ← mul_assoc, ENNReal.inv_mul_cancel hmV0 hmVt, one_mul]
  rw [e1, div_eq_mul_inv, e2]
  calc (m V)⁻¹ * (K * m (s ∩ V)) = (m V)⁻¹ * K * (m V * (m V)⁻¹) * m (s ∩ V) := by
        rw [ENNReal.mul_inv_cancel hmV0 hmVt, mul_one, mul_assoc]
    _ = (m V)⁻¹ * (K * m V) * (m V)⁻¹ * m (s ∩ V) := by ring

end LHU

end HcInf
end
end

noncomputable section

namespace HcHDC

open HcInf HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem cayDensU (P Q : ℕ) (m : Measure (UpqT P Q)) [hm : m.IsHaarMeasure] (lam : Measure (lieU P Q))
    [hlam : lam.IsAddHaarMeasure] :
    ∃ D ∈ 𝓝 (0 : lieU P Q), MeasurableSet D ∧ ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧ ContinuousAt f 0 ∧
      f 0 ≠ 0 ∧ f 0 ≠ ⊤ ∧ (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f := by

  have hW : IsOpen (cayS (D0 P Q)) := isOpen_cayley_domain (P := P) (Q := Q)
  have h00 : (0 : lieU P Q) ∈ D0 P Q := zero_mem_cayley_domain (P := P) (Q := Q)
  have h1W : (1 : UpqT P Q) ∈ cayS (D0 P Q) := by
    have h := cayF_spec (P := P) (Q := Q) 0 h00
    rw [cayF_zero (P := P) (Q := Q)] at h
    exact ⟨0, h00, h⟩
  have hHua : HuaInv := huaInv_of_tauDeriv tau_derivative
  have hinv : ∀ (h : UpqT P Q) (S : Set (UpqT P Q)), MeasurableSet S → S ⊆ cayS (D0 P Q) →
      (fun g => h * g) '' S ⊆ cayS (D0 P Q) →
      betaH P Q lam ((fun g => h * g) '' S) = betaH P Q lam S :=
    fun h S hS hSW hhSW => hHua P Q lam hlam h S hS hSW hhSW

  have hcpt : ∀ K, IsCompact K → K ⊆ cayS (D0 P Q) → betaH P Q lam K ≠ ⊤ := by
    intro K hK hKW
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hCc : IsCompact (insert (0 : lieU P Q) (cayInv P Q '' K)) :=
      (hK.image_of_continuousOn ((continuousOn_cayInv (P := P) (Q := Q)).mono hKW)).insert 0
    have hC0 : insert (0 : lieU P Q) (cayInv P Q '' K) ⊆ D0 P Q := by
      rintro X (rfl | ⟨g, hg, rfl⟩)
      · exact h00
      · obtain ⟨Y, hY, hrel⟩ := hKW hg
        rw [cayley_inverse_iff P Q g Y hrel]
        exact hY
    obtain ⟨x0, -, hmax⟩ := hCc.exists_isMaxOn ⟨0, Set.mem_insert _ _⟩
      (fun x hx => (continuousAt_rhoH (P := P) (Q := Q) x (hC0 hx)).continuousWithinAt)
    have hS'm : MeasurableSet (cayF P Q ⁻¹' K ∩ D0 P Q) :=
      (measurable_cayF (P := P) (Q := Q) hKm).inter (isOpen_cell_domain (P := P) (Q := Q)).measurableSet
    have hS'C : cayF P Q ⁻¹' K ∩ D0 P Q ⊆ insert (0 : lieU P Q) (cayInv P Q '' K) :=
      fun X hX => Set.mem_insert_of_mem _ (preimage_subset_image (P := P) (Q := Q) K hX)
    rw [betaH_apply (P := P) (Q := Q) lam K hKm]
    apply ne_of_lt
    calc ∫⁻ X in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q X ∂lam
        ≤ ∫⁻ _ in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q x0 ∂lam := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS'm] with X hX
          exact isMaxOn_iff.1 hmax X (hS'C hX)
      _ = rhoH P Q x0 * lam (cayF P Q ⁻¹' K ∩ D0 P Q) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 ENNReal.ofReal_ne_top)
          ((measure_mono hS'C).trans_lt hCc.measure_lt_top)

  have hne : betaH P Q lam (cayS (D0 P Q)) ≠ 0 := by
    rw [betaH_apply (P := P) (Q := Q) lam _ hW.measurableSet]
    have hpre : cayF P Q ⁻¹' cayS (D0 P Q) ∩ D0 P Q = D0 P Q :=
      Set.inter_eq_right.2 (fun X hX => ⟨X, hX, cayF_spec (P := P) (Q := Q) X hX⟩)
    rw [hpre]
    have hpos : 0 < lam (D0 P Q) := (isOpen_cell_domain (P := P) (Q := Q)).measure_pos lam ⟨0, h00⟩
    intro h0
    rw [lintegral_eq_zero_iff (measurable_rhoH (P := P) (Q := Q))] at h0
    have hF : ∀ᵐ x ∂(lam.restrict (D0 P Q)), False := by
      filter_upwards [h0, ae_restrict_mem (isOpen_cell_domain (P := P) (Q := Q)).measurableSet]
        with x hx hxD
      exact rhoH_pos (P := P) (Q := Q) x hxD hx
    rw [ae_iff] at hF
    simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ] at hF
    exact hpos.ne' hF
  obtain ⟨t, ht0, httop, W', hW'1, hW'W, hβW'⟩ :=
    local_haar_unique (UpqT P Q) m hm (betaH P Q lam) (cayS (D0 P Q)) hW h1W hinv hcpt hne
  obtain ⟨V, hVW', hVo, h1V⟩ := mem_nhds_iff.1 hW'1
  have hβV : (betaH P Q lam).restrict V = t • m.restrict V := by
    have h := congrArg (fun μ : Measure (UpqT P Q) => μ.restrict V) hβW'
    simp only [Measure.restrict_restrict_of_subset hVW', Measure.restrict_smul] at h
    exact h
  have key : ∀ S ⊆ V, betaH P Q lam S = t * m S := by
    intro S hSV
    have h := congrArg (fun μ : Measure (UpqT P Q) => μ S) hβV
    simp only [smul_apply, Measure.restrict_apply' hVo.measurableSet,
      Set.inter_eq_left.2 hSV, smul_eq_mul] at h
    exact h

  set D : Set (lieU P Q) := D0 P Q ∩ cayF P Q ⁻¹' V with hDdef
  have hDnhds : D ∈ 𝓝 (0 : lieU P Q) := by
    have hc : ContinuousAt (cayF P Q) 0 :=
      (continuousOn_cayF (P := P) (Q := Q)).continuousAt
        ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00)
    have hV0 : V ∈ 𝓝 (cayF P Q 0) := by
      rw [cayF_zero (P := P) (Q := Q)]
      exact hVo.mem_nhds h1V
    exact Filter.inter_mem ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00) (hc.preimage_mem_nhds hV0)
  have hDmeas : MeasurableSet D :=
    (isOpen_cell_domain (P := P) (Q := Q)).measurableSet.inter
      (measurable_cayF (P := P) (Q := Q) hVo.measurableSet)
  have hcayS : cayS D = cayS (D0 P Q) ∩ cayInv P Q ⁻¹' D := by
    ext g
    constructor
    · rintro ⟨X, hXD, hrel⟩
      refine ⟨⟨X, hXD.1, hrel⟩, ?_⟩
      show cayInv P Q g ∈ D
      rw [cayley_inverse_iff P Q g X hrel]
      exact hXD
    · rintro ⟨⟨X, -, hrel⟩, hgD⟩
      have hgX := cayley_inverse_iff P Q g X hrel
      refine ⟨X, ?_, hrel⟩
      rw [← hgX]
      exact hgD
  refine ⟨D, hDnhds, hDmeas, fun X => t⁻¹ * rhoH P Q X,
    (measurable_rhoH (P := P) (Q := Q)).const_mul _, ?_, ?_, ?_, ?_⟩
  · exact (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.2 ht0)).continuousAt.comp
      (continuousAt_rhoH (P := P) (Q := Q) 0 h00)
  · exact mul_ne_zero (ENNReal.inv_ne_zero.2 httop) (rhoH_pos (P := P) (Q := Q) 0 h00)
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ht0) ENNReal.ofReal_ne_top
  · ext A hA
    have hSV : cayInv P Q ⁻¹' A ∩ cayS D ⊆ V := by
      rintro g ⟨-, X, hXD, hrel⟩
      rw [← cayF_eq_of (P := P) (Q := Q) g X hrel]
      exact hXD.2
    have hSmeas : MeasurableSet (cayInv P Q ⁻¹' A ∩ cayS D) := by
      rw [hcayS]
      exact (cayley_inverse_measurable P Q hA).inter (hW.measurableSet.inter (cayley_inverse_measurable P Q hDmeas))
    have hpre : cayF P Q ⁻¹' (cayInv P Q ⁻¹' A ∩ cayS D) ∩ D0 P Q = A ∩ D := by
      ext X
      constructor
      · rintro ⟨⟨hXA, Y, hYD, hrel⟩, hX0⟩
        have h1 : cayInv P Q (cayF P Q X) = X := cayInv_cayF (P := P) (Q := Q) X hX0
        have h2 : cayInv P Q (cayF P Q X) = Y := cayley_inverse_iff P Q _ Y hrel
        have hXY : X = Y := h1.symm.trans h2
        refine ⟨?_, by rw [hXY]; exact hYD⟩
        have hA' : cayInv P Q (cayF P Q X) ∈ A := hXA
        rwa [h1] at hA'
      · rintro ⟨hXA, hXD⟩
        refine ⟨⟨?_, X, hXD, cayF_spec (P := P) (Q := Q) X hXD.1⟩, hXD.1⟩
        show cayInv P Q (cayF P Q X) ∈ A
        rw [cayInv_cayF (P := P) (Q := Q) X hXD.1]
        exact hXA
    have hβS : betaH P Q lam (cayInv P Q ⁻¹' A ∩ cayS D) = ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by
      rw [betaH_apply (P := P) (Q := Q) lam _ hSmeas, hpre]
    rw [Measure.map_apply (cayley_inverse_measurable P Q) hA, Measure.restrict_apply (cayley_inverse_measurable P Q hA),
      withDensity_apply _ hA, Measure.restrict_restrict hA]
    calc m (cayInv P Q ⁻¹' A ∩ cayS D)
        = t⁻¹ * (t * m (cayInv P Q ⁻¹' A ∩ cayS D)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
      _ = t⁻¹ * ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by rw [← key _ hSV, hβS]
      _ = ∫⁻ X in A ∩ D, t⁻¹ * rhoH P Q X ∂lam :=
          (lintegral_const_mul _ (measurable_rhoH (P := P) (Q := Q))).symm

end HcHDC
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped ENNReal

namespace CDX

section Perm

variable {n : ℕ} (ε : Fin n → Bool)

abbrev pP : ℕ := Fintype.card {i : Fin n // ε i = true}

abbrev pQ : ℕ := Fintype.card {i : Fin n // ¬ ε i = true}

def eS : Fin n ≃ Fin (pP ε) ⊕ Fin (pQ ε) :=
  (Equiv.sumCompl (fun i : Fin n => ε i = true)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem eS_symm_inl (a : Fin (pP ε)) : ε ((eS ε).symm (Sum.inl a)) = true := by
  unfold eS
  first
    | (simp; done)
    | (simp; exact ((Fintype.equivFin _).symm a).2)
    | exact ((Fintype.equivFin _).symm a).2

theorem eS_symm_inr (b : Fin (pQ ε)) : ε ((eS ε).symm (Sum.inr b)) = false := by
  unfold eS
  first
    | (simp; done)
    | (simpa using ((Fintype.equivFin _).symm b).2)
    | (simp; simpa using ((Fintype.equivFin _).symm b).2)

abbrev rA : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ :=
  reindexAlgEquiv ℂ ℂ (eS ε)

theorem rA_conj (M : Matrix (Fin n) (Fin n) ℂ) : (rA ε M)ᴴ = rA ε Mᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem rA_Jm : rA ε (Formalism.REAL.Jm ε) = HcS.UG.Jpq (pP ε) (pQ ε) := by
  ext i j
  simp only [rA, reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.REAL.Jm, HcS.UG.Jpq,
    Matrix.diagonal_apply, (eS ε).symm.injective.eq_iff]
  rcases i with a | a <;> rcases j with b | b
  · by_cases h : a = b <;> simp [h, eS_symm_inl, Matrix.one_apply]
  · simp
  · simp
  · by_cases h : a = b <;> simp [h, eS_symm_inr, Matrix.one_apply]

theorem rA_mem_iff (M : Matrix (Fin n) (Fin n) ℂ) :
    (rA ε M)ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) * rA ε M = HcS.UG.Jpq (pP ε) (pQ ε) ↔ Formalism.REAL.inUJ ε M := by
  rw [rA_conj, ← rA_Jm, ← map_mul, ← map_mul, (rA ε).injective.eq_iff]
  rfl

theorem rA_skew_iff (M : Matrix (Fin n) (Fin n) ℂ) :
    (rA ε M)ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) + HcS.UG.Jpq (pP ε) (pQ ε) * rA ε M = 0 ↔
      Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 := by
  rw [rA_conj, ← rA_Jm, ← map_mul, ← map_mul, ← map_add (f := _), ← map_zero (rA ε), (rA ε).injective.eq_iff]

theorem continuous_rA : Continuous (rA ε) := by
  exact LinearMap.continuous_of_finiteDimensional (rA ε).toLinearMap

theorem continuous_rA_symm : Continuous (rA ε).symm := by
  exact LinearMap.continuous_of_finiteDimensional (rA ε).symm.toLinearMap

def rM : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ where
  toFun := rA ε
  map_one' := map_one _
  map_mul' := map_mul _

def rMs : Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun := (rA ε).symm
  map_one' := map_one _
  map_mul' := map_mul _

def phiF (g : Formalism.REAL.UJ ε) : HcS.BasicNotions.UpqT (pP ε) (pQ ε) :=
  ((⟨Units.map (rM ε) g.1, by
      rw [HcInf.mem_Upq_iff]; exact (rA_mem_iff ε _).2 g.2⟩ : HcS.UG.Upq (pP ε) (pQ ε)) :
        HcS.BasicNotions.UpqT (pP ε) (pQ ε))

theorem phiB_mem (h : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) :
    Formalism.REAL.inUJ ε ((rA ε).symm (HcS.BasicNotions.UpqT.mat h)) := by
  rw [← rA_mem_iff, AlgEquiv.apply_symm_apply]
  exact (HcInf.mem_Upq_iff _ _ _).1 (h : HcS.UG.Upq (pP ε) (pQ ε)).2

def phiB (h : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) : Formalism.REAL.UJ ε :=
  ⟨Units.map (rMs ε) (HcInf.toS _ _ h).1, phiB_mem ε h⟩

theorem phiF_mat (g : Formalism.REAL.UJ ε) :
    HcS.BasicNotions.UpqT.mat (phiF ε g) = rA ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem phiB_val (h : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) :
    (((phiB ε h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      (rA ε).symm (HcS.BasicNotions.UpqT.mat h) := rfl

theorem mat_mul' (a b : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) :
    HcS.BasicNotions.UpqT.mat (a * b) = HcS.BasicNotions.UpqT.mat a * HcS.BasicNotions.UpqT.mat b := rfl

def phiU : Formalism.REAL.UJ ε ≃* HcS.BasicNotions.UpqT (pP ε) (pQ ε) where
  toFun := phiF ε
  invFun := phiB ε
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    rw [phiB_val, phiF_mat]
    exact (rA ε).symm_apply_apply _
  right_inv h := by
    apply (HcInf.isClosedEmbedding_mat _ _).injective
    rw [phiF_mat, phiB_val]
    exact (rA ε).apply_symm_apply _
  map_mul' a b := by
    apply (HcInf.isClosedEmbedding_mat _ _).injective
    rw [mat_mul', phiF_mat, phiF_mat, phiF_mat, Subgroup.coe_mul, Units.val_mul]
    exact map_mul (rA ε) _ _

theorem continuous_phiF : Continuous (phiF ε) := by
  first
  | exact (HcInf.isClosedEmbedding_mat _ _).isInducing.continuous_iff.mpr
      ((continuous_rA ε).comp (Units.continuous_val.comp continuous_subtype_val))
  | exact (HcInf.isClosedEmbedding_mat _ _).toIsInducing.continuous_iff.mpr
      ((continuous_rA ε).comp (Units.continuous_val.comp continuous_subtype_val))

theorem continuous_toS : Continuous fun h : HcS.BasicNotions.UpqT (pP ε) (pQ ε) =>
    ((HcInf.toS _ _ h : HcS.UG.Upq (pP ε) (pQ ε)) : GL (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ) :=
  continuous_subtype_val

theorem continuous_phiB : Continuous (phiB ε) :=
  ((Continuous.units_map (rMs ε) (continuous_rA_symm ε)).comp (continuous_toS ε)).subtype_mk _

def phiC : Formalism.REAL.UJ ε ≃ₜ* HcS.BasicNotions.UpqT (pP ε) (pQ ε) where
  toMulEquiv := phiU ε
  continuous_toFun := continuous_phiF ε
  continuous_invFun := continuous_phiB ε

def psiL : gLie ε →ₗ[ℝ] HcS.BasicNotions.lieU (pP ε) (pQ ε) where
  toFun x := ⟨rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))), by
    show (rA ε _)ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) + HcS.UG.Jpq (pP ε) (pQ ε) * rA ε _ = 0
    rw [rA_skew_iff]
    exact lieSkew_holds n ε _ x.2⟩
  map_add' x y := by
    apply Subtype.ext
    show rA ε (unrLin n ((x + y : gLie ε) : EuclideanSpace ℝ _)) = rA ε (unrLin n x) + rA ε (unrLin n y)
    rw [Submodule.coe_add, map_add (f := _), map_add (f := _)]
  map_smul' c x := by
    apply Subtype.ext
    ext i j
    apply Complex.ext <;> simp [unrealify]

theorem psiL_val (x : gLie ε) :
    (psiL ε x).1 =
      rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := rfl

theorem psiL_bij : Function.Bijective (psiL ε) := by
  constructor
  · intro x y hxy
    have h1 : rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        rA ε (unrealify (y : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := by
      rw [← psiL_val, ← psiL_val, hxy]
    have h2 := (rA ε).injective h1
    apply Subtype.ext
    rw [← re_unr n (x : EuclideanSpace ℝ _), ← re_unr n (y : EuclideanSpace ℝ _)]
    exact congrArg (reLin n) h2
  · intro Y
    set X := (rA ε).symm Y.1 with hX
    have hY : Y.1ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) + HcS.UG.Jpq (pP ε) (pQ ε) * Y.1 = 0 :=
      Y.2
    have hsk : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := by
      rw [← rA_skew_iff, hX, AlgEquiv.apply_symm_apply]; exact hY
    refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun X), skewLie_holds n ε X hsk⟩, ?_⟩
    apply Subtype.ext
    rw [psiL_val]
    show rA ε (unrealify ((WithLp.equiv 2 _).symm (realifyFun X))) = _
    rw [unr_re, hX, AlgEquiv.apply_symm_apply]

def psiC : gLie ε ≃L[ℝ] HcS.BasicNotions.lieU (pP ε) (pQ ε) :=
  (LinearEquiv.ofBijective (psiL ε) (psiL_bij ε)).toContinuousLinearEquiv

theorem psiC_val (x : gLie ε) :
    (psiC ε x).1 =
      rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := rfl

theorem rel_iff (g : Formalism.REAL.UJ ε) (x : gLie ε) :
    HcS.BasicNotions.UpqT.mat (phiC ε g) * ((1 + 1) - (psiC ε x).1) =
        (1 + 1) + (psiC ε x).1 ↔
      (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) *
          (2 - unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        2 + unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := by
  have e1 : HcS.BasicNotions.UpqT.mat (phiC ε g) = rA ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) :=
    phiF_mat ε g
  rw [e1, psiC_val, one_add_one_eq_two, ← map_ofNat (rA ε) 2, ← map_sub, ← map_mul, ← map_add (f := _),
    (rA ε).injective.eq_iff]

theorem isUnit_of_mem_cayley_domain (x : gLie ε) (hx : psiC ε x ∈ HcInf.D0 (pP ε) (pQ ε)) :
    IsUnit (2 - unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))).det := by
  have h : IsUnit ((1 + 1) - ((psiC ε x : HcS.BasicNotions.lieU (pP ε) (pQ ε)) :
      Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ)).det := hx
  rw [psiC_val] at h
  have e : (1 + 1 : Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ) -
      rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
      rA ε (2 - unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := by
    rw [map_sub, map_ofNat, one_add_one_eq_two]
  rw [e] at h
  simpa [Matrix.det_reindex_self] using h

theorem cayR_eq (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) (g : Formalism.REAL.UJ ε)
    (h : (2 + unrealify x) * (2 - unrealify x)⁻¹ = (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ)) :
    cayR ε x = g := by
  have hc : IsUnit ((2 + unrealify x) * (2 - unrealify x)⁻¹) ∧
      Formalism.REAL.inUJ ε ((2 + unrealify x) * (2 - unrealify x)⁻¹) := by
    rw [h]; exact ⟨(g : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit, g.2⟩
  unfold cayR
  rw [dite_eq_left hc]
  apply Subtype.ext; apply Units.ext
  rw [IsUnit.unit_spec]; exact h

theorem cay_mat (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hu : IsUnit (2 - unrealify x).det) (h : M * (2 - unrealify x) = 2 + unrealify x) :
    (2 + unrealify x) * (2 - unrealify x)⁻¹ = M := by
  rw [← h, Matrix.mul_nonsing_inv_cancel_right _ _ hu]

end Perm

end CDX


open CDX in
theorem cayDensEx_holds : CayDensEx := by
  intro n ε
  classical
  set φ := phiC ε with hφ
  set ψ := psiC ε with hψ
  set φM := φ.toHomeomorph.toMeasurableEquiv with hφM
  set ψM := ψ.toHomeomorph.toMeasurableEquiv with hψM
  set m : Measure (HcS.BasicNotions.UpqT (pP ε) (pQ ε)) := (Formalism.REAL.muG ε).map φM with hm
  have hmHaar : m.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (Formalism.REAL.muG ε) φ
  set lam : Measure (HcS.BasicNotions.lieU (pP ε) (pQ ε)) := (volume : Measure (gLie ε)).map ψM with hlam
  have hlamHaar : lam.IsAddHaarMeasure := ψ.isAddHaarMeasure_map volume
  have hDensity := @HcHDC.cayDensU (pP ε) (pQ ε) m hmHaar lam hlamHaar
  obtain ⟨D, hD, -, f, hfm, hfc, -, hfT, hmap⟩ := hDensity
  have hψ0 : ψ 0 = 0 := map_zero ψ
  have hψc : ContinuousAt ψ 0 := ψ.continuous.continuousAt
  have hN1 : ψ ⁻¹' D ∈ 𝓝 (0 : gLie ε) := hψc.preimage_mem_nhds (by rw [hψ0]; exact hD)
  have hN2 : ψ ⁻¹' HcInf.D0 (pP ε) (pQ ε) ∈ 𝓝 (0 : gLie ε) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact HcInf.isOpen_cell_domain.mem_nhds HcInf.zero_mem_cayley_domain)
  have hN3 : ψ ⁻¹' {X | f X ≠ ⊤} ∈ 𝓝 (0 : gLie ε) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact hfc.eventually_ne hfT)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hN1 hN2) hN3)
  refine ⟨r₀, hr₀, fun x => (f (ψ x)).toReal, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_toReal.comp (hfm.comp ψ.continuous.measurable)
  · have h1 : ContinuousAt (fun x => f (ψ x)) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hψ0]; exact hfc) hψc
    have h2 : ContinuousAt ENNReal.toReal (f (ψ 0)) := ENNReal.continuousAt_toReal (by rw [hψ0]; exact hfT)
    exact ContinuousAt.comp (f := fun x => f (ψ x)) (x := 0) h2 h1
  · intro S hS hSm
    have hpt : ∀ x ∈ S, ψ x ∈ D ∧ ψ x ∈ HcInf.D0 (pP ε) (pQ ε) ∧ f (ψ x) ≠ ⊤ := fun x hx =>
      ⟨(hball (hS hx)).1.1, (hball (hS hx)).1.2, (hball (hS hx)).2⟩
    set T := ψM '' S with hTdef
    have hT : MeasurableSet T := ψM.measurableSet_image.2 hSm
    have hTD : T ⊆ D := by rintro _ ⟨x, hx, rfl⟩; exact (hpt x hx).1

    have hset : φM ⁻¹' HcInf.cayS T =
        (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S := by
      ext g
      constructor
      · rintro ⟨X, ⟨x, hx, rfl⟩, hgX⟩
        refine ⟨x, hx, ?_⟩
        have hu := isUnit_of_mem_cayley_domain ε x (hpt x hx).2.1
        exact cayR_eq ε _ g (cay_mat _ _ hu ((rel_iff ε g x).1 hgX))
      · rintro ⟨x, hx, rfl⟩
        have hD0 := (hpt x hx).2.1
        have hu := isUnit_of_mem_cayley_domain ε x hD0
        set h := HcInf.cayF (pP ε) (pQ ε) (ψ x) with hh
        have hs := HcInf.cayF_spec (ψ x) hD0
        have hrel := (rel_iff ε (φ.symm h) x).1 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hs)
        have hc : cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = φ.symm h :=
          cayR_eq ε _ _ (cay_mat _ _ hu hrel)
        refine ⟨ψ x, ⟨x, hx, rfl⟩, ?_⟩
        show HcS.BasicNotions.UpqT.mat (φ (cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) * _ = _
        rw [hc, ContinuousMulEquiv.apply_symm_apply]
        exact hs
    have hsetD : HcInf.cayInv (pP ε) (pQ ε) ⁻¹' T ∩ HcInf.cayS D = HcInf.cayS T := by
      ext g
      constructor
      · rintro ⟨hgT, X, hXD, hgX⟩
        have e := HcInf.cayley_inverse_iff _ _ g X hgX
        exact ⟨X, e ▸ hgT, hgX⟩
      · rintro ⟨X, hXT, hgX⟩
        have e := HcInf.cayley_inverse_iff _ _ g X hgX
        exact ⟨show HcInf.cayInv _ _ g ∈ T from e ▸ hXT, X, hTD hXT, hgX⟩
    have hmeasT := HcInf.cayley_inverse_measurable (pP ε) (pQ ε) hT
    calc Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S)
        = m (HcInf.cayS T) := by rw [hm, MeasurableEquiv.map_apply, hset]
      _ = ((m.restrict (HcInf.cayS D)).map (HcInf.cayInv (pP ε) (pQ ε))) T := by
          rw [Measure.map_apply (HcInf.cayley_inverse_measurable _ _) hT, Measure.restrict_apply hmeasT, hsetD]
      _ = ∫⁻ X in T, f X ∂lam := by
          rw [hmap, withDensity_apply _ hT, Measure.restrict_restrict hT, Set.inter_eq_left.2 hTD]
      _ = ∫⁻ x in S, f (ψ x) := by
          rw [hlam, MeasurableEquiv.restrict_map, hTdef, MeasurableEquiv.preimage_image, lintegral_map_equiv]
          rfl
      _ = ∫⁻ x in S, ENNReal.ofReal ((f (ψ x)).toReal) := by
          refine setLIntegral_congr_fun hSm (fun x hx => ?_)
          exact (ENNReal.ofReal_toReal (hpt x hx).2.2).symm

end PI.AprimeInfW

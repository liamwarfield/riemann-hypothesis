module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyConvClose

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FinOfWeil
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG
open scoped InnerProductSpace ENNReal Pointwise

namespace Formalism.L2.SG.RealObj.EnergyConvJ

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem fin_of_weil (μ μS ν : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : μ ≠ 0)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν) :
    IsFiniteMeasureOnCompacts μS := by
  refine ⟨fun K hK => ?_⟩
  have hν : ν ≠ 0 := by
    rintro rfl
    apply hμ
    have := hW (fun _ => 1) measurable_const
    simpa using this
  obtain ⟨C, hC, hνC⟩ : ∃ C : Set G, IsCompact C ∧ ν C ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hν
    have : ν Set.univ = 0 := by
      rw [← iUnion_compactCovering G]
      exact measure_iUnion_null fun n => hcon _ (isCompact_compactCovering G n)
    exact Measure.measure_univ_eq_zero.mp this
  have hWc : IsCompact (K * C) := hK.mul hC
  have hWm : MeasurableSet (K * C) := hWc.isClosed.measurableSet
  have hf := hW ((K * C).indicator 1) (measurable_one.indicator hWm)
  rw [lintegral_indicator_one hWm] at hf
  have hinner : ∀ x, ∫⁻ s, (K * C).indicator 1 (s * x) ∂μS = μS ((· * x) ⁻¹' (K * C)) := fun x => by
    rw [← lintegral_indicator_one ((measurable_mul_const x) hWm)]
    rfl
  simp_rw [hinner] at hf
  have hbound : μS K * ν C ≤ μ (K * C) := by
    rw [hf, ← lintegral_indicator_const hC.isClosed.measurableSet]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      exact measure_mono fun k hk => Set.mul_mem_mul hk hx
    · simp [hx]
  have hμW : μ (K * C) < ⊤ := hWc.measure_lt_top
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.top_mul hνC] at hbound
  exact absurd (lt_of_le_of_lt hbound hμW) (lt_irrefl _)

end Gen

variable {D : D7}

theorem sloc_sub_NH (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {x : Formalism.REAL.UJ (X.B.I.ε v)}
    (hx : x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v) : x ∈ Formalism.L2.SG.Pf.WuDec.NHloc X u v := by
  classical
  set s : X.B.I.Ginf := Function.update 1 v x with hsdef
  have hs : s ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hsdef, Function.update_self]
      exact hx
    · rw [hsdef, Function.update_of_ne hw]
      exact Formalism.L2.SG.Pf.WuDec.one_mem_Sloc X u w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdec⟩ := Formalism.L2.S.Pv.HaarSubS.sDecomp_holds D X u
  obtain ⟨n, hn, h, hh, he⟩ := hdec s hs
  have hxv : x = n v * h v := by
    have := congrFun he v
    rw [hsdef, Function.update_self] at this
    exact this
  exact ⟨n v, hn v, h v, hh v, hxv⟩

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG
open scoped InnerProductSpace ENNReal Pointwise

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7}


set_option maxHeartbeats 800000 in
variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem locQuad1_G_holds (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) : LocQuad1_G := by
  intro D hG X w μSl νl C hQ v
  obtain ⟨τ, hτ⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  subst hτ
  obtain ⟨μS, ν, hloc, -⟩ := Formalism.L2.SG.RealObj.EnergyFinal.weilPairJ_holds hI hG X τ
  obtain ⟨sS, sν, hWe, hinv, h0, h3, hli, hne⟩ := hloc w
  obtain ⟨hC0, hCt, hlocl, -⟩ := hQ
  obtain ⟨⟨hsfl, hnel, hconcl, hlil⟩, hWl⟩ := hlocl (vOf X τ)

  have hU := Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds (vOf X τ)).2.2.1
  have e1 := triple_lintegral_eq (μ := Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (μS := μS w) (ν := ν w)
    (S := Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ)) hU (X.B.w (vOf X τ)) (X.Wloc_cont w (vOf X τ)) hWe h0
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X w (vOf X τ) hs x)
  beta_reduce at e1
  have hJ : ∫⁻ a, Kv X w (vOf X τ) a ∂(ν w) < ⊤ := by
    have e2 : ∫⁻ a, Kv X w (vOf X τ) a ∂(ν w) = ∫⁻ z, ‖X.Wloc w (vOf X τ) z‖ₑ *
        ∫⁻ y, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat y) (X.B.w (vOf X τ))⟫_ℂ‖ₑ *
          ‖X.Wloc w (vOf X τ) y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) ∂(ν w) := rfl
    rw [e2, ← e1]
    exact h3

  set S : Subgroup (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :=
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a))
      (rv X.B.I (vOf X τ) (X.zR w)) with hSdef
  have hSc : IsClosed (S : Set (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG_closed _ _ _
  have hSset : (S : Set (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) = Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ) := rfl
  have hNHsub : ∀ x, x ∈ Formalism.L2.SG.Pf.WuDec.NHloc X w (vOf X τ) → x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ) := by
    rintro x ⟨m, hm, h, hh, rfl⟩
    exact Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X w _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X w _ hm)
      (Formalism.L2.SG.Pf.WuDec.Hloc_sub X w _ hh)
  have hG0 : Formalism.REAL.muG (X.B.I.ε (vOf X τ)) ≠ 0 := NeZero.ne _
  have hfc : IsFiniteMeasureOnCompacts (μS w) := fin_of_weil _ (μS w) (ν w) hG0 hWe
  obtain ⟨c, hc0, hct, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC.unique_sf S hSc (μS w) (μSl (vOf X τ)) hne
    (by rw [hSset]; exact h0) (fun s hs => hli s hs) hfc hnel hsfl
    (by rw [hSset]; exact measure_mono_null (show (Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ))ᶜ ⊆ (Formalism.L2.SG.Pf.WuDec.NHloc X w (vOf X τ))ᶜ from fun x hx h' => hx (hNHsub x h')) hconcl)
    (fun s hs => hlil s (sloc_sub_NH X w _ hs))

  have hsub : MeasurableEmbedding (Subtype.val : S → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :=
    MeasurableEmbedding.subtype_coe hSc.measurableSet
  obtain ⟨hli', hmap⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC.comap_inv S hSc (μS w) (by rw [hSset]; exact h0)
    (fun s hs => hli s hs)
  set μS' : Measure S := (μS w).comap Subtype.val with hμS'
  have : LocallyCompactSpace S := hSc.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace S := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : IsFiniteMeasureOnCompacts μS' := ⟨fun K hK => by
    rw [hμS', hsub.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  have hne' : μS' ≠ 0 := by
    intro h00
    apply hne
    rw [← hmap, h00, Measure.map_zero]
  have hinv2 : (μS w).map Inv.inv = μS w := hinv
  have e : μS'.inv.map Subtype.val = μS'.map Subtype.val := by
    rw [Measure.inv, Measure.map_map hsub.measurable measurable_inv,
      show (Subtype.val ∘ (Inv.inv : S → S)) = (Inv.inv : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → _) ∘ Subtype.val from rfl,
      ← Measure.map_map measurable_inv hsub.measurable, hmap, hinv2]
  have hinv' : μS'.inv = μS' := by
    rw [← hsub.comap_map μS'.inv, e, hsub.comap_map]
  have : μS'.IsInvInvariant := ⟨hinv'⟩
  have : μS'.IsMulRightInvariant := by
    have h := (inferInstance : μS'.inv.IsMulRightInvariant)
    rwa [hinv'] at h
  have : μS'.IsOpenPosMeasure := by
    obtain ⟨K, hK, hK0⟩ : ∃ K : Set S, IsCompact K ∧ μS' K ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hne'
      have : μS' Set.univ = 0 := by
        rw [← iUnion_compactCovering S]
        exact measure_iUnion_null fun n => hc _ (isCompact_compactCovering S n)
      exact Measure.measure_univ_eq_zero.mp this
    exact isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK hK0
  have hlint : ∀ (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))),
      ∫⁻ s, f (s * x) ∂(μS w) = ∫⁻ s : S, f ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) ∂μS' := by
    intro f x
    conv_lhs => rw [← hmap]
    rw [hsub.lintegral_map]
  have hW1 : ∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        ∫⁻ x, ∫⁻ s : S, f ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) ∂μS' ∂(ν w) := by
    intro f hf
    rw [hWe f hf]
    exact lintegral_congr fun x => hlint f x
  have hμl : μSl (vOf X τ) = c⁻¹ • μS w := by
    rw [hceq, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  have hci : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hW2 : ∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        ∫⁻ x, ∫⁻ s : S, f ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) ∂μS' ∂(c⁻¹ • νl (vOf X τ)) := by
    intro f hf
    rw [hWl f hf, lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul' _ _ hci]
    refine lintegral_congr fun x => ?_
    rw [hμl, lintegral_smul_measure, smul_eq_mul, hlint f x]
  have hKinv : ∀ (s : S) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))),
      Kv X w (vOf X τ) ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) = Kv X w (vOf X τ) x := by
    intro s x
    obtain ⟨m, hm, h, hh, he⟩ := sloc_sub_NH X w _ s.2
    rw [he]
    exact Kv_inv X w (vOf X τ) m hm h hh x
  have hind := Formalism.L2.SG.Pf.QuotIndep.quotIndep (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) S hSc μS'
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (ν w) (c⁻¹ • νl (vOf X τ)) hW1 hW2 (Kv X w (vOf X τ))
    (measurable_Kv X w (vOf X τ)) hKinv
  rw [lintegral_smul_measure, smul_eq_mul] at hind
  have hfinal : ∫⁻ a, Kv X w (vOf X τ) a ∂(νl (vOf X τ)) = c * ∫⁻ a, Kv X w (vOf X τ) a ∂(ν w) := by
    rw [hind, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
  rw [hfinal]
  exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hct) hJ


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem stepConvG_holds (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) : StepConvG :=
  stepConvG_of (locQuadGG_G_holds hI) (locQuad1_G_holds hI)

end Formalism.L2.SG.RealObj.EnergyConvJ

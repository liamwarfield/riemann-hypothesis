module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdmC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHL
noncomputable section

namespace PI.VolStabS

namespace LatFactsW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem smul_mem_latSub {a M : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {x : Fin a → Fin M → Fv F v ⊗[F] E} (hx : x ∈ latSub b v a M) : s • x ∈ latSub b v a M := by
  have hx' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k ∈
      v.adicCompletionIntegers F := hx
  show ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((s • x) i j) k ∈
      v.adicCompletionIntegers F
  intro i j k
  simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hs (hx' i j k)

theorem isOpen_hermO (σ : E →ₐ[F] E) (a : ℕ) : IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) :=
  continuous_subtype_val.isOpen_preimage _ (PositiveNearLattice.isClopen_latV b v a a).isOpen

theorem isCompact_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage
    (PositiveNearLattice.isCompact_latV b v a a)

instance contSMul_herm (σ : E →ₐ[F] E) (a : ℕ) : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
    p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

end LatFactsW

open scoped TensorProduct
open NumberField IsDedekindDomain Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW LatFactsW

theorem latFacts_holds : LatFacts := by
  intro F E _ _ _ _ _ σ d b a M v
  obtain ⟨h0, hπ, hint⟩ := unifV_spec v
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun n => ?_, fun n => ?_, ?_⟩
  · exact isOpen_smulSub _ (pow_ne_zero _ h0) _ (PositiveNearLattice.isClopen_latV b v a M).isOpen
  · exact isCompact_smulSub _ _ (PositiveNearLattice.isCompact_latV b v a M)
  · intro m n hmn x hx
    simp only [lamF, mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨unifV v ^ (n - m) • p, smul_mem_latSub b v (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  · intro x hx
    simp only [lamF, mem_smulSub] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact smul_mem_latSub b v (pow_mem hint _) hp
  · exact isOpen_smulSub _ (pow_ne_zero _ h0) _ (isOpen_hermO b v σ a)
  · exact isCompact_smulSub _ _ (isCompact_hermO b v σ a)
  · intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (hermO b v σ a : Set (HermR (Fv F v) σ a))
      (isCompact_hermO b v σ a) (fun k => unifV v ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN
    refine ⟨k, ?_⟩
    simp only [hF, coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdm
noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabS
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

theorem detAdm_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH (F := F) (E := E) (a := a) (M := M)
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (by exact fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU

end PI.VolStabS.DeterminantAdmissible

namespace PI.VolStabS

theorem detAdm_holds : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocPosV
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

theorem locPos_holds : LocPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).2 v
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let b := Module.finBasis F E
  set X1 := ratTup (F := F) (Fv F v) X0 with hX1
  set T := hermOf (Fv F v) σ (gramE σ J X0) hT with hTdef
  have hgT : gramH (Fv F v) σ hσ J hJ.1 X1 = T := Subtype.ext (gramR_ratTup (Fv F v) σ J X0)
  have hX1U : LinearIndependent (Fv F v ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Fv F v) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  obtain ⟨N, hN, hd⟩ := gramFilt_of (dxOpen_of secGram_holds) F E σ hσ M J hJ.1 hJ.2 a ha1 (by omega) v
    _ b X1 hX1U
  obtain ⟨Λ0, hB, hΛ0o, hΛ0c, hsub⟩ := isCOBasis_latSub b v a M N hN
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ :=
    hd X1 (by rw [sub_self]; exact mem_of_mem_nhds hN) Λ0 hB hsub
  let Nb : Set (HermR (Fv F v) σ a) :=
    {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
  have hNb : Nb ∈ 𝓝 T :=
    (isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a).mem_nhds
      (isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  have hval := fibCos μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (continuous_gramH (Fv F v) σ hσ J hJ.1) (fun _ => rfl)
    _ Set.univ fibV hfib T Filter.univ_mem Nb hNb
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) Λ H hΛo hΛc hΛa hHo hHc hHb D hD X1
    hyp (by rw [hgT, sub_self]; exact zero_mem _)
  have hΛ0pos : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ 0 :=
    ((hΛo 0).measure_pos μv ⟨0, zero_mem _⟩).ne'
  have hΛ0fin : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ ⊤ :=
    ((hΛc 0).measure_lt_top).ne
  have hH0pos : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ 0 :=
    ((hHo 0).measure_pos νv ⟨0, zero_mem _⟩).ne'
  have hH0fin : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ ⊤ := ((hHc 0).measure_lt_top).ne
  have hQo : IsOpen {x | x - X1 ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - X1 ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - X1 ∈ Λ 0} := by
    have e : {x | x - X1 ∈ Λ 0} = (fun w => w + X1) '' (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - X1, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [e]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  refine ⟨{x | x - X1 ∈ Λ 0}.indicator 1, ⟨(LocallyConstant.indicator
    (LocallyConstant.const _ (1 : ℂ)) ⟨hQcl, hQo⟩).isLocallyConstant,
    HasCompactSupport.intro' hQc hQcl fun Y hY => Set.indicator_of_notMem hY _⟩, ?_⟩
  rw [hval]
  have hr : 0 < (μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) /
      νv (H 0 : Set (HermR (Fv F v) σ a))).toReal :=
    ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨hΛ0pos, hH0fin⟩).ne'
      (ENNReal.div_ne_top hΛ0fin hH0pos)
  exact_mod_cast hr.ne'

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ArchPosHolds
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

theorem lbInf_of (hC : CoordInf) (hS : SubmLB) : LBInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ hν W hWo hXW
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  set T := hermOf (Ainf F) σ (gramE σ J X0) hT with hTdef
  have hX1U : LinearIndependent (Ainf F ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  have hW' : IsOpen (eV.symm ⁻¹' W) := hWo.preimage eV.symm.continuous
  have hx0W : eV X1 ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV X1) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hXW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    hS n m _ _ hμ' hν' f' hf' (eV X1) (hsurj X1 hX1U) _ hW' hx0W
  have hfx0 : f' (eV X1) = eH T := by
    have h1 : eH.symm (f' (eV X1)) = T := Subtype.ext ((hG X1).trans (gramR_ratTup (Ainf F) σ J X0))
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 T := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (νinf.map eH) = νinf.map eH.toMeasurableEquiv from rfl,
    show (μinf.map eV) = μinf.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

theorem lbInf_holds : LBInf :=
  lbInf_of (coordInf_of quadCoord_holds tensR_holds (freeSurj_of semisimpleTens_holds))
    submLB_holds

theorem archPos_holds : ArchPos := archPos_of_lb lbInf_holds

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMuInv
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoFibInv
noncomputable section

namespace PI.VolStabS.TopoFibInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X]

theorem isFibreFamily_map (e : V ≃ₜ V) {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν B fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hf : ∀ x, f (e x) = f x) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν B (fun b => (fib b).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι b ∧ x ∈ U)
      rw [hf x, hx]
    rw [this]
    exact hfib.1 b
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    refine lintegral_congr fun b => ?_
    exact (lintegral_map_equiv _ _).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b hb => (integrable_map_equiv em φ).2 (h1 b hb), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib b).map em)) = fun b => ∫ x, (φ ∘ e) x ∂(fib b) :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    exact h2

end Abstract

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gramR_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (h • X) = gramR R σ J X := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  funext x y
  change hR R σ J (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR R σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

theorem linIndep_mulVec {A : Type} [CommRing A] (G : GL (Fin M) A) (X : Fin a → Fin M → A) :
    LinearIndependent A (fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) ↔ LinearIndependent A X := by
  have inj : ∀ H : GL (Fin M) A, LinearMap.ker (mulVecLin (H : Matrix (Fin M) (Fin M) A)) = ⊥ :=
    fun H => by
      refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
      have := congrArg (fun z => ((H⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ z) hxy
      simpa [mulVecLin_apply, mulVec_mulVec] using this
  constructor
  · intro hl
    have h2 := hl.map' (mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) (inj G⁻¹)
    have e : (⇑(mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) ∘
        fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) = X := by
      funext x
      simp [mulVec_mulVec]
    rw [e] at h2
    exact h2
  · intro hl
    exact hl.map' (mulVecLin (G : Matrix (Fin M) (Fin M) A)) (inj G)

theorem linIndep_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) (h • X) ↔ LinearIndependent (R ⊗[F] E) X :=
  linIndep_mulVec (HA.mat R σ J h) X

end Loc

end PI.VolStabS.TopoFibInv

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MuInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ h : HA (Ainf F) σ J, μinf.map (fun X => h • X) = μinf

def MuInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ h : HA (Fv F v) σ J, μv.map (fun X => h • X) = μv

theorem fibInvInf_of (hP : FibPin) (hM : MuInvInf) : FibInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfi h Φinf
    hcΦ hcs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Ainf F) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfi
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h)
    (fun x => TopoFibInv.gramR_smul (Ainf F) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Ainf F) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 μinf hμ νinf hν _ _ hfam hfi Φinf
    hcΦ hcs
  rw [integral_map_equiv] at this
  exact this

theorem fibInvV_of (hP : FibPin) (hM : MuInvV) : FibInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfv h Φv hSB
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Fv F v) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfv
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h)
    (fun x => TopoFibInv.gramR_smul (Fv F v) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Fv F v) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2 v μv hμ νv hν _ _ hfam hfv Φv hSB
  rw [integral_map_equiv] at this
  exact this

theorem nuInv_of_steps (hD : DetAdm) (hC : CompG) (hP : FibPin) (hMI : MuInvInf) (hMV : MuInvV) :
    NuInv :=
  nuInv_of_loc gramPres_holds (pullLoc_of hC (fibInvInf_of hP hMI) (fibInvV_of hP hMV)) hD

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem smul_apply (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (x : Fin n) :
    (h • X) x = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ X x :=
  rfl

theorem BR_smul (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by
  have hg' : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  simp only [BR, smul_apply, hR, TopoGram.hform_mulVec, hg']

theorem BR_smul_left (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) Y = BR R σ J X (h⁻¹ • Y) := by
  conv_lhs => rw [← smul_inv_smul h Y]
  exact BR_smul R σ J h X (h⁻¹ • Y)

theorem smul_neg' (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by
  funext x
  simp only [smul_apply, Pi.neg_apply, mulVec_neg]

def smulAddEquiv (h : HA R σ J) (n : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  map_add' X Y := by
    funext x
    change ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (X x + Y x) = _
    rw [mulVec_add]
    rfl

theorem selfDual_map (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabS.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]

end PI.VolStabS.TopoMuInv

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem muInvInf_of (hU : SdUniq) : MuInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) σ J (psiInf F ψ) μinf hμ h) hμ

theorem muInvV_of (hU : SdUniq) : MuInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ((hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) σ J (psiV F ψ v) μv hμ h) hμ

theorem nuInv_of_pin (hD : DetAdm) (hC : CompG) (hP : FibPin) (hU : SdUniq) : NuInv :=
  nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)

end PI.VolStabS
end
end

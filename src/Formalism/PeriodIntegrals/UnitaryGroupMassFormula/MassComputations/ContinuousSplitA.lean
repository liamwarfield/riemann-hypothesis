module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA
noncomputable section

namespace MassDataMassesW

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.BasicNotions

theorem continuous_splitA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (splitA σ J) := by
  unfold splitA
  rw [MonoidHom.coe_prod]
  refine Continuous.prodMk ?_ ?_
  · have hφ : Continuous (tensMap (E := E) (fstA F)) := by
      have hsm : ∀ (a : AF F) (x : TensorProduct F (AF F) E),
          tensMap (E := E) (fstA F) (a • x) = (fstA F a) • tensMap (E := E) (fstA F) x := by
        intro a x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      have hc : Continuous (fstA F : AF F → Ainf F) := continuous_fst
      haveI : IsModuleTopology (AF F) (TensorProduct F (AF F) E) := ⟨rfl⟩
      haveI : IsModuleTopology (Ainf F) (TensorProduct F (Ainf F) E) := ⟨rfl⟩
      have key : Continuous (fun p : AF F × TensorProduct F (Ainf F) E => (fstA F p.1) • p.2) :=
        continuous_smul.comp ((hc.comp continuous_fst).prodMk continuous_snd)
      letI : Module (AF F) (TensorProduct F (Ainf F) E) :=
        Module.compHom _ (fstA F).toRingHom
      haveI : ContinuousSMul (AF F) (TensorProduct F (Ainf F) E) := ⟨key⟩
      let f : TensorProduct F (AF F) E →ₗ[AF F] TensorProduct F (Ainf F) E :=
        { toFun := tensMap (E := E) (fstA F)
          map_add' := map_add _
          map_smul' := hsm }
      exact IsModuleTopology.continuous_of_linearMap f
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map hφ
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hφ
  · have hφ : Continuous (tensMap (E := E) (sndA F)) := by
      have hsm : ∀ (a : AF F) (x : TensorProduct F (AF F) E),
          tensMap (E := E) (sndA F) (a • x) = (sndA F a) • tensMap (E := E) (sndA F) x := by
        intro a x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      have hc : Continuous (sndA F : AF F → Af F) := continuous_snd
      haveI : IsModuleTopology (AF F) (TensorProduct F (AF F) E) := ⟨rfl⟩
      haveI : IsModuleTopology (Af F) (TensorProduct F (Af F) E) := ⟨rfl⟩
      have key : Continuous (fun p : AF F × TensorProduct F (Af F) E => (sndA F p.1) • p.2) :=
        continuous_smul.comp ((hc.comp continuous_fst).prodMk continuous_snd)
      letI : Module (AF F) (TensorProduct F (Af F) E) :=
        Module.compHom _ (sndA F).toRingHom
      haveI : ContinuousSMul (AF F) (TensorProduct F (Af F) E) := ⟨key⟩
      let f : TensorProduct F (AF F) E →ₗ[AF F] TensorProduct F (Af F) E :=
        { toFun := tensMap (E := E) (sndA F)
          map_add' := map_add _
          map_smul' := hsm }
      exact IsModuleTopology.continuous_of_linearMap f
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map hφ
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hφ

theorem continuous_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : Continuous (X.toInf hb) := by
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
  exact continuous_fst.comp ((continuous_splitA _ _).comp
    ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))

theorem measurable_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : Measurable (X.toInf hb) := by
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_toInf X hb).measurable

theorem volHTie_holds : VolHTie := by
  intro D X hb u hMT
  have h := (hMT.2.2.2 u).2
  have h1 := congrArg (fun m => m Set.univ) h
  rw [Measure.map_apply (measurable_toInf X hb) MeasurableSet.univ, Set.preimage_univ] at h1
  rw [← h1]
  unfold Formalism.L2.SG.Measures.amb
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]

end MassDataMassesW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StabFiniteOf
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem stabFinite_of (hH : HinfCompact) (hK : KCompactOpen) : StabFinite := by
  intro D X u x
  obtain ⟨e, he⟩ := splitIso_holds X.B.I.cm.sig X.B.I.J
  have hcK := (hK X).1
  have hcI : IsCompact ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))) := by
    haveI := hH X u
    exact isCompact_iff_compactSpace.2 this
  have homogComponent_comm_second_action : IsCompact ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
      (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hcK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcK3 : IsCompact (e ⁻¹' ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ×ˢ
        ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
          (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))) :=
    e.toHomeomorph.isCompact_preimage.2 (hcI.prod homogComponent_comm_second_action)
  haveI hdisc : DiscreteTopology ↥(show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from
      HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := discHF_setting X
  have pullback_fin_relation : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
      [DiscreteTopology Γ] (K : Set G), IsCompact K → Finite ↥((Subtype.val : Γ → G) ⁻¹' K) := by
    intro G _ _ _ Γ _ K hK
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
    have h1U : (1 : G) ∈ U := by
      have h0 : (1 : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' U := by rw [hUeq]; exact Set.mem_singleton 1
      exact h0
    have hc : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
    have hpre : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U ∈ nhds ((1 : G), (1 : G)) := by
      apply hc.continuousAt.preimage_mem_nhds
      simpa using hU.mem_nhds h1U
    obtain ⟨V1, hV1, V2, hV2, hVV⟩ := mem_nhds_prod_iff.1 hpre
    have hV1m : (1 : G) ∈ interior (V1 ∩ V2) := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hV1 hV2)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : K => (fun y => (k : G)⁻¹ * y) ⁻¹' interior (V1 ∩ V2))
      (fun k => isOpen_interior.preimage (continuous_const.mul continuous_id)) (by
        intro y hy
        exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, by rw [Set.mem_preimage, inv_mul_cancel]; exact hV1m⟩)
    have hch : ∀ s : ↥((Subtype.val : Γ → G) ⁻¹' K), ∃ i : t,
        ((((i : K) : G))⁻¹ * ((s : Γ) : G)) ∈ interior (V1 ∩ V2) := by
      intro s
      obtain ⟨i, hi, hs⟩ := Set.mem_iUnion₂.1 (ht s.2)
      exact ⟨⟨i, hi⟩, hs⟩
    choose f hf using hch
    refine Finite.of_injective f (fun s1 s2 h => ?_)
    have a1 := hf s1
    have a2 := hf s2
    rw [h] at a1
    have hmem : ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G), (((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) ∈ V1 ×ˢ V2 :=
      ⟨(interior_subset a1).1, (interior_subset a2).2⟩
    have hU' : ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G))⁻¹ * ((((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) ∈ U :=
      hVV hmem
    rw [show ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G))⁻¹ * ((((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) =
      ((s1 : Γ) : G)⁻¹ * ((s2 : Γ) : G) by group] at hU'
    have e1 : ((s1 : Γ)⁻¹ * (s2 : Γ) : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' U := hU'
    rw [hUeq, Set.mem_singleton_iff, inv_mul_eq_one] at e1
    exact Subtype.ext e1
  haveI := pullback_fin_relation _ (show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from
    HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) _ hcK3
  have hsurj : ∀ t : ↥(GamH X u ⊓ (KH X u).map (MulAut.conj x).toMonoidHom),
      ∃ γ : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
        γ ∈ ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
          prjF X.B.I.cm.sig X.B.I.J (frameOf X u) γ = t := by
    intro t
    have ht : (t : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∈
        (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).map
          (prjF X.B.I.cm.sig X.B.I.J (frameOf X u)) := by
      rw [prjF_map_ratOf]
      exact t.2.1
    obtain ⟨γ, hγ, hγt⟩ := Subgroup.mem_map.1 ht
    exact ⟨γ, hγ, hγt⟩
  choose γ hγ hγt using hsurj
  refine Finite.of_injective (fun t => (⟨⟨(γ t : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J),
    Subgroup.mem_comap.1 (hγ t)⟩, ?_⟩ : ((↑) ⁻¹' (e ⁻¹' ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ×ˢ
        ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
          (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))) :
      Set ↥(show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)))) ?_
  · simp only [Set.mem_preimage]
    rw [he]
    refine ⟨?_, ?_⟩
    · exact haMap_stabT X.B.I.cm.sig X.B.I.J (fstA X.B.I.F) (tupH (frameOf X u)) (γ t) (γ t).2
    · show (splitA X.B.I.cm.sig X.B.I.J (γ t : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).2 ∈
        (_ : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))
      rw [← prjF_val, hγt t]
      obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.1 t.2.2
      rw [← hkt]
      refine ⟨(k : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), Subgroup.mem_subgroupOf.1 hk, ?_⟩
      simp [MulAut.conj_apply]
  · intro t1 t2 h
    have h1 : (γ t1 : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) = γ t2 := by
      have h0 := congrArg (fun z => z.1.1) h
      simpa using h0
    have h2 : γ t1 = γ t2 := Subtype.ext h1
    apply Subtype.ext
    rw [← hγt t1, ← hγt t2, h2]

end MassDataMassesW
end
end

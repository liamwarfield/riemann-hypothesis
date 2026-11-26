module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
open ValuativeRel Topology

private theorem UpperTheory.V.Z.Tf.Orb.local_field_topology_facts (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    T2Space E ∧ SecondCountableTopology E ∧ IsOpen {x : E | valuation E x ≤ 1} := by
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  letI : (Valued.v (R := E)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := E).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  refine ⟨inferInstance, ?_, Valued.isOpen_integer E⟩
  open scoped Valued in
  have : ProperSpace E := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E
  infer_instance

theorem UpperTheory.V.Z.Tf.Orb.gLTop :
    UpperTheory.V.Z.Tf.Orb.GLTop := by
  intro E _ _ _ _ n
  obtain ⟨h2, hsc, hO⟩ := UpperTheory.V.Z.Tf.Orb.local_field_topology_facts E
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have hlast : ∀ Ω Ω' : Set (Matrix (Fin n) (Fin n) E), IsCompact Ω → IsCompact Ω' →
      IsCompact {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'} := by
    intro Ω Ω' hΩ hΩ'
    have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) E)).isCompact_preimage
      (hΩ.prod (hΩ'.image MulOpposite.continuous_op))
    have e : {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'} =
        Units.embedProduct (Matrix (Fin n) (Fin n) E) ⁻¹' (Ω ×ˢ (MulOpposite.op '' Ω')) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
        MulOpposite.op_injective.mem_set_image]
    rw [e]
    exact h
  refine ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance, ?_, hlast⟩
  let O : Subring E := (valuation E).integer
  let M : Set (Matrix (Fin n) (Fin n) E) := {A | ∀ i j, A i j ∈ O}
  have hMmul : ∀ A ∈ M, ∀ B ∈ M, A * B ∈ M := by
    intro A hA B hB i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (hA i l) (hB l j)
  have hMone : (1 : Matrix (Fin n) (Fin n) E) ∈ M := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hMo : IsOpen M := by
    have e : M = ⋂ i, ⋂ j, (fun A : Matrix (Fin n) (Fin n) E => A i j) ⁻¹' {x : E | valuation E x ≤ 1} := by
      ext A
      simp only [M, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_apply_apply i j)
  have hMc : IsCompact M := by
    have hc := IsNonarchimedeanLocalField.isCompact_closedBall E 1
    have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
        {x : E | valuation E x ≤ 1}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
    have e : M = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
        {x : E | valuation E x ≤ 1}) := by
      ext A
      exact ⟨fun hA i _ j _ => hA i j, fun hA i j => hA i trivial j trivial⟩
    rw [e]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ M ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ M}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul]
          exact hMmul _ ha _ hb
        · rw [mul_inv_rev, Units.val_mul]
          exact hMmul _ hb' _ ha'
      one_mem' := ⟨hMone, by rw [inv_one]; exact hMone⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rw [inv_inv]; exact ha⟩ }
  refine ⟨K, ?_, hlast M M hMc hMc⟩
  exact (hMo.preimage Units.continuous_val).inter (hMo.preimage Units.continuous_coe_inv)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
noncomputable section

open Module

namespace UpperTheory.V.Z.Tf.Orb

private theorem endComm {L V : Type} [Field L] [IsAlgClosed L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (f x y : Module.End L V) (hf : f.charpoly.Separable) (hx : Commute x f) (hy : Commute y f) : Commute x y := by
  have key : ∀ μ : L, ∀ v ∈ f.maxGenEigenspace μ, (x * y) v = (y * x) v := by
    intro μ v hv
    have h1 : finrank L (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨w, hw⟩ := finrank_le_one_iff.mp h1
    have mx := Module.End.mapsTo_maxGenEigenspace_of_comm hx.symm μ
    have my := Module.End.mapsTo_maxGenEigenspace_of_comm hy.symm μ
    obtain ⟨c, hc⟩ := hw ⟨v, hv⟩
    obtain ⟨a, ha⟩ := hw ⟨x w, mx w.2⟩
    obtain ⟨b, hb⟩ := hw ⟨y w, my w.2⟩
    have hc' : v = c • (w : V) := by simpa using (congrArg Subtype.val hc).symm
    have ha' : x w = a • (w : V) := by simpa using (congrArg Subtype.val ha).symm
    have hb' : y w = b • (w : V) := by simpa using (congrArg Subtype.val hb).symm
    simp only [hc', Module.End.mul_apply, map_smul, ha', hb', smul_smul, mul_comm a b]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top f
  have : (⊤ : Submodule L V) ≤ LinearMap.eqLocus (x * y) (y * x) := by
    rw [← htop]
    exact iSup_le fun μ v hv => key μ v hv
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem centComm : CentComm := by
  intro K _ n A X Y hA hX hY
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →+* Module.End L (Fin n → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).toRingEquiv.toRingHom.comp (algebraMap K L).mapMatrix
  have hφ : Function.Injective φ :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).injective.comp
      (Matrix.map_injective (algebraMap K L).injective)
  have hch : (φ A).charpoly = A.charpoly.map (algebraMap K L) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_toLin']
    rfl
  have h := endComm (φ A) (φ X) (φ Y) (hch ▸ hA.map) (hX.map φ) (hY.map φ)
  apply hφ
  rw [map_mul, map_mul]
  exact h

end UpperTheory.V.Z.Tf.Orb
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarComm :
    UpperTheory.V.Z.Tf.Orb.HaarComm := by
  intro G _ _ _ _ _ _ _ _ H hH hc μ hμ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  refine ⟨inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular μ, ⟨fun g => ?_⟩⟩
  have : (fun h : H => h * g) = fun h => g * h := funext fun h => mul_comm h g
  rw [this]
  exact map_mul_left_eq_self μ g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarConj :
    UpperTheory.V.Z.Tf.Orb.HaarConj := by
  intro G _ _ _ _ _ _ _ _ H H' y hy μ hμ
  let e : H ≃ₜ* H' :=
    { toFun := fun x => ⟨y⁻¹ * x * y, (hy x).1 x.2⟩
      invFun := fun z => ⟨y * z * y⁻¹, (hy _).2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨μ.map e, e.isHaarMeasure_map μ, ?_⟩
  have he : Measurable (e : H → H') := (map_continuous e).measurable
  exact (Measure.map_map (g := fun x : H' => (x : G)) measurable_subtype_coe he).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Untwist
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem aux {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μG : Measure G) (H H' : Subgroup G) (e : H' = H)
    (μ : Measure H) (hμ : μ.IsHaarMeasure) : ∃ μ' : Measure H', μ'.IsHaarMeasure ∧
      (∀ ρ, IsQuotNormaliser H' μ' ρ ↔ IsQuotNormaliser H μ ρ) ∧ ∀ F, quotIntegral μG H' μ' F = quotIntegral μG H μ F := by
  subst e
  exact ⟨μ, hμ, fun _ => Iff.rfl, fun _ => rfl⟩

theorem UpperTheory.V.Z.Tf.Orb.untwist :
    UpperTheory.V.Z.Tf.Orb.Untwist := by
  intro k _ _ _ _ n _ _ μk γ
  have h1 : ∀ g : GL (Fin n) k, sigmaGL (1 : k ≃ₐ[k] k) g = g := fun g => by rw [sigmaGL_one]; rfl
  refine ⟨fun τ => ?_, h1, fun h => ?_, fun μ hμ => ?_⟩
  · have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  · have : normGL (1 : k ≃ₐ[k] k) γ = γ := by
      rw [normGL, Module.finrank_self]
      simp [twNorm]
    rwa [IsTwRegSemisimple, this]
  · have e : twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ = Subgroup.centralizer {γ} := by
      ext x
      rw [mem_twCent, h1, Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
      rw [commute_iff_eq]
    obtain ⟨μ', a, b, c⟩ := aux μk _ _ e μ hμ
    refine ⟨μ', a, b, fun f => ?_⟩
    rw [twOrbIntegralC, orbIntegralC, c]
    simp only [twConj, h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotConj
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotConj :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotConj := by
  intro hC hI G _ _ _ _ _ _ _ _ μG hμ H H' y hH hc hy μ μ' h1 h2 hm F hF hFH
  have hy' : ∀ z, z ∈ H' ↔ y * z * y⁻¹ ∈ H := fun z => by rw [hy]; simp [mul_assoc]
  have hH' : IsClosed (H' : Set G) := by
    have : (H' : Set G) = (fun z => y * z * y⁻¹) ⁻¹' H := Set.ext hy'
    rw [this]
    exact hH.preimage (by fun_prop)
  have hc' : ∀ a ∈ H', ∀ b ∈ H', Commute a b := fun a ha b hb => by
    have := (hc _ ((hy' a).1 ha) _ ((hy' b).1 hb)).eq
    have h : y * a * b = y * b * a := by simpa [← mul_assoc] using this
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  obtain ⟨s1, i1, -⟩ := hC G H hH hc μ h1
  obtain ⟨s2, i2, -⟩ := hC G H' hH' hc' μ' h2
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h : H, f (y⁻¹ * h * y) ∂μ = ∫⁻ h : H', f h ∂μ' := fun f hf => by
    rw [← lintegral_map hf (g := fun x : H => y⁻¹ * (x : G) * y) (by fun_prop), hm,
      lintegral_map hf (g := fun x : H' => (x : G)) measurable_subtype_coe]
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H' μ' fun g => ρ (y * g) := ⟨hρ.1.comp (measurable_const_mul y), fun g => by
      rw [← key (fun z => ρ (y * (z * g))) (hρ.1.comp (by fun_prop)), ← hρ.2 (y * g)]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [hI G μG hμ H μ s1 i1 F hF hFH ρ hρ, hI G μG hμ H' μ' s2 i2 (fun g => F (y * g)) (hF.comp (measurable_const_mul y)) (fun h hh g => by
      rw [← hFH _ ((hy' h).1 hh) (y * g)]; simp [mul_assoc]) _ hρ']
    exact integral_mul_left_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' μ' ρ := fun ⟨ρ, hρ⟩ => hex ⟨fun g => ρ (y⁻¹ * g), hρ.1.comp (measurable_const_mul _), fun g => by
      rw [← hρ.2 (y⁻¹ * g), ← key (fun z => ρ (z * (y⁻¹ * g))) (hρ.1.comp (by fun_prop))]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [quotIntegral, quotIntegral, dite_eq_right hex, dite_eq_right hex']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotIndep
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

section Core

variable {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group T] [MeasurableSpace T] [MeasurableInv T]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν] {j : T →* G}

omit [MeasurableInv G] [MeasurableInv T] in
private theorem ae_fin (hj : Measurable j) {ρ : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) :
    ∀ᵐ g ∂μ, ρ g < ∞ := by
  have hA : MeasurableSet {g | ρ g = ∞} := hm (measurableSet_singleton _)
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have h1 : ∫⁻ g, ∫⁻ t, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂ν ∂μ = 0 := by
    refine (lintegral_congr fun g => ?_).trans lintegral_zero
    have h2 : ∀ᵐ t ∂ν, ρ (j t * g) < ∞ := ae_lt_top (hm.comp (hj.mul_const g)) (by rw [h]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae (h2.mono fun t ht => ?_)).trans lintegral_zero
    exact Set.indicator_of_notMem (s := {g | ρ g = ∞}) ht.ne _
  rw [lintegral_lintegral_swap (f := fun g t => {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g))
    ((measurable_one.indicator hA).comp hmul).aemeasurable] at h1
  have h3 : ∀ t : T, ∫⁻ g, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂μ = μ {g | ρ g = ∞} := fun t => by
    rw [lintegral_mul_left_eq_self, lintegral_indicator_one hA]
  simp only [h3, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · rw [ae_iff]
    simpa using h1
  · have := h 1
    rw [Measure.measure_univ_eq_zero.1 h1] at this
    simp at this

private theorem lint_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫⁻ g, F g * ρ g ∂μ = ∫⁻ g, F g * ρ' g ∂μ := by
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => j p.2⁻¹ * p.1 := (hj.comp measurable_snd.inv).mul measurable_fst
  have a : ∀ g, F g * ρ g = ∫⁻ t, F g * ρ g * ρ' (j t * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ' (j t * g)) (hm'.comp (hj.mul_const g)), h', mul_one]
  have b : ∀ g, F g * ρ' g = ∫⁻ t, F g * ρ' g * ρ (j t⁻¹ * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ (j t⁻¹ * g)) (hm.comp ((hj.comp measurable_inv).mul_const g)),
      lintegral_inv_eq_self (fun t : T => ρ (j t * g)), h, mul_one]
  rw [lintegral_congr a, lintegral_congr b,
    lintegral_lintegral_swap (f := fun g t => F g * ρ g * ρ' (j t * g))
      (((hF.comp measurable_fst).mul (hm.comp measurable_fst)).mul (hm'.comp hmul)).aemeasurable,
    lintegral_lintegral_swap (f := fun g t => F g * ρ' g * ρ (j t⁻¹ * g))
      (((hF.comp measurable_fst).mul (hm'.comp measurable_fst)).mul (hm.comp hmul')).aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [← lintegral_mul_left_eq_self _ (j t⁻¹)]
  refine lintegral_congr fun g => ?_
  rw [hFH, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul]
  ring

private theorem wd_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℂ} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μ := by
  have key : ∀ {ρ : G → ℝ≥0∞}, Measurable ρ → (∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) →
      ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := fun {ρ} hm h => by
    rw [integral_map (f := fun z : ℂ => z) hF.aemeasurable aestronglyMeasurable_id, integral_withDensity_eq_integral_toReal_smul hm (ae_fin hj hm h)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [mul_comm]
  rw [key hm h, key hm' h']
  congr 1
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA), withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), ← lintegral_indicator (hF hA)]
  have e : ∀ ρ : G → ℝ≥0∞, (F ⁻¹' A).indicator ρ = fun g => (F ⁻¹' A).indicator 1 g * ρ g := fun ρ => funext fun g => by
    by_cases hg : g ∈ F ⁻¹' A <;> simp [hg]
  rw [e, e ρ']
  refine lint_eq hj (measurable_one.indicator (hF hA)) (fun t g => ?_) hm h hm' h'
  by_cases hg : F g ∈ A <;> simp [Set.indicator, hFH, hg]

end Core

theorem UpperTheory.V.Z.Tf.Orb.quotIndep :
    UpperTheory.V.Z.Tf.Orb.QuotIndep := by
  intro G _ _ _ _ _ _ _ _ μG hμ H μ _ _ F hF hFH ρ hρ
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hex : ∃ ρ, IsQuotNormaliser H μ ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dite_eq_left hex]
  exact wd_eq (j := H.subtype) measurable_subtype_coe hF (fun t g => hFH t t.2 g) hex.choose_spec.1 hex.choose_spec.2 hρ.1 hρ.2
end

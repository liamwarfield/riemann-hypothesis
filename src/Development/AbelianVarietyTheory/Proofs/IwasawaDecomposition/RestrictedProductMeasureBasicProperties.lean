module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTupleMeasureExtOfPureTensorIntegrals
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdBasic

theorem repr_map {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E)
    (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [hx, hy]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

def box (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}

theorem isOpen_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (box (n := n) (M := M) b S) := by
  have h : box (n := n) (M := M) b S = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        ((Algebra.TensorProduct.basis (AF F) b).coord k (X a i)).2) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} := by
    ext X
    simp only [box, latV, projV, projFin, repr_map, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [h]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => IsOpen.preimage ?_ ?_
  · have h1 : Continuous ((Algebra.TensorProduct.basis (AF F) b).coord k) :=
      IsModuleTopology.continuous_of_linearMap _
    exact continuous_snd.comp (h1.comp ((continuous_apply i).comp (continuous_apply a)))
  · exact RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun _ => Valued.isOpen_valuationSubring _)

theorem box_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    box (n := n) (M := M) b S ⊆ box b T := fun _ hX v hv => hX v fun hs => hv (h hs)

theorem exists_mem_box (X : Fin n → Fin M → AF F ⊗[F] E) : ∃ S, X ∈ box b S := by
  have h := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.1
  have hX : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
    have h1 := Set.mem_range_self (f := fun X : Fin n → Fin M → AF F ⊗[F] E =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) X
    rw [h, Set.mem_setOf_eq] at h1
    exact h1
  have hf := Filter.eventually_cofinite.1 hX
  refine ⟨hf.toFinset, fun v hv => ?_⟩
  by_contra h'
  exact hv (by simpa using h')

variable {b} {ν : Measure (Fin n → Fin M → AF F ⊗[F] E)}
  {mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
  {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}

theorem measure_rect (h : IsProd b ν mi mv) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)}
    {Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)}
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) :
    ν ({X | projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} ∩ box b S) =
      mi Ai * (∏ v ∈ S, mv v (Av v)) * tailProd b mv S := by
  have hm := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).1.measurable
  have hmi : Measurable (projInf (F := F) (E := E) (M := M) (n := n)) := measurable_fst.comp hm
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F),
      Measurable fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X) := fun v =>
    (measurable_pi_apply v).comp (measurable_snd.comp hm)
  have hR : MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} := by
    have : {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} =
        projInf ⁻¹' Ai ∩ ⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' Av v := by
      ext X; simp
    rw [this]
    exact (hmi hi).inter (S.measurableSet_biInter fun v _ => hmv v (hv v))
  have key := h.2 S (Ai.indicator 1) (fun v => (Av v).indicator 1)
    (measurable_const.indicator hi) (fun v => measurable_const.indicator (hv v))
  simp only [lintegral_indicator_one hi, lintegral_indicator_one (hv _)] at key
  rw [← key, ← Measure.restrict_apply hR, ← lintegral_indicator_one hR]
  refine lintegral_congr fun X => ?_
  by_cases hX : projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v
  · rw [Set.indicator_of_mem (by exact hX), Set.indicator_of_mem hX.1,
      Finset.prod_eq_one fun v hv => Set.indicator_of_mem (hX.2 v hv) _]
    simp
  · rw [Set.indicator_of_notMem (by exact hX)]
    rcases not_and_or.1 hX with h1 | h1
    · rw [Set.indicator_of_notMem h1, zero_mul]
    · push Not at h1
      obtain ⟨v, hv, h1⟩ := h1
      rw [Finset.prod_eq_zero hv (Set.indicator_of_notMem h1 _), mul_zero]

theorem exists_tailProd_ne_zero (h : Conv b mi mv) : ∃ S, tailProd b mv S ≠ 0 := by
  have hs := h.2.2
  have ht := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  have hf := Filter.eventually_cofinite.1 ht
  refine ⟨hf.toFinset, ?_⟩
  have hpos : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset},
      0 < (mv v.1 (latV b v.1)).toReal := fun v => by
    have h1 : |(mv v.1 (latV b v.1)).toReal - 1| < 1 := by
      by_contra h'
      exact v.2 (by simpa using h')
    linarith [(abs_lt.1 h1).1]
  have hs' : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset} =>
      (mv v.1 (latV b v.1)).toReal - 1 := (hs.of_abs).subtype _
  have hl := Real.summable_log_one_add_of_summable hs'
  simp only [add_sub_cancel] at hl
  rw [tailProd, ← Real.rexp_tsum_eq_tprod hpos hl]
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem finiteOnCompacts (h : IsProd b ν mi mv) : IsFiniteMeasureOnCompacts ν := by
  classical
  refine ⟨fun K hK => ?_⟩
  obtain ⟨S, hS⟩ := hK.elim_directed_cover (box b) (isOpen_box b)
    (fun X _ => Set.mem_iUnion.2 (exists_mem_box b X))
    (fun S T => ⟨S ∪ T, box_mono b Finset.subset_union_left, box_mono b Finset.subset_union_right⟩)
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2
  have hi := hK.image hc.1
  have hv := fun v => hK.image (hc.2 v)
  have key := measure_rect h S hi.measurableSet (fun v => (hv v).measurableSet)
  haveI := h.1.1
  haveI := h.1.2.1
  refine lt_of_le_of_lt (measure_mono fun X hX => ?_) (key.trans_lt ?_)
  · exact ⟨⟨⟨X, hX, rfl⟩, fun v _ => ⟨X, hX, rfl⟩⟩, hS hX⟩
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hi.measure_lt_top
      (ENNReal.prod_lt_top fun v _ => (hv v).measure_lt_top)) ENNReal.ofReal_lt_top

theorem ne_zero (h : IsProd b ν mi mv) (hi : mi ≠ 0) (hv : ∀ v, mv v ≠ 0) : ν ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_tailProd_ne_zero h.1
  have := measure_rect h S (Av := fun _ => Set.univ) MeasurableSet.univ fun _ => MeasurableSet.univ
  rintro rfl
  exact mul_ne_zero (mul_ne_zero (Measure.measure_univ_ne_zero.2 hi)
    (Finset.prod_ne_zero_iff.2 fun v _ => Measure.measure_univ_ne_zero.2 (hv v))) hS this.symm

theorem null (h : IsProd b ν mi mv) (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) (zi : mi Aiᶜ = 0)
    (zv : ∀ v, mv v (Av v)ᶜ = 0) :
    ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have h1 : ∀ S, ν ({X | projInf X ∈ Aiᶜ ∧ ∀ v ∈ S, projV v (projFin X) ∈ Set.univ} ∩ box b S) = 0 :=
    fun S => by
      rw [measure_rect h S (Av := fun _ => Set.univ) hi.compl fun _ => MeasurableSet.univ, zi,
        zero_mul, zero_mul]
  have h2 : ∀ (w : HeightOneSpectrum (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))),
      ν ({X | projInf X ∈ Set.univ ∧ ∀ v ∈ insert w S,
        projV v (projFin X) ∈ (if v = w then (Av v)ᶜ else Set.univ)} ∩ box b (insert w S)) = 0 :=
    fun w S => by
      rw [measure_rect h (insert w S) (Av := fun v => if v = w then (Av v)ᶜ else Set.univ)
        MeasurableSet.univ fun v => by
          split_ifs
          exacts [(hv v).compl, MeasurableSet.univ],
        Finset.prod_eq_zero (Finset.mem_insert_self w S) (by simpa using zv w), mul_zero, zero_mul]
  refine measure_mono_null (fun X hX => ?_) (measure_union_null (measure_iUnion_null h1)
    (measure_iUnion_null fun w => measure_iUnion_null (h2 w)))
  obtain ⟨S, hS⟩ := exists_mem_box b X
  rcases not_and_or.1 hX with h3 | h3
  · exact Or.inl (Set.mem_iUnion.2 ⟨S, ⟨h3, fun _ _ => trivial⟩, hS⟩)
  · obtain ⟨w, hw⟩ := not_forall.1 h3
    refine Or.inr (Set.mem_iUnion₂.2 ⟨w, S, ⟨trivial, fun v _ => ?_⟩,
      box_mono b (Finset.subset_insert w S) hS⟩)
    split_ifs with h4
    · subst h4; exact hw
    · trivial

end GlobalTheory.GaugeEx.ProdBasic

theorem GlobalTheory.GaugeEx.isProd_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  intro F E _ _ _ _ _ d b n M ν mi mv h
  refine ⟨ProdBasic.finiteOnCompacts h, ProdBasic.ne_zero h, fun ν' h' => ?_, ProdBasic.null h⟩
  refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b n M ν' ν fun Φ Φi Φf Φv h1 h2 h3 h4 => ?_
  have k := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b n M ν mi mv h d b Φ Φi Φf Φv h1 h2 h3 h4
  have k' := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b n M ν' mi mv h' d b Φ Φi Φf Φv h1 h2 h3 h4
  exact ⟨k'.1, k.1, k'.2.2.trans k.2.2.symm⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProductMeasure_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  first | exact @GlobalTheory.GaugeEx.isProd_basic | exact GlobalTheory.GaugeEx.isProd_basic | (intros; apply GlobalTheory.GaugeEx.isProd_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
noncomputable section

namespace GlobalTheory.LevelHecke.MovePair

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem pairOf_act {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M M' : Submodule R V)
    (pr : M →+ W) (pr' : M' →+ W') (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (g : V ≃ₗ[R] V) (a : k)
    (h1 : ∀ z ∈ M', ∃ s, res s ≠ 0 ∧ s • g z ∈ M)
    (h2 : ∀ z, g z ∈ M → ∃ s, res s ≠ 0 ∧ s • z ∈ M')
    (h3 : ∀ z (hz : z ∈ M') (hg : g z ∈ M), φ' (pr' ⟨z, hz⟩) = a * φ (pr ⟨g z, hg⟩)) :
    (pairOf res M' pr' φ').act g = (pairOf res M pr φ).dil a := by
  have key : ∀ z, z ∈ loc res M' ↔ g z ∈ loc res M := by
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      refine loc_sat res M s _ hs0 ?_
      rw [← map_smul]
      exact (mem_loc _ _ _).2 (h1 _ h)
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      rw [← map_smul] at h
      exact loc_sat res M' s _ hs0 ((mem_loc _ _ _).2 (h2 _ h))
  ext x
  · rw [Pr.mem_act]
    show g.symm x ∈ loc res M' ↔ x ∈ loc res M
    rw [key, g.apply_symm_apply]
  · obtain ⟨z, rfl⟩ := g.surjective x
    show φ' (locExt res M' pr' (g.symm (g z))) = a * φ (locExt res M pr (g z))
    rw [g.symm_apply_apply]
    by_cases hz : z ∈ loc res M'
    · have hz' := (key z).1 hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      obtain ⟨t, ht0, h'⟩ := (mem_loc _ _ _).1 hz'
      have e1 : (t * s) • z ∈ M' := by rw [mul_smul]; exact M'.smul_mem _ h
      have e2 : (t * s) • g z ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem _ h'
      have e3 : g ((t * s) • z) ∈ M := by rw [map_smul]; exact e2
      have hne : res (t * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero ht0 hs0
      have e4 := h3 _ e1 e3
      have e5 : (⟨g ((t * s) • z), e3⟩ : M) = ⟨(t * s) • g z, e2⟩ := Subtype.ext (map_smul _ _ _)
      rw [e5, locExt_spec res M' pr' hs' z hz _ e1, locExt_spec res M pr hs _ hz' _ e2, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul] at e4
      apply mul_left_cancel₀ hne
      rw [e4]; ring
    · rw [locExt_off _ _ _ _ hz, locExt_off _ _ _ _ (fun h => hz ((key z).2 h)), map_zero, map_zero, mul_zero]

theorem mov_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (z : Fin n → E) :
    (bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y')).1 *ᵥ
      (((bc (prV (E := E) v) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a))) =
    ((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) := by
  have e : (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) =
      (γ.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [e, mulVec_mulVec, ← Units.val_mul, map_mul, mul_inv_cancel_right, map_mul, map_inv, Units.val_mul,
    ← mulVec_mulVec]
  rfl

theorem mulsF_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hM : MulsF S v hv a h) {k : Type} [Ring k] (φ : S.fM v hv ≃+ k)
    (x x' : Fin n → E ⊗[F] v.adicCompletion F) (e : h.1 *ᵥ x = x') :
    (x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) ↔
      x' ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) ∧
    ∀ hx hx', φ (S.fT v hv ⟨x, hx⟩) = (a : k) * φ (S.fT v hv ⟨x', hx'⟩) := by
  subst e
  obtain ⟨hg, hf⟩ := hM
  refine ⟨hg x, fun hx hx' => ?_⟩
  rw [← hf ⟨x, hx⟩, map_zsmul, zsmul_eq_mul]

section Tied

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

theorem ld_lattice (c : (D.mem u).C.cls i) : Submodule.IsLattice D.host.E (Ld D u i hi c) := by
  letI := D.host.cmStar
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := bwB_clsCrd_lat D u i hi c
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i c).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i c).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i c : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i c).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  obtain ⟨d, hd, hle⟩ := LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  exact Submodule.IsLattice.of_fg D.host.E (LocB.fg_of_le_bnd hd hle)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem ld_loc (K : ClsTied u i hi) (v : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈ dualV K v := by
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := bwB_clsCrd_lat D u i hi c
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i c).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i c).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i c : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i c).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  letI : Submodule.IsLattice D.host.E K.lev.Lb :=
    Submodule.IsLattice.of_fg D.host.E (Module.Finite.iff_fg.1 K.lev.Lb_fin)
  have hLb : Submodule.IsFullLattice D.host.E K.lev.Lb := ⟨K.lev.Lb_span⟩
  refine GlobalTheory.T.unitary_completion_maps_dualLattices D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi c) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) hL hLb
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x

end Tied


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem pc_act_of_mulsF : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  intro D u A i hi P K fMe hT v c c' γ a hM
  have hin : ∀ c (z : Fin (D.R.N i) → D.host.E), z ∈ Ld D u i hi c →
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 :=
    fun c z hz => (ld_loc K _ c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hout : ∀ c (z : Fin (D.R.N i) → D.host.E),
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 →
      ∃ s, A.res v s ≠ 0 ∧ s • z ∈ Ld D u i hi c := by
    intro c z hz
    obtain ⟨r, hr, h⟩ := GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion D.host.F D.host.E (A.eV v).1 _ _ (ld_lattice c) z ((ld_loc K _ c _).2 hz)
    exact ⟨_, fun h0 => hr ((A.res_v v r).2 h0), h⟩
  have hst := fun z => mulsF_apply K.lev _ _ a _ hM (fMe v) _ _
    (mov_mulVec (A.eV v).1 (K.y c).1 (K.y c').1 γ z)
  refine pairOf_act _ _ _ _ _ _ _ (P.pr_smul v c) (P.pr_smul v c') (glE γ) _
    (fun z hz => hout c (γ.1 *ᵥ z) ((hst z).1.1 (hin c' z hz)))
    (fun z hz => hout c' z ((hst z).1.2 (hin c (γ.1 *ᵥ z) hz))) (fun z hz hz' => ?_)
  · have hz2 : γ.1 *ᵥ z ∈ Ld D u i hi c := hz'
    have hT' : ∀ c (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c), (D.fm u).fv i v c (P.pr v c ⟨z, hz⟩) =
        fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hin c z hz⟩) := fun c z hz => hT v c ⟨z, hz⟩ (hin c z hz)
    have e1 := hT' c' z hz
    have e2 := hT' c _ hz2
    exact e1.trans (((hst z).2 _ _).trans (congrArg (fun t => (a : (D.mem u).A.Fv v) * t) e2.symm))

end GlobalTheory.LevelHecke.MovePair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctionalStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  first | exact @GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF | exact GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF | (intros; apply GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions IsDedekindDomain
open Formalism.MainNotions.S (FlagG XS ddS FrameOK)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS XLam IsFixedConv FixedHyp)
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm.Conv

section Ideals

variable {E : Type} [Field E] [NumberField E]

theorem exists_local_gen {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) :
    ∃ c : E, c ≠ 0 ∧ c ∈ I ∧ ∀ x ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  have int {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹) : ∃ o : 𝓞 E, (o : E) = a * b := by
    have := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  obtain ⟨a, ha, b, hb, s, hs, e⟩ : ∃ a ∈ I, ∃ b ∈ I⁻¹, ∃ s : 𝓞 E, s ∉ P ∧ (s : E) = a * b := by
    by_contra h
    have h1 : (1 : E) ∈ I * I⁻¹ := by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
    obtain ⟨s, hs, e⟩ := FractionalIdeal.mul_induction_on (C := fun x => ∃ s ∈ P, (s : E) = x) h1
      (fun a ha b hb => by
        obtain ⟨o, e⟩ := int ha hb
        exact ⟨o, by_contra fun k => h ⟨a, ha, b, hb, o, k, e⟩, e⟩)
      (fun _ _ ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨s + t, add_mem hs ht, by rw [← e, ← f]; simp⟩)
    obtain rfl : s = 1 := RingOfIntegers.ext e
    exact hP ((Ideal.eq_top_iff_one _).2 hs)
  refine ⟨a, fun h => hs ?_, ha, fun x hx => ⟨s, hs, ?_⟩⟩
  · obtain rfl : s = 0 := RingOfIntegers.ext (by rw [e, h, zero_mul]; rfl)
    exact zero_mem _
  · obtain ⟨o, f⟩ := int hx hb
    exact ⟨o, by rw [e, f]; ring⟩

theorem exists_gen_dInv (j : ℕ) (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    ∃ c : E, c ≠ 0 ∧ c ∈ dInv E j ∧ (¬ P ∣ differentIdeal ℤ (𝓞 E) → c = 1) ∧
      ∀ x ∈ dInv E j, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  by_cases h : P ∣ differentIdeal ℤ (𝓞 E)
  · obtain ⟨c, h1, h2, h3⟩ := exists_local_gen (I := dInv E j)
      (fun e => by simpa [e] using Iota.one_mem_dInv (E := E) j) hP.ne_top
    exact ⟨c, h1, h2, fun k => absurd h k, h3⟩
  · obtain ⟨s, hs, hn⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.dvd_iff_le.2 h)
    refine ⟨1, one_ne_zero, Iota.one_mem_dInv j, fun _ => rfl, fun x hx =>
      ⟨s ^ j, fun k => hn (hP.mem_of_pow_mem j k), ?_⟩⟩
    have h0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
    have := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E) (Ideal.pow_mem_pow hs j)) hx
    rw [FractionalIdeal.coeIdeal_pow, dInv, ← mul_pow, mul_inv_cancel₀ h0, one_pow] at this
    obtain ⟨o, e⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨o, by rw [mul_one]; exact e.symm⟩

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P) : ¬ P ∣ differentIdeal ℤ (𝓞 E) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have e : HeightOneSpectrum.asIdeal '' placesOver E p = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := v.isPrime
      exact ⟨v.isPrime, (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa [placesOver] using hv)⟩
    · rintro ⟨h1, h2⟩
      have k : (p : 𝓞 E) ∈ Q := by simpa using (Ideal.liesOver_span_iff h1.ne_top hp').1 h2
      exact ⟨⟨Q, h1, fun e => hp.ne_zero (by simpa [e] using k)⟩, k, rfl⟩
  have hd := GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp E (by
    rw [← e, Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw, h])
  exact not_dvd_differentIdeal_iff.2 ((not_dvd_discr_iff_forall_mem E (𝓞 E) hp').1 hd P hP (by simpa using hm))

end Ideals

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) (Fin S.rank → E)} {F : LFlag S r T}

variable (h : IntFrame (starRingEnd E) S.gram T Λ (coMat S (Formalism.MainNotions.S.Lat.frame F)))
include h

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddS_eq : ddS D = (differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) := by
  rw [ddS, differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.F) (𝓞 D.host.E),
    GlobalTheory.CMDiscrSq.differentIdeal_eq_top D.sp.cm, Ideal.top_mul]

theorem level_not_dvd (P : HeightOneSpectrum (𝓞 D.host.E)) (h : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.E) := by
  have := P.isPrime
  rw [gS, Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact not_dvd_different (D.host.g_prime 0) (D.nd.g_split 0) _ h
  · exact not_dvd_different (D.host.g_prime 1) (D.nd.g_split 1) _ h

variable {D}

end Record

end GlobalTheory.IntTerm.Conv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEq
noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem nsmul_latS_of_nsmul {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L M : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ z ∈ M, T • z ∈ L) (w : Fin n → E ⊗[F] v.adicCompletion F)
    (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) M) :
    T • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
  have key : ∀ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
      T • x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
    intro x hx
    unfold latS at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨T • z, h z hz, ?_⟩
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  exact key w hw


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem nsmul_dual_mem_loc {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hLb : Submodule.IsFullLattice E S.Lb :=
    { toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp S.Lb_fin)
      span_eq_top := S.Lb_span }

  have hT : ∀ x ∈ dualL (σ : E →+* E) J S.Lb, T • x ∈ S.Lb := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact S.Lb_dual x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  let zV : Fin n → E ⊗[F] v.adicCompletion F := fun a => inclE (F := F) (v.adicCompletion F) (z a)
  have hdual : (y⁻¹).1 *ᵥ zV ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J S.Lb) := by
    apply (GlobalTheory.DualCompletion.mem_latS_dualL σ J hJ v S.Lb hLb _).2
    intro u hu
    have huL : y.1 *ᵥ u ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
      apply (hyl _).2
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hyU : cT (sigR σ (v.adicCompletion F)) y.1 *
        J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
        J.map (inclE (F := F) (v.adicCompletion F)) := hy
    have hpair := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F))
      (J.map (inclE (F := F) (v.adicCompletion F))) y.1 u ((y⁻¹).1 *ᵥ zV)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at hpair
    rw [← hpair]
    exact Formalism.L2.G.RelativeIndexFlags.pair_int v σ J L z
      ((GlobalTheory.DualCompletion.mem_dualL (σ : E →+* E) J L z).1 hz) _ huL
  have h2 := nsmul_latS_of_nsmul v T S.Lb (dualL (σ : E →+* E) J S.Lb) hT _ hdual
  rw [← Matrix.mulVec_smul] at h2
  have h3 := (hyl _).mpr h2
  have h4 : (fun a => inclE (F := F) (v.adicCompletion F) ((T • z) a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) L := by
    convert h3 using 1
    funext a
    simp only [zV, Pi.smul_apply, map_nsmul]
  exact GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion F E v n L hL (T • z) h4


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem nsmul_dual_mem_loc_adelic {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (y.1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hloc : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    intro x
    rw [← map_inv]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hyl x
  exact nsmul_dual_mem_loc S hJ v L hL _ (Formalism.UG.P.afsplit_bc_mem σ J v y.1 y.2) hloc z hz

end Core

theorem loc_sup_ker_smul {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] (res : R →+* k) (t : R)
    (hu : Unram res t) (M N : Submodule R V) (h : ∀ z ∈ N, t • z ∈ loc res M) :
    loc res (M ⊔ RingHom.ker res • N) = loc res M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res _ x).mp hx
    have hle : M ⊔ RingHom.ker res • N ≤ loc res M := by
      refine sup_le (le_loc res M) ?_
      rw [Submodule.smul_le]
      intro a ha z hz
      obtain ⟨s', b, hs', hsab⟩ := hu.2 a (RingHom.mem_ker.mp ha)
      apply loc_sat res M s' _ hs'
      rw [smul_smul, hsab, mul_comm, ← smul_smul]
      exact Submodule.smul_mem _ b (h z hz)
    exact loc_sat res M s x hs (hle hsx)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res M x).mp hx
    exact (mem_loc res _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem loc_lk_eq_loc_cls : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  intro D u A i hi K v c
  refine loc_sup_ker_smul (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (GlobalTheory.T.levelPrime_unramifiedUniformizer D u A v) _ _ ?_
  intro z hz
  obtain ⟨r, hr, hrz⟩ := nsmul_dual_mem_loc_adelic K.lev (bwB_gramN_det D i hi) (A.eV v).1
    (clsCrd D u i hi c) (bwB_clsCrd_lat D u i hi c) (K.y c) (K.y_lat c) z hz
  refine (mem_loc _ _ _).mpr ⟨algebraMap _ _ r, fun h0 => hr ((A.res_v v r).mpr h0), ?_⟩
  rwa [Nat.cast_smul_eq_nsmul]

end GlobalTheory.LevelHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEqStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classLattice_sup_primeDual_localization_eq : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  first | exact @GlobalTheory.LevelHecke.loc_lk_eq_loc_cls | exact GlobalTheory.LevelHecke.loc_lk_eq_loc_cls | (intros; apply GlobalTheory.LevelHecke.loc_lk_eq_loc_cls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical

namespace GlobalTheory.LocWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idem (D : D7) : Pl D → AE D
  | .inl v => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin D v
  | .inr τ => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf D (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))

theorem idem_mul_self (v : Pl D) : idem D v * idem D v = idem D v := by
  rcases v with v | τ
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin]
    rw [← map_mul]
    congr 1
    refine Prod.ext (mul_zero _) ?_
    change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
    refine DFunLike.ext _ _ fun u => ?_
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F v 1) = evalV D.host.F u (singleV D.host.F v 1)
    rw [map_mul]
    by_cases h : u = v
    · subst h
      have : evalV D.host.F u (singleV D.host.F u 1) = 1 := RestrictedProduct.single_eq_same
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) u 1
      rw [this, mul_one]
    · have : evalV D.host.F u (singleV D.host.F v 1) = 0 := RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 h
      rw [this, mul_zero]
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf]
    rw [← map_mul]
    congr 1
    refine Prod.ext ?_ (mul_zero _)
    exact (Pi.single_mul (α := fun w : InfinitePlace D.host.F => w.Completion) _ 1 1).symm.trans (by rw [mul_one]; rfl)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem cA_idem (v : Pl D) : cA D (idem D v) = idem D v := by
  rcases v with v | τ <;> exact cA_algebraMap _

def cutGL {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) : GL (Fin n) R →* GL (Fin n) R :=
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun g => e • g + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun g h => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
        have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
          Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add] }
  Units.map f

theorem cutGL_val {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (g : GL (Fin n) R) :
    (cutGL he g).val = e • g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := rfl

theorem cutGL_mem {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (c : R →+* R) (hc : c e = e)
    (J : Matrix (Fin n) (Fin n) R) {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ c J) : cutGL he g ∈ Formalism.UG.UJ c J := by
  have hg' : Formalism.UG.cT c g.val * J * g.val = J := hg
  show Formalism.UG.cT c (cutGL he g).val * J * (cutGL he g).val = J
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : Formalism.UG.cT c (cutGL he g).val = e • Formalism.UG.cT c g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    simp only [cutGL_val, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, hc, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  rw [e1, cutGL_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
    Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add, hg']
  rw [← add_smul]; simp

def comp (V : HSp D) (v : Pl D) : GA D V →* GA D V :=
  ((cutGL (idem_mul_self v)).comp (matHom V)).codRestrict (HR (AF D.host.F) D.sp.cm.sig V.gram) fun g =>
    cutGL_mem (idem_mul_self v) (cA D) (cA_idem v) _ g.2

def GAt (V : HSp D) (v : Pl D) : Subgroup (GA D V) := (comp V v).range

def Gk (θ : InfF D) (V : HSp D) (A : CptF V) : Subgroup (GA D V) :=
  GfC V ⊔ Subgroup.closure {k | V.SigOK ∧ IsKinf θ V A k}

def KAt (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Subgroup (GA D V) := (Gk θ V A).map (comp V (.inr τ))

def OneP (V : HSp D) (τ : D.what₂.Tau) : Type :=
  {γ : Multiplicative ℝ →* GA D V // Continuous γ ∧ ∀ t, γ t ∈ GAt V (.inr τ)}

abbrev HAlg (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Type :=
  MonoidAlgebra ℂ (Monoid.Coprod (KAt θ V A τ) (FreeMonoid (OneP V τ)))

def ofK (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : KAt θ V A τ →* HAlg θ V A τ :=
  (MonoidAlgebra.of ℂ _).comp Monoid.Coprod.inl

def Hloc (θ : InfF D) (V : HSp D) (A : CptF V) : Pl D → Type
  | .inl v => GAt V (.inl v)
  | .inr τ => HAlg θ V A τ

instance (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Monoid (Hloc θ V A v)
  | .inl v => inferInstanceAs (Monoid (GAt V (.inl v)))
  | .inr τ => inferInstanceAs (Monoid (HAlg θ V A τ))

def loc (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Gk θ V A →* Hloc θ V A v
  | .inl v => (comp V (.inl v)).rangeRestrict.comp (Gk θ V A).subtype
  | .inr τ => (ofK θ V A τ).comp ((comp V (.inr τ)).subgroupMap (Gk θ V A))

def IsEvalAt (D : D7) (v : FinF D) (w : FinE D) (φ : AE D →+* v.adicCompletion (FF D)) : Prop :=
  (∀ a, φ (algebraMap (AF D.host.F) (AE D) a) = evalV D.host.F v (sndA D.host.F a)) ∧
    ∀ x : 𝓞 D.host.E, Valued.v (φ (incA D (x : D.host.E))) < 1 ↔ x ∈ w.asIdeal

structure SplitFrames (D : D7) where
  ev : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (AE D →+* v.adicCompletion (FF D))
  ev_spec : ∀ v w hv hw, IsEvalAt D v w (ev v w hv hw)
  ev_conj : ∀ v w w' hv hw hw', w' ≠ w → ∀ x, ev v w' hv hw' x = ev v w hv hw (cA D x)
  sc : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (v.adicCompletion (FF D))ˣ
  sc_spec : ∀ v w hv hw x, IntV v 0 (((sc v w hv hw)⁻¹ : (v.adicCompletion (FF D))ˣ) * x) ↔
    x ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {y | ∃ a ∈ D.host.AA, y = ev v w hv hw (incA D a)}
  fr : ∀ (V : HSp D) (v : FinF D) (w : FinE D), Split D v → Over D w v → GL (Fin V.rank) (v.adicCompletion (FF D))
  fr_spec : ∀ V v w hv hw y, (∀ i, IntV v 0 (((fr V v w hv hw)⁻¹).val.mulVec y i)) ↔
    y ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {z | ∃ x ∈ L0c D V, z = fun i => ev v w hv hw (incA D (x i))}
  fr_dual : ∀ V v w w' hv hw hw', w' ≠ w →
    (fr V v w' hv hw').valᵀ * V.gram.map (fun a => ev v w hv hw (incA D a)) * (fr V v w hv hw).val = 1

def SplitFrames.gl (Fr : SplitFrames D) (V : HSp D) (v : FinF D) (w : FinE D) (hw : Over D w v) :
    GAt V (.inl v) →* GL (Fin V.rank) (v.adicCompletion (FF D)) :=
  if hv : Split D v then
    (MulAut.conj (Fr.fr V v w hv hw)⁻¹).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (Fr.ev v w hv hw)).comp ((matHom V).comp (GAt V (.inl v)).subtype))
  else 1

variable {X : ThetaX D} {T : ThetaTied D X}

def Splitting (T : ThetaTied D X) (V W : HSp D) (χ χ' : X.Chr) : Prop :=
  ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank

structure PairData {Wl : WeilTied D X T} (K : KfinTied Wl) (θ : InfF D) (Fr : SplitFrames D) (V W : HSp D)
    (om : X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Type 1 where
  S : Pl D → Type
  [sA : ∀ v, AddCommGroup (S v)]
  [sM : ∀ v, Module ℂ (S v)]
  omL : X.Chr → X.Chr → ∀ v, Representation ℂ (Hloc θ V (K.cpt V) v × Hloc θ W (K.cpt W) v) (S v)
  vac : ∀ v, S v
  pure : (∀ v, S v) → X.Sch V W
  pure_span : Submodule.span ℂ {Φ | ∃ φ, Restr vac φ ∧ Φ = pure φ} = X.kfin V W
  pure_om : ∀ χ χ', Splitting T V W χ χ' → ∀ (g : Gk θ V (K.cpt V)) (h : Gk θ W (K.cpt W)) φ, Restr vac φ →
    om χ χ' ((g : GA D V), (h : GA D W)) (pure φ) = pure fun v => omL χ χ' v (loc θ V _ v g, loc θ W _ v h) (φ v)
  pure_mlin : ∀ φ v (c : ℂ) (x y : S v), Restr vac φ →
    pure (Function.update φ v (c • x + y)) = c • pure (Function.update φ v x) + pure (Function.update φ v y)
  linM : ∀ (v : FinF D) (w : FinE D), Over D w v →
    S (.inl v) →ₗ[ℂ] (Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ)
  linM_inj : ∀ v w (hw : Over D w v), Split D v → Function.Injective (linM v w hw)
  linM_eq : ∀ χ χ' v w (hw : Over D w v), Splitting T V W χ χ' → Split D v →
    ∀ g k : _, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, linM v w hw (omL χ χ' (.inl v) (g, k) φ) = c • fun (Xm : Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D))) =>
      linM v w hw φ (Units.val (Fr.gl V v w hw g)⁻¹ * Xm * (Units.val (Fr.gl W v w hw k)⁻¹).transpose)

attribute [instance] PairData.sA PairData.sM

end GlobalTheory.LocWeil

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimKKapAtWcPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeylDimPos

theorem weylDimU_pos {p : ℕ} (lam : Fin p → ℤ) (h : ∀ i j : Fin p, i ≤ j → lam j ≤ lam i) : 0 < weylDimU lam := by
  unfold weylDimU
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  have h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.2 (h i j hij.le)
  exact div_pos (by linarith) (by linarith)

theorem dimK_kapW_pos {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    0 < dimK p q (Formalism.L2.NTheta.kapW h p q) := by
  obtain ⟨h1, h2, -⟩ := Formalism.L2.NTheta.holOK_kapW h p q hpq
  exact mul_pos (weylDimU_pos _ fun i j hij => h1 i j hij) (weylDimU_pos _ fun i j hij => h2 i j hij)

theorem dimK_kapAt_pos {D : D7} (W : HSp D) (hW : W.SigOK) (hr : W.rank = D.R.r) (σ : D.what₂.LL →+* ℂ)
    (ρ : D.what₂.Tau) : 0 < dimK _ _ (kapAt W σ ρ) :=
  dimK_kapW_pos _ _ _ (by rw [← hr]; obtain ⟨e, -⟩ := hW (tauE D ρ); simpa using (Fintype.card_congr e).symm)

theorem dimK_kapAt_Wc_pos (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    0 < dimK _ _ (kapAt (Wc D i) σ ρ) :=
  dimK_kapAt_pos _ (D.sp.W_sig _) (D.sp.W_rank _ (by omega) (by have := i.2; omega)) σ ρ

end GlobalTheory.Mem.WeylDimPos
end

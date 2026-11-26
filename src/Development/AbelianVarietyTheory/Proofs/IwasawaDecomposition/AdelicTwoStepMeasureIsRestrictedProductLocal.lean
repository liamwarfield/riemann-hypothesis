module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElement
noncomputable section

namespace GlobalTheory.GaugeEx.LocComp

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
  (π : R ⊗[F] E →+* R' ⊗[F] E) (σ : E →ₐ[F] E)

theorem map_mulVec_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) (R ⊗[F] E)) (z : Fin n → R ⊗[F] E) :
    (fun i => π (A.mulVec z i)) = (A.map π).mulVec (fun i => π (z i)) := by
  funext i
  exact RingHom.map_mulVec π A z i

theorem map_smul_ratTup (hπ : ∀ e : E, π (inclR R e) = inclR R' e) {N n : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (x : Fin n → Fin N → E) (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π) :
    (fun a i => π ((g • ratTup (F := F) R x) a i)) = g' • ratTup (F := F) R' x := by
  funext a
  change (fun i => π ((HA.mat R σ J g).val.mulVec (fun j => inclR R (x a j)) i)) =
    (HA.mat R' σ J g').val.mulVec (fun j => inclR R' (x a j))
  rw [map_mulVec_eq, h]
  simp only [hπ]

theorem map_pairOf (hπ : ∀ e : E, π (inclR R e) = inclR R' e) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π)
    (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) :
    (fun a i => π (pairOf R σ J B y g y' a i)) =
      pairOf R' σ J B (fun a i => π (y a i)) g' (fun a i => π (y' a i)) := by
  have hB : (B.map (inclR (F := F) R)).map π = B.map (inclR (F := F) R') := by
    ext i j
    exact hπ _
  funext a
  fin_cases a
  · rfl
  · change (fun i => π ((HA.mat R σ J g).val.mulVec ((B.map (inclR (F := F) R)).mulVec (y' 0)) i)) =
      (HA.mat R' σ J g').val.mulVec ((B.map (inclR (F := F) R')).mulVec (fun i => π (y' 0 i)))
    rw [map_mulVec_eq, map_mulVec_eq, h, hB]

theorem map_inv {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π) :
    (HA.mat R' σ J g'⁻¹).val = (HA.mat R σ J g⁻¹).val.map π := by
  change ((HA.mat R' σ J g')⁻¹).val = ((HA.mat R σ J g)⁻¹).val.map π
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]

end BaseMap

theorem exists_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  intro F E _ _ _ _ _ σ d b M J x B g
  obtain ⟨⟨gi, hgi⟩, hv⟩ := (q_and_unitary_local_components F E σ (M + 1) J).2 g
  choose gv hgv using hv
  have hI : ∀ e : E, prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e :=
    qloc_incl (fstA F) prInf fun r e => rfl
  have hV : ∀ v (e : E), prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := fun v =>
    qloc_incl ((evalV F v).comp (sndA F)) (prV v) fun r e => rfl
  have hint := (GlobalTheory.GaugeEx.IntBasis.main F E σ d b).2.2.1
  refine ⟨gi, gv, map_smul_ratTup prInf σ hI J x g gi hgi,
    fun v => map_smul_ratTup (prV v) σ (hV v) J x g (gv v) (hgv v),
    fun y y' => map_pairOf prInf σ hI J B g gi hgi y y',
    fun v y y' => map_pairOf (prV v) σ (hV v) J B g (gv v) (hgv v) y y', ?_⟩
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  filter_upwards [hint ((HA.mat (AF F) σ J g).val i j), hint ((HA.mat (AF F) σ J g⁻¹).val i j)]
    with v h1 h2
  rw [map_inv (prV v) σ J g (gv v) (hgv v), hgv v]
  exact ⟨h1, h2⟩

end GlobalTheory.GaugeEx.LocComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElementStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_components_adelic_unitary_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  first | exact @GlobalTheory.GaugeEx.LocComp.exists_local_components | exact GlobalTheory.GaugeEx.LocComp.exists_local_components | (intros; apply GlobalTheory.GaugeEx.LocComp.exists_local_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSet
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeSetChange

theorem abstract_change {ι X Z : Type} [Countable ι] {Y : ι → Type} [MeasurableSpace X]
    [MeasurableSpace Z] [∀ v, MeasurableSpace (Y v)] (ν : Measure X) (mi : Measure Z)
    (mv : ∀ v, Measure (Y v)) (p : X → Z) (q : ∀ v, X → Y v) (hq : ∀ v, Measurable (q v))
    (S T S' : Finset ι) (A L : ∀ v, Set (Y v)) (c : ℝ≥0∞)
    (hS' : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) (hA : ∀ v, MeasurableSet (A v))
    (hL : ∀ v ∉ S', A v = L v)
    (H : ∀ (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x in {x | ∀ v ∉ S', q v x ∈ L v}, fi (p x) * ∏ v ∈ S', fv v (q v x) ∂ν =
        (∫⁻ y, fi y ∂mi) * (∏ v ∈ S', ∫⁻ y, fv v y ∂(mv v)) * c)
    (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞) (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ x in {x | ∀ v ∉ S, q v x ∈ A v}, fi (p x) * ∏ v ∈ S, fv v (q v x) ∂ν =
      (∫⁻ y, fi y ∂mi) * (∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * c) := by
  classical
  have hSeq : S' = S ∪ T := by
    ext v; rw [hS', Finset.mem_union]
  subst hSeq
  have hmeas : ∀ U : Finset ι, MeasurableSet {x | ∀ v ∉ U, q v x ∈ A v} := by
    intro U
    have : {x | ∀ v ∉ U, q v x ∈ A v} = ⋂ v, ⋂ (_ : v ∉ U), q v ⁻¹' A v := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hq v (hA v)
  let gv : ∀ v, Y v → ℝ≥0∞ := fun v => if v ∈ S then fv v else (A v).indicator 1
  have hgS : ∀ v ∈ S, gv v = fv v := fun v hv => if_pos hv
  have hgT : ∀ v ∈ T, gv v = (A v).indicator 1 := fun v hv =>
    if_neg (fun h => Finset.disjoint_left.mp hd h hv)
  have hgm : ∀ v, Measurable (gv v) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hgS v hv]; exact hfv v
    · have : gv v = (A v).indicator 1 := if_neg hv
      rw [this]; exact measurable_one.indicator (hA v)
  have h1 := H fi gv hfi hgm
  have hset : {x | ∀ v ∉ S ∪ T, q v x ∈ L v} = {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := by
    ext x
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    rw [hL v hv]
  rw [hset, Finset.prod_union hd, ← lintegral_indicator (hmeas _)] at h1
  have e1 : ∏ v ∈ S, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  have e2 : ∏ v ∈ T, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ T, mv v (A v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgT v hv]; exact lintegral_indicator_one (hA v)
  rw [e1, e2] at h1
  rw [← lintegral_indicator (hmeas _), ← mul_assoc, mul_assoc (∫⁻ y, fi y ∂mi), ← h1]
  refine lintegral_congr fun x => ?_
  have e3 : ∏ v ∈ S, gv v (q v x) = ∏ v ∈ S, fv v (q v x) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  by_cases hx : x ∈ {x | ∀ v ∉ S, q v x ∈ A v}
  · have hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := fun v hv =>
      hx v fun h => hv (Finset.mem_union_left _ h)
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Finset.prod_union hd, e3]
    have : ∏ v ∈ T, gv v (q v x) = 1 := Finset.prod_eq_one fun v hv => by
      rw [hgT v hv, Set.indicator_of_mem (hx v fun h => Finset.disjoint_left.mp hd h hv)]
      rfl
    rw [this, mul_one]
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v}
    · rw [Set.indicator_of_mem hx', Finset.prod_union hd]
      simp only [Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, hvA⟩ := hx
      have hvT : v ∈ T := by
        by_contra h
        exact hvA (hx' v (by simp [hvS, h]))
      have : ∏ v ∈ T, gv v (q v x) = 0 := Finset.prod_eq_zero hvT (by
        rw [hgT v hvT, Set.indicator_of_notMem hvA])
      rw [this, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem hx']

theorem product_formula_change_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  intro F E _ _ _ _ _ d b n M ν mi mv S T S' A hS' hd hA hL H fi fv hfi hfv
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2.2
  exact abstract_change ν mi mv projInf (fun v X => projV v (projFin X))
    (fun v => (hc v).measurable) S T S' A (fun v => latV b v) _ hS' hd hA hL H fi fv hfi hfv

end GlobalTheory.GaugeSetChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSetStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_change_sets_outside_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  first | exact @GlobalTheory.GaugeSetChange.product_formula_change_sets | exact GlobalTheory.GaugeSetChange.product_formula_change_sets | (intros; apply GlobalTheory.GaugeSetChange.product_formula_change_sets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupEleme
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupEleme
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.TwoStepIndep

theorem lintegral_pairOf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ M J x a B J' m' hS hinv y g k hgk f hf
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.FrameStep.frameStep F E σ hCM R M J x a B J' hS
  have hmem : k⁻¹ * g ∈ Hstab R σ J x := by
    have : (k⁻¹ * g) • ratTup (F := F) R x = ratTup (F := F) R x := by
      rw [mul_smul, hgk, inv_smul_smul]
    exact this
  have hrel : FrameRelR R σ J J' B (k⁻¹ * g) (e ⟨k⁻¹ * g, hmem⟩) := he ⟨k⁻¹ * g, hmem⟩
  set u := e ⟨k⁻¹ * g, hmem⟩ with hu
  have hkey : ∀ y', pairOf R σ J B y g y' = pairOf R σ J B y k (u • y') := by
    intro y'
    have hg : g = k * (k⁻¹ * g) := by group
    have h1 : ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
        ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
        ((HA.mat R σ J (k⁻¹ * g) : GL (Fin (M + 1)) (R ⊗[F] E)) :
          Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := by
      conv_lhs => rw [hg]
      rfl
    have h2 : (u • y') 0 = ((HA.mat R σ J' u : GL (Fin M) (R ⊗[F] E)) :
        Matrix _ _ (R ⊗[F] E)).mulVec (y' 0) := rfl
    unfold FrameRelR at hrel
    unfold pairOf
    rw [h1, h2]
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc]
    exact congrArg (fun A : Matrix (Fin (M + 1)) (Fin M) (R ⊗[F] E) =>
      (![y 0, (((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A).mulVec (y' 0)] :
          Fin 2 → Fin (M + 1) → R ⊗[F] E)) hrel
  have hc : Continuous fun y' => pairOf R σ J B y k y' := by
    refine continuous_pi ?_
    rw [Fin.forall_fin_two]
    refine ⟨continuous_const, ?_⟩
    have h0 : Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E => y' 0 := continuous_apply 0
    show Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec ((B.map (inclR R)).mulVec (y' 0))
    exact continuous_const.matrix_mulVec (continuous_const.matrix_mulVec h0)
  have hm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => u • X :=
    (continuous_const_smul u).measurable
  simp_rw [hkey]
  conv_rhs => rw [← hinv u]
  exact (lintegral_map (hf.comp hc.measurable) hm).symm

end GlobalTheory.TwoStepIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupElemeStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  first | exact @GlobalTheory.TwoStepIndep.lintegral_pairOf_eq | exact GlobalTheory.TwoStepIndep.lintegral_pairOf_eq | (intros; apply GlobalTheory.TwoStepIndep.lintegral_pairOf_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductTailSplitFiniteFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductTailSplitFiniteFactors
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.TailSplit

theorem tprod_split {ι : Type} (a : ι → ℝ) (ha : Summable fun v => |a v - 1|) (S T S' : Finset ι)
    (h : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) :
    ∏' v : {v : ι // v ∉ S}, a v.1 = (∏ v ∈ T, a v) * ∏' v : {v : ι // v ∉ S'}, a v.1 := by
  classical
  have e1 : ∏' v : {v : ι // v ∉ S}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : ∏' v : {v : ι // v ∉ S'}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have m2 : Multipliable fun v => Set.mulIndicator {v | v ∉ S'} a v := by
    have : Summable fun v => ‖Set.mulIndicator {v | v ∉ S'} a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) ha
      by_cases hv : v ∈ S'
      · simp [Set.mulIndicator, hv]
      · simp [Set.mulIndicator, hv]
    simpa using multipliable_one_add_of_summable this
  have m1 : HasProd (fun v => Set.mulIndicator (T : Set ι) a v) (∏ v ∈ T, a v) := by
    have : HasProd (fun v => Set.mulIndicator (T : Set ι) a v)
        (∏ v ∈ T, Set.mulIndicator (T : Set ι) a v) :=
      hasProd_prod_of_ne_finset_one fun v hv => by simp [Set.mulIndicator, hv]
    rwa [Finset.prod_congr rfl (fun v hv => Set.mulIndicator_of_mem (by simpa using hv) a)] at this
  rw [e1, e2, ← (m1.mul m2.hasProd).tprod_eq]
  refine tprod_congr fun v => ?_
  by_cases hS : v ∈ S
  · have hT : v ∉ T := Finset.disjoint_left.1 hd hS
    simp [Set.mulIndicator, h, hS, hT]
  · by_cases hT : v ∈ T <;> simp [Set.mulIndicator, h, hS, hT]

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → tailProd b mv S = (∏ v ∈ T, mv v (latV b v)) * tailProd b mv S' := by
  intro F E _ _ _ _ _ d b n M mi mv S T S' hc h hd
  obtain ⟨-, hfin, hsum⟩ := hc
  have hne : ∀ v, mv v (latV b v) ≠ ∞ := by
    intro v
    have hk : IsCompact (intV b v) :=
      ((GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b).1 v).1
    have hk2 : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
      have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
          Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
        ext Y
        rw [mem_latV_iff]
        simp [Set.mem_pi]
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hk
    have := hfin v
    exact hk2.measure_lt_top.ne
  unfold tailProd
  rw [tprod_split (fun v => (mv v (latV b v)).toReal) hsum S T S' h hd,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hne v)

end GlobalTheory.GaugeEx.TailSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductTailSplitFiniteFactorsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProduct_tail_split_finite_factors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → tailProd b mv S = (∏ v ∈ T, mv v (latV b v)) * tailProd b mv S' := by
  first | exact @GlobalTheory.GaugeEx.TailSplit.main | exact GlobalTheory.GaugeEx.TailSplit.main | (intros; apply GlobalTheory.GaugeEx.TailSplit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegralOrthogonalComplementPair
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegralOrthogonalComplementPair
noncomputable section

namespace GlobalTheory.GaugeEx.PairLat

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem ev_incl (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    inclR (Fv F v) e ∈ intV b v := by
  filter_upwards [IntBasis.ev_int_coord b e] with v hv
  exact IntBasis.tmul_mem b v (one_mem _) hv

theorem ev_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, A.map (inclR (Fv F v)) i j ∈ intV b v :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_incl b (A i j)

theorem mulVec_mem (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ intV b v)
    (w : Fin n → Fv F v ⊗[F] E) (hw : ∀ j, w j ∈ intV b v) (i : Fin m) :
    A.mulVec w i ∈ intV b v := by
  have h : A.mulVec w i = ∑ j, A i j * w j := rfl
  rw [h]
  exact IntBasis.sum_mem' b v Finset.univ (fun j => A i j * w j) fun j _ => hm _ (hA i j) _ (hw j)

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : HA (Fv F v) σ J, (∀ i j, (HA.mat (Fv F v) σ J k).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J (k)⁻¹).val i j ∈ intV b v) → ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (y' : Fin 1 → Fin M → Fv F v ⊗[F] E), pairOf (Fv F v) σ J B y k y' ∈ latV b v ↔ y ∈ latV b v ∧ y' ∈ latV b v := by
  intro F E _ _ _ _ _ σ d b M J x a B J' hS
  obtain ⟨-, -, -, -, hJ', hH⟩ := hS
  have hdet : J'.det ≠ 0 := hH.2
  set C : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J) with hC
  have hCB : C * B = 1 := by
    rw [hC, Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  filter_upwards [(IntBasis.main F E σ d b).2.1, ev_map b B, ev_map b C] with v hv hB hCv k hk y y'
  have hm := hv.2.1
  simp only [mem_latV_iff, Fin.forall_fin_two, Fin.forall_fin_one]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := mulVec_mem b v hm _ hCv _ (mulVec_mem b v hm _ (fun i j => (hk i j).2) _ h)
    have h2 : (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        (pairOf (Fv F v) σ J B y k y' 1)) = y' 0 := by
      change (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        ((HA.mat (Fv F v) σ J k).val.mulVec ((B.map (inclR (Fv F v))).mulVec (y' 0)))) = y' 0
      rw [Matrix.mulVec_mulVec _ _ (HA.mat (Fv F v) σ J k).val, Units.inv_mul, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    intro i
    rw [← h2]
    exact h1 i
  · exact mulVec_mem b v hm _ (fun i j => (hk i j).1) _ (mulVec_mem b v hm _ hB _ h)

end GlobalTheory.GaugeEx.PairLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegralOrthogonalComplementPairStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_orthogonalComplement_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : HA (Fv F v) σ J, (∀ i j, (HA.mat (Fv F v) σ J k).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J (k)⁻¹).val i j ∈ intV b v) → ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (y' : Fin 1 → Fin M → Fv F v ⊗[F] E), pairOf (Fv F v) σ J B y k y' ∈ latV b v ↔ y ∈ latV b v ∧ y' ∈ latV b v := by
  first | exact @GlobalTheory.GaugeEx.PairLat.main | exact GlobalTheory.GaugeEx.PairLat.main | (intros; apply GlobalTheory.GaugeEx.PairLat.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousUnitaryTwoStepVectorAndTranslatePair
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousUnitaryTwoStepVectorAndTranslatePair
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem continuous_pairOf_joint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E), Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  intro F E _ _ _ _ _ σ R _ _ _ _ M J B
  refine continuous_pi (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · exact (continuous_apply (0 : Fin 1)).comp continuous_fst
  · exact ((continuous_mat R σ J).comp (continuous_fst.comp continuous_snd)).matrix_mulVec
      (continuous_const.matrix_mulVec
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousUnitaryTwoStepVectorAndTranslatePairStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E), Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  first | exact @GlobalTheory.GaugeEx.continuous_pairOf_joint | exact GlobalTheory.GaugeEx.continuous_pairOf_joint | (intros; apply GlobalTheory.GaugeEx.continuous_pairOf_joint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEq
noncomputable section

namespace GlobalTheory.GaugeEx.OrbitQuadric

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_of_cT_mul_mul_eq {A : Type} [CommRing A] (s : A →+* A)
    (G g : Matrix (Fin M) (Fin M) A) (hg : Formalism.UG.cT s g * G * g = G) (x y : Fin M → A) :
    Formalism.UG.hform s G (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform s G x y := by
  have hc : Formalism.UG.cT s g = (g.map s)ᵀ := by
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; simp)
  rw [hc] at hg
  have hs : (fun i => s ((g *ᵥ x) i)) = (g.map s) *ᵥ (fun i => s (x i)) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [hform_eq_dot, hform_eq_dot, hs, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose (g.map s) (fun i => s (x i)),
    ← Matrix.dotProduct_mulVec (fun i => s (x i)) (g.map s)ᵀ ((G * g) *ᵥ y),
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem hR_act (k : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J k).1 *ᵥ x) ((HA.mat R σ J k).1 *ᵥ y) = hR R σ J x y := by
  have hk : HA.mat R σ J k ∈ HR R σ J := (k : HR R σ J).2
  unfold HR Formalism.UG.UJ at hk
  have hk' : Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 * JR R J * (HA.mat R σ J k).1 = JR R J := hk
  unfold hR
  exact hform_mulVec_mulVec_of_cT_mul_mul_eq (sigR R σ) (JR R J) _ hk' x y

theorem hR_rat (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = (1 : R) ⊗ₜ[F] hE σ J x z := by
  unfold hR hE JR
  rw [hform_eq_dot, hform_eq_dot]
  show _ = inclR R _
  rw [RingHom.map_dotProduct]
  congr 1
  all_goals funext i
  all_goals first
    | exact (RingHom.map_mulVec (inclR R) J z i).symm
    | simp [sigR, inclR]

end Form

theorem qR_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  intro F E _ _ _ _ _ σ hcm R _ _ M J x a hx g
  have hfin : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  have hact : (g • ratTup (F := F) R x) 0 = (HA.mat R σ J g).1 *ᵥ (fun i => inclR R (x 0 i)) := rfl
  rw [hact]
  unfold qR
  rw [hR_act R σ J g, hR_rat R σ J (x 0) (x 0), hx]
  have h2 : (1 : R) ⊗ₜ[F] algebraMap F E a = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]
    exact (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)).commutes a
  rw [h2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasis F E)) (algebraMap F R a),
    Fintype.card_fin, hcm.2.2.1, nsmul_eq_mul, ← mul_assoc]
  have h3 : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [h3, one_mul]

end GlobalTheory.GaugeEx.OrbitQuadric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEqStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  first | exact @GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit | exact GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit | (intros; apply GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMul
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem summable_abs_mul_sub_one {ι : Type} {a a' : ι → ℝ} (ha : Summable fun v => |a v - 1|)
    (ha' : Summable fun v => |a' v - 1|) : Summable fun v => |a v * a' v - 1| := by
  have h1 : Summable fun v => |a v - 1| * |a' v - 1| := by
    refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
      (ha.mul_right (∑' w, |a' w - 1|))
    exact mul_le_mul_of_nonneg_left (ha'.le_tsum v fun w _ => abs_nonneg _) (abs_nonneg _)
  refine Summable.of_nonneg_of_le (fun v => abs_nonneg _) (fun v => ?_) ((h1.add ha).add ha')
  have : a v * a' v - 1 = (a v - 1) * (a' v - 1) + (a v - 1) + (a' v - 1) := by ring
  rw [this, ← abs_mul]
  exact abs_add_three _ _ _

theorem multipliable_subtype_of_summable_abs {ι : Type} {a : ι → ℝ}
    (ha : Summable fun v => |a v - 1|) (p : ι → Prop) :
    Multipliable fun v : {v // p v} => a v.1 := by
  have h : Summable fun v : {v // p v} => (a v.1 - 1) :=
    (Summable.of_abs ha).comp_injective Subtype.val_injective
  have := Real.multipliable_one_add_of_summable h
  simpa using this

theorem tprod_nonneg_of_multipliable {ι : Type} {a : ι → ℝ} (ha : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v :=
  ge_of_tendsto' ha.hasProd fun _ => Finset.prod_nonneg fun v _ => h0 v

theorem tailProd_mul_of_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  intro F E _ _ _ _ _ d b n₁ M₁ n₂ M₂ n₃ M₃ mi mv mi' mv' Nv S₀ h h' hN
  refine ⟨?_, fun S hS => ?_⟩
  · refine (summable_abs_mul_sub_one h.2.2 h'.2.2).congr_cofinite ?_
    filter_upwards [S₀.eventually_cofinite_notMem] with v hv
    rw [hN v hv, ENNReal.toReal_mul]
  · have m := multipliable_subtype_of_summable_abs h.2.2 (fun v => v ∉ S)
    have m' := multipliable_subtype_of_summable_abs h'.2.2 (fun v => v ∉ S)
    unfold tailProd
    rw [← ENNReal.ofReal_mul (tprod_nonneg_of_multipliable m fun _ => ENNReal.toReal_nonneg),
      ← m.tprod_mul m']
    congr 1
    refine tprod_congr fun v => ?_
    rw [hN v.1 (fun hv => v.2 (hS hv)), ENNReal.toReal_mul]

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMulStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tailProd_mul_of_lattice_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  first | exact @GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | exact GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | (intros; apply GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureIsRestrictedProductLocal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.TsProd

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem measurableSet_latV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (n M : ℕ) :
    MeasurableSet (latV (n := n) (M := M) b v) := by
  have h := ((GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E σ d b).1 v).2
  have : latV (n := n) (M := M) b v = ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
    ext Y; simp [mem_latV_iff]
  rw [this]
  refine IsOpen.measurableSet ?_
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => h.preimage (by fun_prop)

theorem isProd_of_large (σ : E →ₐ[F] E) {n M : ℕ} (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (hc : Conv b mi mv)
    (h : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), S₀ ⊆ S →
      ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
      (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v},
        fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν =
      (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S) :
    IsProd b ν mi mv := by
  classical
  refine ⟨hc, fun S fi fv hfi hfv => ?_⟩
  have h1 : ∀ v, v ∈ S ∪ S₀ ↔ v ∈ S ∨ v ∈ S₀ \ S := by intro v; simp; tauto
  have h2 : Disjoint S (S₀ \ S) := Finset.disjoint_sdiff
  rw [GlobalTheory.T.restrictedProduct_tail_split_finite_factors F E d b n M mi mv S (S₀ \ S) (S ∪ S₀) hc h1 h2]
  exact GlobalTheory.T.product_formula_change_sets_outside_finite_set F E d b n M ν mi mv S (S₀ \ S) (S ∪ S₀) (fun v => latV b v) h1 h2
    (fun v => measurableSet_latV b σ v n M) (fun _ _ => rfl)
    (h _ Finset.subset_union_right) fi fv hfi hfv

theorem isProd_sets {n M : ℕ} {ν : Measure (Fin n → Fin M → AF F ⊗[F] E)}
    {mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsProd b ν mi mv) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hAe : ∀ᶠ v in Filter.cofinite, A v = latV b v)
    (hAm : ∀ v ∉ S, mv v (A v) = mv v (latV b v))
    (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞)
    (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v},
        fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν =
      (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S := by
  classical
  have hfin : {v | ¬ A v = latV b v}.Finite := hAe
  set S₀ := hfin.toFinset with hS₀
  have h1 : ∀ v, v ∈ S ∪ S₀ ↔ v ∈ S ∨ v ∈ S₀ \ S := by intro v; simp; tauto
  have h2 : Disjoint S (S₀ \ S) := Finset.disjoint_sdiff
  rw [GlobalTheory.T.restrictedProduct_tail_split_finite_factors F E d b n M mi mv S (S₀ \ S) (S ∪ S₀) h.1 h1 h2,
    GlobalTheory.T.product_formula_change_sets_outside_finite_set F E d b n M ν mi mv S (S₀ \ S) (S ∪ S₀) A h1 h2 hA
    (fun v hv => by
      by_contra hne
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne)))
    (h.2 _) fi fv hfi hfv]
  congr 2
  exact Finset.prod_congr rfl fun v hv => hAm v (Finset.mem_sdiff.1 hv).2

include b in
theorem measurableSet_cyl {n M : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ A v} := by
  have hc : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have : {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ A v} =
      ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' A v := by
    ext X; simp
  rw [this]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    ((GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M).2.2.2 v).measurable (hA v)

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
  {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}

section
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem measurable_pair (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g : HA R σ J) :
    Measurable fun y' => pairOf R σ J B y g y' :=
  ((GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair F E σ R M J B).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).measurable

theorem exists_sec (x : Fin 1 → Fin (M + 1) → E) :
    MeasurableSet {y : Fin 1 → Fin (M + 1) → R ⊗[F] E | ∃ g : HA R σ J, g • ratTup (F := F) R x = y} ∧
    ∃ s, IsSec R σ J x s ∧ ∀ (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsFiniteMeasureOnCompacts m' →
      ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f →
        Measurable fun y => ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' := by
  obtain ⟨h1, s, hs, hs'⟩ := GlobalTheory.T.measurableSet_orbit_exists_measurable_section (HA R σ J) (Fin 1 → Fin (M + 1) → R ⊗[F] E) (ratTup (F := F) R x)
  refine ⟨h1, s, hs', fun m' hm' f hf => ?_⟩
  have hm : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin 1 → Fin M → R ⊗[F] E) =>
      f (pairOf R σ J B p.1 (s p.1) p.2) :=
    hf.comp ((GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair F E σ R M J B).measurable.comp
      (measurable_fst.prodMk ((hs.comp measurable_fst).prodMk measurable_snd)))
  exact hm.lintegral_prod_right'

end

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem fst_mem {v : HeightOneSpectrum (𝓞 F)} {y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E}
    {g : HA (Fv F v) σ J} {y' : Fin 1 → Fin M → Fv F v ⊗[F] E}
    (h : pairOf (Fv F v) σ J B y g y' ∈ latV b v) : y ∈ latV b v := by
  intro c i k
  have := h 0 i k
  rw [Subsingleton.elim c 0]
  exact this

theorem good_ae (hCM : IsCMExt F E σ) (hS : StepData σ J x a B J') :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ m' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), IsInvTup (Fv F v) σ J' m' →
      ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
        g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
        m' {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = m' (latV b v) := by
  filter_upwards [GlobalTheory.T.eventually_integral_orthogonalComplement_pair F E σ d b M J x a B J' hS,
    GlobalTheory.T.integral_witt_theorem_almost_all_places F E σ hCM d b (M + 1) J x a hS.1 hS.2.1 hS.2.2.1] with v h1 h2 m' hm' y g hg hy
  obtain ⟨k, hk, hk'⟩ := h2 y hy (hg ▸ GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq F E σ hCM _ _ J x a hS.2.2.1 g)
  have hL := measurableSet_latV b σ v 2 (M + 1)
  have h3 := GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement F E σ hCM (Fv F v) M J x a B J' m' hS hm' y g k (hg.trans hk.symm)
    ((latV b v).indicator 1) (measurable_one.indicator hL)
  have h4 : ∀ g : HA (Fv F v) σ J, ∫⁻ y', (latV b v).indicator (1 : (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (pairOf (Fv F v) σ J B y g y') ∂m' =
      m' {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} := by
    intro g
    exact lintegral_indicator_one (measurable_pair (B := B) (Fv F v) y g hL)
  rw [h4, h4] at h3
  rw [h3]
  congr 1
  ext y'
  simp [h1 k hk' y y', hy]

theorem mass_mul {v : HeightOneSpectrum (𝓞 F)} {m : Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)}
    {m' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)} {N : Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)}
    (hm : OnOrbit (Fv F v) σ J x m) (hN : TwoStep (Fv F v) σ J x B m m' N)
    (h : ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
        g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
        m' {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = m' (latV b v)) :
    N (latV b v) = m (latV b v) * m' (latV b v) := by
  obtain ⟨-, s, hs, -⟩ := exists_sec (σ := σ) (J := J) (B := B) (Fv F v) x
  have hL := measurableSet_latV b σ v 2 (M + 1)
  have h1 := hN ((latV b v).indicator 1) (measurable_one.indicator hL) s hs
  rw [lintegral_indicator_one hL] at h1
  rw [h1, mul_comm, ← setLIntegral_const, ← lintegral_indicator (measurableSet_latV b σ v 1 (M + 1))]
  refine lintegral_congr_ae ?_
  have hm' : ∀ᵐ y ∂m, ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y := hm
  filter_upwards [hm'] with y hy
  have h4 : ∫⁻ y', (latV b v).indicator (1 : (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (pairOf (Fv F v) σ J B y (s y) y') ∂m' =
      m' {y' | pairOf (Fv F v) σ J B y (s y) y' ∈ latV b v} := by
    exact lintegral_indicator_one (measurable_pair (B := B) (Fv F v) y (s y) hL)
  rw [h4]
  by_cases hyL : y ∈ latV b v
  · rw [Set.indicator_of_mem hyL, h y (s y) (hs y hy) hyL]
  · rw [Set.indicator_of_notMem hyL]
    have : {y' | pairOf (Fv F v) σ J B y (s y) y' ∈ latV b v} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y' hy' => hyL (fst_mem b hy')
    rw [this, measure_empty]

theorem adelic_orbit (hCM : IsCMExt F E σ) (hS : StepData σ J x a B J')
    {ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)}
    {mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)}
    {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)}
    (h : IsProd b ν mi mv) (hi : OnOrbit (Ainf F) σ J x mi) (hv : ∀ v, OnOrbit (Fv F v) σ J x (mv v)) :
    ∀ᵐ y ∂ν, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  have h1 := (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 (M + 1) ν mi mv h).2.2.2
    {y | ∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) x = y}
    (fun v => {y | ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y})
    (exists_sec (σ := σ) (J := J) (B := B) (Ainf F) x).1
    (fun v => (exists_sec (σ := σ) (J := J) (B := B) (Fv F v) x).1) hi hv
  have h2 : ∀ᵐ y ∂ν, projInf y ∈ {y | ∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) x = y} ∧
      ∀ v, projV v (projFin y) ∈ {y | ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y} := h1
  filter_upwards [h2] with y ⟨⟨gi, hgi⟩, hy⟩
  refine GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM (M + 1) J x a hS.1 hS.2.1 hS.2.2.1 y ?_
  refine ((q_and_unitary_local_components F E σ (M + 1) J).1 (y 0) a).2 ⟨?_, fun v => ?_⟩
  · have := GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq F E σ hCM _ _ J x a hS.2.2.1 gi
    rw [hgi] at this
    exact this
  · obtain ⟨g, hg⟩ := hy v
    have := GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq F E σ hCM _ _ J x a hS.2.2.1 g
    rw [hg] at this
    exact this

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
  {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem inner_eq (hCM : IsCMExt F E σ) (hS : StepData σ J x a B J')
    {ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)}
    {mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)}
    {mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}
    (h : IsProd b ν' mi' mv') (hi : IsInvTup (Ainf F) σ J' mi') (hv : ∀ v, IsInvTup (Fv F v) σ J' (mv' v))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hg : ∀ v ∉ S, ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
        g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
        mv' v {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = mv' v (latV b v))
    (fi : (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v))
    {si : _} (hsi : IsSec (Ainf F) σ J x si)
    {sv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → HA (Fv F v) σ J}
    (hsv : ∀ v, IsSec (Fv F v) σ J x (sv v))
    (y : Fin 1 → Fin (M + 1) → AF F ⊗[F] E) (g : HA (AF F) σ J)
    (hy : g • ratTup (F := F) (AF F) x = y) :
    ∫⁻ y', {X : Fin 2 → Fin (M + 1) → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}.indicator
        (fun X => fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X))) (pairOf (AF F) σ J B y g y') ∂ν' =
      {X : Fin 1 → Fin (M + 1) → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}.indicator
        (fun X => (∫⁻ y', fi (pairOf (Ainf F) σ J B (projInf X) (si (projInf X)) y') ∂mi') *
          ∏ v ∈ S, ∫⁻ y', fv v (pairOf (Fv F v) σ J B (projV v (projFin X)) (sv v (projV v (projFin X))) y')
            ∂(mv' v)) y * tailProd b mv' S := by
  obtain ⟨gi, gv, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_local_components_adelic_unitary_element F E σ d b M J x B g
  rw [hy] at h1 h2
  by_cases hyL : y ∈ {X : Fin 1 → Fin (M + 1) → AF F ⊗[F] E | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}
  · rw [Set.indicator_of_mem hyL]
    have hA : ∀ v, MeasurableSet {y' | pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) y' ∈ latV b v} :=
      fun v => measurable_pair (Fv F v) _ _ (measurableSet_latV b σ v 2 (M + 1))
    have key := isProd_sets b h S
      (fun v => {y' | pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) y' ∈ latV b v}) hA
      (by
        filter_upwards [GlobalTheory.T.eventually_integral_orthogonalComplement_pair F E σ d b M J x a B J' hS, h5, S.finite_toSet.compl_mem_cofinite]
          with v e1 e2 e3
        ext y'
        simp [e1 _ e2, hyL v e3])
      (fun v hv => hg v hv _ _ (h2 v).symm (hyL v hv))
      (fun y' => fi (pairOf (Ainf F) σ J B (projInf y) gi y'))
      (fun v y' => fv v (pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) y'))
      (hfi.comp (measurable_pair (Ainf F) _ _)) (fun v => (hfv v).comp (measurable_pair (Fv F v) _ _))
    rw [← GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement F E σ hCM (Ainf F) M J x a B J' mi' hS hi (projInf y) gi _
      (h1.symm.trans (hsi _ ⟨gi, h1.symm⟩).symm) fi hfi,
      Finset.prod_congr rfl fun v _ => (GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement F E σ hCM (Fv F v) M J x a B J' (mv' v) hS (hv v)
        (projV v (projFin y)) (gv v) _ ((h2 v).symm.trans (hsv v _ ⟨gv v, (h2 v).symm⟩).symm)
        (fv v) (hfv v)).symm, ← key, ← lintegral_indicator (measurableSet_cyl b S _ hA)]
    refine lintegral_congr fun y' => ?_
    by_cases hq : ∀ v ∉ S, pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y')) ∈ latV b v
    · rw [Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq, h4] using hq),
        Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq] using hq)]
      simp only [h3, h4]
    · rw [Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq, h4] using hq),
        Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq] using hq)]
  · rw [Set.indicator_of_notMem hyL, zero_mul]
    refine (lintegral_congr fun y' => ?_).trans lintegral_zero
    refine Set.indicator_of_notMem (fun hm => hyL fun v hv => ?_) _
    have := hm v hv
    rw [h4] at this
    exact fst_mem b this

end

theorem twoStep_isProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)) (Ni : Measure (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)), StepData σ J x a B J' → IsProd b ν mi mv → IsProd b ν' mi' mv' → OnOrbit (Ainf F) σ J x mi → (∀ v, OnOrbit (Fv F v) σ J x (mv v)) → IsInvTup (Ainf F) σ J' mi' → (∀ v, IsInvTup (Fv F v) σ J' (mv' v)) → TwoStep (Ainf F) σ J x B mi mi' Ni → (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) → TwoStep (AF F) σ J x B ν ν' N → IsProd b N Ni Nv := by
  intro F E _ _ _ _ _ σ hCM d b M J x a B J' ν mi mv ν' mi' mv' N Ni Nv hS hν hν' hoi hov hii hiv
    hNi hNv hN
  have hfin := Filter.eventually_cofinite.1 (good_ae b hCM hS)
  have hg : ∀ v ∉ hfin.toFinset, ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (g : HA (Fv F v) σ J),
      g • ratTup (F := F) (Fv F v) x = y → y ∈ latV b v →
      mv' v {y' | pairOf (Fv F v) σ J B y g y' ∈ latV b v} = mv' v (latV b v) := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
    exact hv _ (hiv v)
  obtain ⟨hsum, htail⟩ := GlobalTheory.T.tailProd_mul_of_lattice_mass_mul F E d b _ _ _ _ _ _ mi mv mi' mv' Nv hfin.toFinset hν.1 hν'.1
    (fun v hv => mass_mul b (hov v) (hNv v) (hg v hv))
  have hnice := nice_ainf_fv F
  refine isProd_of_large b σ N Ni Nv hfin.toFinset
    ⟨GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hCM (Ainf F) hnice.1 M J x a B J' mi mi' Ni hS hoi hν.1.1 hν'.1.1 hii hNi,
     fun v => GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hCM (Fv F v) (hnice.2 v) M J x a B J' (mv v) (mv' v) (Nv v) hS (hov v)
      (hν.1.2.1 v) (hν'.1.2.1 v) (hiv v) (hNv v), hsum⟩ fun S hSS fi fv hfi hfv => ?_
  obtain ⟨-, s, hs, -⟩ := exists_sec (σ := σ) (J := J) (B := B) (AF F) x
  obtain ⟨-, si, hsi, hsi'⟩ := exists_sec (σ := σ) (J := J) (B := B) (Ainf F) x
  choose sv hsv hsv' using fun v : HeightOneSpectrum (𝓞 F) =>
    (exists_sec (σ := σ) (J := J) (B := B) (Fv F v) x).2
  have hG := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b 2 (M + 1)
  have hG1 := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b 1 (M + 1)
  have hc2 := measurableSet_cyl b S _ fun v => measurableSet_latV b σ v 2 (M + 1)
  have hc1 := measurableSet_cyl b S _ fun v => measurableSet_latV b σ v 1 (M + 1)
  have hFi := hsi' mi' hν'.1.1 fi hfi
  have hFv := fun v => hsv' v (mv' v) (hν'.1.2.1 v) (fv v) (hfv v)
  have hm : Measurable fun X : Fin 2 → Fin (M + 1) → AF F ⊗[F] E =>
      fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) :=
    (hfi.comp hG.2.2.1.measurable).mul
      (Finset.measurable_prod _ fun v _ => (hfv v).comp (hG.2.2.2 v).measurable)
  rw [← lintegral_indicator hc2, hN _ (hm.indicator hc2) s hs, hNi fi hfi si hsi,
    Finset.prod_congr rfl fun v _ => hNv v (fv v) (hfv v) (sv v) (hsv v), htail S hSS, ← mul_assoc,
    ← hν.2 S _ _ hFi hFv, ← lintegral_indicator hc1, ← lintegral_mul_const' (tailProd b mv' S) _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [adelic_orbit b hCM hS hν hoi hov] with y hy
  exact inner_eq b hCM hS hν' hii hiv S (fun v hv => hg v fun h => hv (hSS h)) fi fv hfi hfv hsi hsv
    y (s y) (hs y hy)

end GlobalTheory.GaugeEx.TsProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureIsRestrictedProductLocalStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTwoStepMeasure_isRestrictedProduct_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (mi : Measure (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (mi' : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)) (Ni : Measure (Fin 2 → Fin (M + 1) → Ainf F ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)), StepData σ J x a B J' → IsProd b ν mi mv → IsProd b ν' mi' mv' → OnOrbit (Ainf F) σ J x mi → (∀ v, OnOrbit (Fv F v) σ J x (mv v)) → IsInvTup (Ainf F) σ J' mi' → (∀ v, IsInvTup (Fv F v) σ J' (mv' v)) → TwoStep (Ainf F) σ J x B mi mi' Ni → (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) → TwoStep (AF F) σ J x B ν ν' N → IsProd b N Ni Nv := by
  first | exact @GlobalTheory.GaugeEx.TsProd.twoStep_isProd | exact GlobalTheory.GaugeEx.TsProd.twoStep_isProd | (intros; apply GlobalTheory.GaugeEx.TsProd.twoStep_isProd <;> assumption)
end

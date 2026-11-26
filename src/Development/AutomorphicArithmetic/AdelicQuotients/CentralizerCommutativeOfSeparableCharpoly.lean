module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.CentralizerCommutativeOfSeparableCharpoly
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem coord_comm {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (φ : R →ₗ[F] F) (s : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s) :
    Commute (s.map φ) γ := by
  have hl : ∀ (r : R) (x : F), φ (r * algebraMap F R x) = φ r * x := by
    intro r x
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hr : ∀ (r : R) (x : F), φ (algebraMap F R x * r) = x * φ r := by
    intro r x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  show s.map φ * γ = γ * s.map φ
  ext a c
  have h := congrArg φ (congrFun (congrFun hs a) c)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, hl, hr] using h

private theorem coord_sum {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (b : Module.Basis ι F R) (B : Finset ι) (s : Matrix (Fin n) (Fin n) R)
    (hB : ∀ a c, (b.repr (s a c)).support ⊆ B) :
    s = ∑ i ∈ B, b i • (s.map (b.coord i)).map (algebraMap F R) := by
  ext a c
  rw [Matrix.sum_apply]
  conv_lhs => rw [← b.linearCombination_repr (s a c)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hB a c) _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

private theorem sum_comm_of {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (e : ι → R) (B : Finset ι) (S T : ι → Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, S i * T j = T j * S i) :
    (∑ i ∈ B, e i • (S i).map (algebraMap F R)) * (∑ j ∈ B, e j • (T j).map (algebraMap F R)) =
      (∑ j ∈ B, e j • (T j).map (algebraMap F R)) * (∑ i ∈ B, e i • (S i).map (algebraMap F R)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (e i), ← Matrix.map_mul, ← Matrix.map_mul, h]

private theorem comm_alg {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (hγ : γ.charpoly.Separable) (s t : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s)
    (ht : t * γ.map (algebraMap F R) = γ.map (algebraMap F R) * t) : s * t = t * s := by
  classical
  let b := Module.Basis.ofVectorSpace F R
  let B := Finset.univ.biUnion fun a => Finset.univ.biUnion fun c =>
    (b.repr (s a c)).support ∪ (b.repr (t a c)).support
  have hsB : ∀ a c, (b.repr (s a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_left _ hi⟩⟩
  have htB : ∀ a c, (b.repr (t a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_right _ hi⟩⟩
  have h := sum_comm_of (R := R) (fun i => b i) B (fun i => s.map (b.coord i))
    (fun i => t.map (b.coord i)) fun i j =>
      (UpperTheory.V.Z.Tf.Orb.centComm F n γ _ _ hγ (coord_comm γ _ s hs) (coord_comm γ _ t ht)).eq
  rwa [← coord_sum b B s hsB, ← coord_sum b B t htB] at h

theorem UpperTheory.centralizer_commutative_of_separable_charpoly :
    CentComm := by
  intro F R _ _ _ f n γ hγ s t hs ht
  letI : Algebra F R := f.toAlgebra
  exact comm_alg γ hγ s t hs ht
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLSplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.adelicGL_split_equiv :
    SplitEquiv := by
  intro G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk
  have hd1 : ∀ x, d (i x) = 1 := fun x => (hk _).2 ⟨x, rfl⟩
  have h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹ := fun g => by
    have h1 : d (g * (c (d g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    exact (hk _).1 h1
  choose f hf using h
  have hfc : Continuous f := by
    refine hi.continuous_iff.2 ?_
    have h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹ := funext hf
    rw [h2]
    exact continuous_id.mul (hc.comp hd).inv
  let E : G₁ × R ≃* G :=
    { toFun := fun x => i x.1 * c x.2
      invFun := fun g => (f g, d g)
      left_inv := by
        rintro ⟨x, r⟩
        have hdr : d (i x * c r) = r := by rw [map_mul, hd1, hs, one_mul]
        refine Prod.ext (hi.injective ?_) hdr
        show i (f (i x * c r)) = i x
        rw [hf, hdr, mul_inv_cancel_right]
      right_inv := by
        intro g
        show i (f g) * c (d g) = g
        rw [hf, inv_mul_cancel_right]
      map_mul' := by
        rintro ⟨x, r⟩ ⟨y, s⟩
        show i (x * y) * c (r * s) = i x * c r * (i y * c s)
        rw [map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]
        simp only [mul_assoc] }
  exact ⟨{ E with
    continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd)
    continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.HaarUnimodularCriterion
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal NNReal

private theorem haar_inv_eq_self {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.inv = μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.inv = c • μ :=
    ⟨Measure.haarScalarFactor μ.inv μ, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hinv : μ.inv.inv = μ := Measure.inv_inv μ
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := hinv.symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by
        simpa only [Measure.inv_def] using Measure.map_smul c (μ := μ) measurable_inv.aemeasurable
      _ = c • (c • μ) := by rw [hc]
      _ = (c * c) • μ := by rw [smul_smul]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hpos : μ K ≠ 0 :=
    ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [hsq]
    simp
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one, ← pow_two] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

theorem UpperTheory.haar_unimodular_criterion :
    UniOf := by
  intro G _ _ _ _ _ _ _ _ μ hμ
  have key : μ.IsMulRightInvariant → Uni μ := fun hr => ⟨hμ, ⟨haar_inv_eq_self μ⟩⟩
  refine ⟨key, fun hcomm => key ⟨fun g => ?_⟩⟩
  have h : (fun x : G => x * g) = fun x => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.CharpolySeparableUnitSmul
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Polynomial

private theorem charpoly_unit_smul {R : Type} [CommRing R] {n : ℕ} (r : Rˣ)
    (M : Matrix (Fin n) (Fin n) R) :
    ((r : R) • M).charpoly =
      C ((r : R) ^ n) * M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) := by
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have hmat : Matrix.charmatrix ((r : R) • M) =
      (C (r : R) : R[X]) • (Matrix.charmatrix M).map
        (compRingHom (C ((r⁻¹ : Rˣ) : R) * X)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        coe_compRingHom_apply, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, hc, one_mul,
        ← C_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, coe_compRingHom_apply, neg_comp, C_comp, mul_neg, ← C_mul]
  have hdet : M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) =
      ((Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))).det := by
    rw [Matrix.charpoly, ← coe_compRingHom_apply, RingHom.map_det]
    rfl
  rw [Matrix.charpoly, hmat, Matrix.det_smul, Fintype.card_fin, hdet, C_pow]

private theorem separable_comp_unit {R : Type} [CommRing R] (r : Rˣ) {p : R[X]}
    (hp : p.Separable) : (p.comp (C ((r⁻¹ : Rˣ) : R) * X)).Separable := by
  obtain ⟨a, b, hab⟩ := hp
  set L : R[X] := C ((r⁻¹ : Rˣ) : R) * X with hL
  have hd : derivative (p.comp L) = C ((r⁻¹ : Rˣ) : R) * (derivative p).comp L := by
    rw [derivative_comp, hL, derivative_C_mul, derivative_X, mul_one]
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  refine ⟨a.comp L, b.comp L * C (r : R), ?_⟩
  have h := congrArg (fun q : R[X] => q.comp L) hab
  simp only [add_comp, mul_comp, one_comp] at h
  rw [hd, ← h]
  linear_combination ((b.comp L) * (derivative p).comp L) * hc

theorem UpperTheory.charpoly_separable_unit_smul :
    SepSc := by
  intro R _ n r M h
  rw [charpoly_unit_smul, Polynomial.separable_def, derivative_C_mul]
  exact (isCoprime_mul_unit_left (isUnit_C.2 (r.isUnit.pow n)) _ _).2
    (separable_comp_unit r h)
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductCentralizerAdelicGL
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.restrictedProduct_centralizer_adelicGL :
    RPCen := by
  intro V G Gi Gv _ _ _ _ _ _ _ _ _ _ _ _ q p K h g
  have comm : ∀ {A : Type} [Group A] {a b : A}, b ∈ Subgroup.centralizer ({a} : Set A) ↔ a * b = b * a := by
    intro A _ a b
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun e => e.symm, fun e => e.symm⟩
  have key : ∀ x : G, q x ∈ Subgroup.centralizer ({q g} : Set Gi) →
      (∀ v, p v x ∈ Subgroup.centralizer ({p v g} : Set (Gv v))) →
      x ∈ Subgroup.centralizer ({g} : Set G) := by
    intro x h1 h2
    refine comm.2 (h.ext _ _ ?_ fun v => ?_)
    · rw [map_mul, map_mul]; exact comm.1 h1
    · rw [map_mul, map_mul]; exact comm.1 (h2 v)
  refine
    { cq := ?_, cp := ?_, opn := ?_, cpt := ?_, ae := ?_, opnU := ?_, ext := ?_, surj := ?_, prop := ?_ }
  · exact Continuous.subtype_mk (h.cq.comp continuous_subtype_val) _
  · intro v
    exact Continuous.subtype_mk ((h.cp v).comp continuous_subtype_val) _
  · intro v
    exact (h.opn v).preimage continuous_subtype_val
  · intro v
    have hc : IsClosed ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v)) := by
      have : ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v))
          = {x | p v g * x = x * p v g} := by
        ext x; exact comm
      rw [this]
      exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (h.cpt v)
  · intro t
    exact h.ae t
  · intro S
    exact (h.opnU S).preimage continuous_subtype_val
  · intro a b h1 h2
    exact Subtype.ext (h.ext _ _ (congrArg Subtype.val h1) fun v => congrArg Subtype.val (h2 v))
  · intro gi gv hv
    obtain ⟨x, hx, hx'⟩ := h.surj gi.1 (fun v => (gv v).1) hv
    refine ⟨⟨x, key x (hx ▸ gi.2) fun v => (hx' v).symm ▸ (gv v).2⟩, Subtype.ext hx, fun v => Subtype.ext (hx' v)⟩
  · intro Ci C hCi hC hae
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' {t : Subgroup.centralizer ({g} : Set G) | cen q g t ∈ Ci ∧ ∀ v, cen (p v) g t ∈ C v}
        = {x | q x ∈ Subtype.val '' Ci ∧ ∀ v, p v x ∈ Subtype.val '' C v} := by
      ext x
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨_, h1, rfl⟩, fun v => ⟨_, h2 v, rfl⟩⟩
      · rintro ⟨⟨a, ha, ea⟩, h2⟩
        have hx : x ∈ Subgroup.centralizer ({g} : Set G) := by
          refine key x (ea ▸ a.2) fun v => ?_
          obtain ⟨b, -, eb⟩ := h2 v
          exact eb ▸ b.2
        refine ⟨⟨x, hx⟩, ⟨?_, fun v => ?_⟩, rfl⟩
        · have : cen q g ⟨x, hx⟩ = a := Subtype.ext ea.symm
          rw [this]; exact ha
        · obtain ⟨b, hb, eb⟩ := h2 v
          have : cen (p v) g ⟨x, hx⟩ = b := Subtype.ext eb.symm
          rw [this]; exact hb
    rw [e]
    refine h.prop _ _ (Subtype.isCompact_iff.1 hCi) (fun v => Subtype.isCompact_iff.1 (hC v)) ?_
    filter_upwards [hae] with v hv
    rintro _ ⟨b, hb, rfl⟩
    exact hv hb
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.HaarConstOfHaarExists
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HaarConstOfHaarExists
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictedProductMeasureSet
open MeasureTheory in
private theorem UpperTheory.restricted_product_measure_set
    (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
    (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v))
    [SigmaFinite μi] [∀ v, SigmaFinite (m v)]
    (hq : Measurable q) (hp : ∀ v, Measurable (p v)) (hK : ∀ v, MeasurableSet (K v))
    (h1 : ∀ v, m v (K v) = 1) (A : Set Gi) (hA : MeasurableSet A)
    (S : Finset V) (a : NNReal)
    (h : Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
      a • μi.prod (Measure.pi fun v : S => m v)) :
    μ {g | q g ∈ A ∧ ∀ v, p v g ∈ K v} = (a : ENNReal) * μi A := by
  have hf : Measurable (fun g => (q g, fun v : S => p v g)) :=
    hq.prodMk (Measurable.of_eval fun v => hp v)
  have hB : MeasurableSet (A ×ˢ (Set.univ.pi fun v : S => K v)) :=
    hA.prod (MeasurableSet.univ_pi fun v => hK v)
  have h2 := congrArg (fun ν => ν (A ×ˢ (Set.univ.pi fun v : S => K v))) h
  simp only [Measure.map_apply hf hB, Measure.restrict_apply (hf hB)] at h2
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.pi_pi] at h2
  simp only [h1, Finset.prod_const_one, mul_one] at h2
  rw [← h2]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_imp_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, fun v => hb v⟩, fun v _ => hb v⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, fun v => ?_⟩
    by_cases hv : v ∈ S
    · exact hb ⟨v, hv⟩
    · exact hc v hv

theorem UpperTheory.restricted_product_measure :
    ∀ (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
        (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
        (μ : MeasureTheory.Measure G) (μi : MeasureTheory.Measure Gi) (m : ∀ v, MeasureTheory.Measure (Gv v))
        [MeasureTheory.SigmaFinite μi] [∀ v, MeasureTheory.SigmaFinite (m v)],
        Measurable q → (∀ v, Measurable (p v)) → (∀ v, MeasurableSet (K v)) → (∀ v, m v (K v) = 1) →
        (∃ A : Set Gi, MeasurableSet A ∧ μi A ≠ 0 ∧ μi A ≠ ⊤) →
        ∀ (S T : Finset V) (a b : NNReal),
          MeasureTheory.Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
            a • μi.prod (MeasureTheory.Measure.pi fun v : S => m v) →
          MeasureTheory.Measure.map (fun g => (q g, fun v : T => p v g)) (μ.restrict {g | ∀ v ∉ T, p v g ∈ K v}) =
            b • μi.prod (MeasureTheory.Measure.pi fun v : T => m v) →
          a = b := by
  intro V G Gi Gv _ _ _ q p K μ μi m _ _ hq hp hK h1 ⟨A, hA, h0, ht⟩ S T a b hS hT
  have e1 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA S a hS
  have e2 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA T b hT
  have e : (a : ENNReal) * μi A = (b : ENNReal) * μi A := e1.symm.trans e2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 e)
end

theorem UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists :
    UpperTheory.ConvolutionTheory.T4.HaarEx → UpperTheory.ConvolutionTheory.T4.HaarConst := by
  intro H V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  have hm1 := fun v => (hm v).1
  choose a ha0 ha using H V G Gi Gv q p K hRP μ μi m hμ hμi hm1
  obtain ⟨hq, hp, hK, -⟩ := hRP
  obtain ⟨A⟩ : Nonempty (TopologicalSpace.PositiveCompacts Gi) := inferInstance
  refine ⟨a ∅, ha0 ∅, fun S => ?_⟩
  have h : a ∅ = a S :=
    UpperTheory.restricted_product_measure V G Gi Gv q (fun v => p v) (fun v => K v) μ μi m hq.measurable
      (fun v => (hp v).measurable) (fun v => (hK v).measurableSet) (fun v => (hm v).2)
      ⟨A, A.isCompact.measurableSet,
        (MeasureTheory.Measure.measure_pos_of_nonempty_interior μi A.interior_nonempty).ne',
        A.isCompact.measure_lt_top.ne⟩ ∅ S (a ∅) (a S) (ha ∅) (ha S)
  exact h ▸ ha S
end

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology

theorem UpperTheory.haar_const_of_haar_exists :
    HaarEx → HaarConst :=
  _root_.UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.OrbitalIntegralFubini
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotFub
open MeasureTheory in
theorem UpperTheory.ConvolutionTheory.G.quotFub_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotFub := by
  intro _ hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP X _ m _ F hF hinv ρ hρ hfin
  haveI : μ.IsHaarMeasure := hP.1.1
  have hρm : Measurable (fun x => ((ρ x).toReal : ℂ)) :=
    Complex.measurable_ofReal.comp hρ.1.ennreal_toReal
  have hH : Measurable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) :=
    hF.mul (hρm.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) (m.prod μ) := by
    refine ⟨hH.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ hH.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfin)
    refine lintegral_mono fun a => lintegral_mono fun x => ?_
    simp only [Function.uncurry, enorm_mul]
    gcongr
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hGm : Measurable (fun g => ∫ a, F a g ∂m) :=
    (hF.stronglyMeasurable.integral_prod_left).measurable
  have hGi : ∀ t g, (fun g => ∫ a, F a g ∂m) (j t * g) = (fun g => ∫ a, F a g ∂m) g := by
    intro t g
    simp only [hinv]
  obtain ⟨h1, -, h3⟩ := hE G T μ j ν hP _ hGm hGi ρ hρ
  have hmul : ∀ x, (∫ a, F a x ∂m) * ((ρ x).toReal : ℂ) = ∫ a, F a x * ((ρ x).toReal : ℂ) ∂m :=
    fun x => (integral_mul_const _ _).symm
  refine ⟨h1.2 ?_, ?_⟩
  · simp only [hmul]
    exact hint.integral_prod_right
  · rw [h3]
    simp only [hmul]
    rw [← integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact ((hE G T μ j ν hP (F a) (hF.of_uncurry_left) (hinv a) ρ hρ).2.2).symm
end

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory Pointwise in
theorem UpperTheory.orbital_integral_fubini :
    Fub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP θ δ z hθ hz hinv hC hB φ hφ hφc
  haveI : μ.IsHaarMeasure := hP.1.1
  obtain ⟨ρ, hρc, hρn, hρD⟩ := normEx G T μ j ν hP
  have hw : Continuous fun x : G => x⁻¹ * δ * θ x :=
    (continuous_inv.mul continuous_const).mul hθ
  have hFm : Measurable (Function.uncurry fun (s : ℝ) (x : G) => φ (z s * (x⁻¹ * δ * θ x))) :=
    (hφ.comp ((hz.comp continuous_fst).mul (hw.comp continuous_snd))).measurable
  have hwi : ∀ (t : T) (g : G), (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * δ * θ g := by
    intro t g
    have h := hinv t
    calc (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * ((j t)⁻¹ * δ * θ (j t)) * θ g := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
      _ = g⁻¹ * δ * θ g := by rw [h]
  have hFi : ∀ (s : ℝ) (t : T) (g : G),
      φ (z s * ((j t * g)⁻¹ * δ * θ (j t * g))) = φ (z s * (g⁻¹ * δ * θ g)) := by
    intro s t g
    rw [hwi]
  obtain ⟨B, hBc, hBm⟩ := hB (tsupport φ) hφc
  have hEc : IsCompact ((fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ)) :=
    (hBc.prod hφc).image ((hz.comp continuous_fst).inv.mul continuous_snd)
  obtain ⟨C, hCc, hCm⟩ := hC _ hEc
  obtain ⟨D, hDc, hDm⟩ := hρD C hCc
  have hsupp : ∀ (s : ℝ) (x : G), φ (z s * (x⁻¹ * δ * θ x)) ≠ 0 →
      s ∈ B ∧ x ∈ Set.range j * C := by
    intro s x h
    have hm : z s * (x⁻¹ * δ * θ x) ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 h)
    have hs := hBm s x hm
    have he : x⁻¹ * δ * θ x ∈ (fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ) :=
      ⟨(s, z s * (x⁻¹ * δ * θ x)), ⟨hs, hm⟩, by simp⟩
    obtain ⟨t, y, hy, hx⟩ := hCm x he
    exact ⟨hs, Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, y, hy, hx.symm⟩⟩
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  obtain ⟨R, hR⟩ := hDc.exists_bound_of_continuousOn (f := fun x => ((ρ x : NNReal) : ℝ))
    (NNReal.continuous_coe.comp hρc).continuousOn
  have hpt : ∀ (s : ℝ) (x : G), ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ≤
      D.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R) x := by
    intro s x
    by_cases h0 : φ (z s * (x⁻¹ * δ * θ x)) = 0
    · simp [h0]
    by_cases h1 : ρ x = 0
    · simp [h1]
    have hx : x ∈ D := hDm x (hsupp s x h0).2 h1
    rw [Set.indicator_of_mem hx]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM _)
    · rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hR x hx))
  have hin : ∀ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≤
      B.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R * μ D) s := by
    intro s
    by_cases hs : s ∈ B
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator_const hDc.measurableSet]
      exact lintegral_mono fun x => hpt s x
    · have h0 : ∀ x : G, φ (z s * (x⁻¹ * δ * θ x)) = 0 := fun x => by
        by_contra h
        exact hs (hsupp s x h).1
      simp [h0]
  have hfin : ∫⁻ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hin)
    rw [lintegral_indicator_const hBc.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hDc.measure_lt_top.ne)
      hBc.measure_lt_top.ne
  obtain ⟨h1, h2⟩ := quotFub_of normEx quotEq G T μ j ν hP ℝ volume
    (fun s x => φ (z s * (x⁻¹ * δ * θ x))) hFm hFi (fun x => (ρ x : ENNReal)) hρn hfin
  exact ⟨h1.1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.EulerProductOfQuotientPushforwardSupport
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotPi
open MeasureTheory Topology
open scoped ENNReal

private theorem lintegral_pi_one {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, MeasurableSpace (T i)]
    (ν : ∀ i, Measure (T i)) [∀ i, SigmaFinite (ν i)] (f : ∀ i, T i → NNReal)
    (hf : ∀ i, Measurable (f i)) (h1 : ∀ i, ∫⁻ t, (f i t : ℝ≥0∞) ∂(ν i) = 1) :
    ∫⁻ t, ((∏ i, f i (t i) : NNReal) : ℝ≥0∞) ∂(Measure.pi ν) = 1 := by
  have hint : ∀ i, Integrable (fun t => (f i t : ℝ)) (ν i) := fun i => by
    have := integrable_toReal_of_lintegral_ne_top (μ := ν i) (f := fun t => (f i t : ℝ≥0∞))
      (hf i).coe_nnreal_ennreal.aemeasurable (by rw [h1 i]; exact ENNReal.one_ne_top)
    simpa using this
  have hI : ∀ i, ∫ t, (f i t : ℝ) ∂(ν i) = 1 := fun i => by
    have := lintegral_coe_eq_integral (f i) (hint i)
    rw [h1 i] at this
    exact ENNReal.ofReal_eq_one.1 this.symm
  have hP : Integrable (fun t : ∀ i, T i => ((∏ i, f i (t i) : NNReal) : ℝ)) (Measure.pi ν) := by
    simp only [NNReal.coe_prod]
    exact Integrable.fintype_prod_dep hint
  rw [lintegral_coe_eq_integral _ hP]
  simp only [NNReal.coe_prod]
  rw [integral_fintype_prod_eq_prod (fun i t => (f i t : ℝ))]
  simp [hI]

theorem UpperTheory.ConvolutionTheory.G.quotPi_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotPi := by
  intro hN hE ι _ G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP J hJ
  haveI : ∀ i, (μ i).IsHaarMeasure := fun i => (hP i).1.1
  haveI : ∀ i, (μ i).IsInvInvariant := fun i => (hP i).1.2
  haveI : ∀ i, (ν i).IsHaarMeasure := fun i => (hP i).2.2.1
  haveI : ∀ i, (ν i).IsInvInvariant := fun i => (hP i).2.2.2
  have hJe : (J : (∀ i, T i) → ∀ i, G i) = Pi.map (fun i => (j i : T i → G i)) := by
    funext t i
    exact hJ t i
  have hPair : UpperTheory.ConvolutionTheory.G.Pair (Measure.pi μ) J (Measure.pi ν) := by
    refine ⟨⟨inferInstance, inferInstance⟩, ?_, ⟨inferInstance, inferInstance⟩⟩
    rw [hJe]
    exact IsClosedEmbedding.piMap fun i => (hP i).2.1
  refine ⟨hPair, fun F hF => ?_⟩
  choose ρ hρc hρn _ using fun i => hN (G i) (T i) (μ i) (j i) (ν i) (hP i)
  have hR : UpperTheory.ConvolutionTheory.G.IsNrm J (Measure.pi ν)
      (fun g => ((∏ i, ρ i (g i) : NNReal) : ℝ≥0∞)) := by
    refine ⟨?_, fun x => ?_⟩
    · exact (Finset.measurable_prod _ fun i _ =>
        (hρc i).measurable.comp (measurable_pi_apply i)).coe_nnreal_ennreal
    · have := lintegral_pi_one ν (fun i t => ρ i (j i t * x i))
        (fun i => ((hρc i).comp ((hP i).2.1.continuous.mul continuous_const)).measurable)
        (fun i => (hρn i).2 (x i))
      simpa only [Pi.mul_apply, hJ] using this
  have hFm : Measurable fun g : ∀ i, G i => ∏ i, F i (g i) :=
    Finset.measurable_prod _ fun i _ => (hF i).1.comp (measurable_pi_apply i)
  have hFi : ∀ t g, (fun g : ∀ i, G i => ∏ i, F i (g i)) (J t * g) =
      (fun g : ∀ i, G i => ∏ i, F i (g i)) g := fun t g => by
    simp only [Pi.mul_apply, hJ, (hF _).2]
  obtain ⟨h1, -, h2⟩ := hE _ _ _ _ _ hPair _ hFm hFi _ hR
  have hloc := fun i => hE (G i) (T i) (μ i) (j i) (ν i) (hP i) (F i) (hF i).1 (hF i).2 _ (hρn i)
  have hfun : (fun x : ∀ i, G i => (∏ i, F i (x i)) *
      ((((∏ i, ρ i (x i) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)) =
      fun x => ∏ i, (F i (x i) * (((ρ i (x i) : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    simp only [ENNReal.coe_toReal, NNReal.coe_prod, Complex.ofReal_prod, Finset.prod_mul_distrib]
  refine ⟨fun hq => h1.2 ?_, ?_⟩
  · rw [hfun]
    exact Integrable.fintype_prod_dep
      (f := fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ)) fun i => (hloc i).1.1 (hq i)
  · rw [h2, hfun, integral_fintype_prod_eq_prod
      (fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ))]
    exact Finset.prod_congr rfl fun i _ => (hloc i).2.2.symm
end

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.eulerProduct_of_quotient_pushforward_support :
    QPush → EulerSupp → Euler := by
  intro hQ hS V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv h1 h2 h3 μ μi m ν νi nv
    hP hPi hPv S a b ha hb hE hET Fi Fv hFi hFii hFv hloc
  obtain ⟨hM, hSupp, hVal⟩ := hS V G Gi Gv q p K T Ti Tv qT pT KT hR hRT j ji jv h1 h2 h3 S Fi Fv
    hFi hFii hFv hloc
  refine ⟨hM, ?_⟩
  have lin := quotLin_of normEx quotEq
  have prd := quotProd_of normEx quotEq
  have pie := quotPi_of normEx quotEq
  let J : (∀ v : S, Tv v) →* ∀ v : S, Gv v :=
    Pi.monoidHom fun v : S => (jv v).comp (Pi.evalMonoidHom _ v)
  have hJ : ∀ (t : ∀ v : S, Tv v) (v : S), J t v = jv v (t v) := fun _ _ => rfl
  obtain ⟨pairPi, valPi⟩ := pie S (fun v : S => Gv v) (fun v : S => Tv v) (fun v : S => m v)
    (fun v : S => jv v) (fun v : S => nv v) (fun v => hPv v) J hJ
  obtain ⟨pairPr, valPr⟩ := prd Gi Ti (∀ v : S, Gv v) (∀ v : S, Tv v) μi ji νi hPi _ J _ pairPi
  obtain ⟨pairL, valL⟩ := (lin _ _ _ _ _ pairPr).2 a b ha hb
  have pullbackMapSquare : Measurable fun g : ∀ v : S, Gv v => ∏ v : S, Fv v (g v) :=
    Finset.measurable_fun_prod _ fun v _ => (hFv v).1.comp (measurable_pi_apply v)
  have indexFSecond : ∀ (t : ∀ v : S, Tv v) (g : ∀ v : S, Gv v),
      ∏ v : S, Fv v ((J t * g) v) = ∏ v : S, Fv v (g v) := fun t g =>
    Finset.prod_congr rfl fun v _ => (hFv v).2 (t v) (g v)
  have mF' : Measurable fun x : Gi × ∀ v : S, Gv v => Fi x.1 * ∏ v : S, Fv v (x.2 v) :=
    (hFi.comp measurable_fst).mul (pullbackMapSquare.comp measurable_snd)
  have iF' : ∀ (t : Ti × ∀ v : S, Tv v) (g : Gi × ∀ v : S, Gv v),
      Fi ((ji.prodMap J t * g).1) * ∏ v : S, Fv v ((ji.prodMap J t * g).2 v) =
        Fi g.1 * ∏ v : S, Fv v (g.2 v) := fun t g => by
    have e1 : Fi ((ji.prodMap J t * g).1) = Fi g.1 := hFii t.1 g.1
    have e2 : ∏ v : S, Fv v ((ji.prodMap J t * g).2 v) = ∏ v : S, Fv v (g.2 v) := indexFSecond t.2 g.2
    rw [e1, e2]
  have hpre : j ⁻¹' (US p K S : Set G) = (US pT KT S : Set T) := by
    ext t
    constructor
    · intro ht v hv
      have := ht v hv
      rw [h2] at this
      exact (h3 v _).2 this
    · intro ht v hv
      show p v (j t) ∈ K v
      rw [h2]
      exact (h3 v _).1 (ht v hv)
  have hET' : (ν.restrict (j ⁻¹' (US p K S : Set G))).map (prS qT pT S) =
      b • νi.prod (Measure.pi fun v : S => nv v) := by
    rw [hpre]; exact hET
  have cπ : Continuous (prS q p S) :=
    hR.cq.prodMk (continuous_pi fun v : S => hR.cp v)
  have cπT : Continuous (prS qT pT S) :=
    hRT.cq.prodMk (continuous_pi fun v : S => hRT.cp v)
  have comm : ∀ t, prS q p S (j t) = ji.prodMap J (prS qT pT S t) := fun t => by
    refine Prod.ext (h1 t) (funext fun v => h2 v t)
  have iF : ∀ t g, Fi (q (j t * g)) * ∏ᶠ v, Fv v (p v (j t * g)) =
      Fi (q g) * ∏ᶠ v, Fv v (p v g) := fun t g => by
    have e1 : Fi (q (j t * g)) = Fi (q g) := by rw [map_mul, h1, hFii]
    have e2 : ∀ v, Fv v (p v (j t * g)) = Fv v (p v g) := fun v => by
      rw [map_mul, h2, (hFv v).2]
    simp only [e1, e2]
  have push := hQ G T (Gi × ∀ v : S, Gv v) (Ti × ∀ v : S, Tv v) μ j ν _ (ji.prodMap J) _ hP pairL
    (US p K S) (hR.opnU S) (prS q p S) (prS qT pT S) cπ cπT comm hE hET'
    (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g))
    (fun x => Fi x.1 * ∏ v : S, Fv v (x.2 v)) hM iF mF' iF' hSupp hVal
  rw [push, (valL _ mF' iF').2, (valPr Fi _ hFi hFii pullbackMapSquare indexFSecond).2, (valPi fun v : S => Fv v)
    (fun v => hFv v) |>.2, Finset.prod_coe_sort S fun v => qI (m v) (jv v) (nv v) (Fv v), mul_assoc]
end

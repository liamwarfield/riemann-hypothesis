module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesMeasurePreserving

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesNaturalInRing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesNaturalInRing
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem repr_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem trace_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      f (Algebra.trace R (R ⊗[F] E) x) := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Algebra.TensorProduct.map f (AlgHom.id F E) (x * Algebra.TensorProduct.basis R b k) =
      Algebra.TensorProduct.map f (AlgHom.id F E) x * Algebra.TensorProduct.basis R' b k := by
    rw [_root_.map_mul]
    simp [Algebra.TensorProduct.basis_apply]
  rw [← repr_map_tensor f b, h]

theorem hCo_hermMap : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d), hCo R' σ b (hermMap f σ S) i = f (hCo R σ b S i) := by
  intro F E _ _ _ σ R R' _ _ _ _ f d b n S i
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, hermMap, Matrix.map_apply, map_mul, AlgHom.commutes, trace_map_tensor f b]
  · simp only [hCo, Sum.elim_inr, hermMap, Matrix.map_apply, repr_map_tensor f b]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesNaturalInRingStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_coordinates_natural_in_ring : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d), hCo R' σ b (hermMap f σ S) i = f (hCo R σ b S i) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_hermMap | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_hermMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_hermMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAll
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.MatInt

theorem algebraMap_mem_integers_of_not_mem_support (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : F) (h : v ∉ HeightOneSpectrum.Support (𝓞 F) a) :
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap F (Fv F v) a) = v.valuation F a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  simpa [HeightOneSpectrum.Support] using h

theorem mulVec_mem_integers (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (v : HeightOneSpectrum (𝓞 F)) (B : Matrix ι ι (Fv F v)) (y : ι → Fv F v)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F)
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) (i : ι) :
    B.mulVec y i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hB i j) (hy j)

theorem exists_finset_mulVec_integral_iff : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 →
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v,
      (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
  intro F _ _ ι _ _ A hA
  classical
  have hfin : ∀ a : F, (HeightOneSpectrum.Support (𝓞 F) a).Finite :=
    HeightOneSpectrum.Support.finite (𝓞 F)
  refine ⟨Finset.univ.biUnion fun p : ι × ι =>
    (hfin (A p.1 p.2)).toFinset ∪ (hfin (A⁻¹ p.1 p.2)).toFinset, fun v hv x => ?_⟩
  have hout : ∀ i j, v ∉ HeightOneSpectrum.Support (𝓞 F) (A i j) ∧
      v ∉ HeightOneSpectrum.Support (𝓞 F) (A⁻¹ i j) := by
    intro i j
    constructor
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_left _ ((hfin _).mem_toFinset.2 h)⟩)
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_right _ ((hfin _).mem_toFinset.2 h)⟩)
  have hinv : (A⁻¹.map (algebraMap F (Fv F v))) * (A.map (algebraMap F (Fv F v))) = 1 := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h1 := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F (Fv F v)))
      (Matrix.nonsing_inv_mul A hu)
    simpa [Matrix.map_mul] using h1
  constructor
  · intro h i
    have e : (A⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((A.map (algebraMap F (Fv F v))).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [← e]
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).2) h i
  · intro h i
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).1) h i

end GlobalTheory.CompanionTheory.MatInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAllStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_preserves_integers_almost_all : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v, (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff | exact GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff | (intros; apply GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.PiCovol

theorem isFD_pi {ι Y : Type} [Fintype ι] [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {G : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain G D ν) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : ι => G) (Set.univ.pi fun _ : ι => D)
      (Measure.pi fun _ : ι => ν) := by
  have hq (i : ι) := Measure.quasiMeasurePreserving_eval (fun _ : ι => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : ι => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem map_eq_of_isFD {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure V) [P.IsAddHaarMeasure] (G : AddSubgroup V) [Countable G] {D : Set V}
    (hD : IsAddFundamentalDomain G D P) (h0 : P D ≠ 0) (h1 : P D ≠ ⊤) (e : V ≃ₜ+ V)
    (hG : ∀ v ∈ G, e.symm v ∈ G) (hG' : ∀ v ∈ G, e v ∈ G) : P.map e = P := by
  haveI : (P.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map P
  set c := Measure.addHaarScalarFactor (P.map e) P with hc
  have h : P.map e = c • P := Measure.isAddLeftInvariant_eq_smul _ P
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : IsAddFundamentalDomain G (e ⁻¹' D) P := by
    refine hD.preimage_of_equiv (f := e) ⟨hm.measurable.aemeasurable, ?_⟩
      (e := fun b : G => (⟨e.symm b, hG _ b.2⟩ : G)) ⟨fun b b' h => ?_, fun a => ?_⟩ fun b v => ?_
    · rw [h]; exact Measure.smul_absolutelyContinuous
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact ⟨⟨e a, hG' _ a.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
    · change e (e.symm b + v) = b + e v
      simp
  have e1 : P (e ⁻¹' D) = P D := hpre.measure_eq hD
  have e2 : P (e ⁻¹' D) = c * P D := by rw [← hm.map_apply, h]; rfl
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have : (c : ℝ≥0∞) * P D = 1 * P D := by rw [← e2, e1, one_mul]
    exact (ENNReal.mul_left_inj h0 h1).1 this
  have : c = 1 := by exact_mod_cast hc1
  rw [h, this, one_smul]

end GlobalTheory.CompanionTheory.SiegelND.PiCovol


open GlobalTheory.CompanionTheory.SiegelND.PiCovol in
theorem GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  intro F _ _ ν hν ι _ _ A hA
  obtain ⟨hH, D, hD, hD1⟩ := hν
  haveI := hH
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  set G₀ : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range with hG₀
  set G : AddSubgroup (ι → AF F) := AddSubgroup.pi Set.univ fun _ : ι => G₀ with hGdef
  have hmemG : ∀ v : ι → AF F, v ∈ G ↔ ∃ ξ : ι → F, v = fun i => algebraMap F (AF F) (ξ i) := by
    intro v
    constructor
    · intro hv
      choose ξ hξ using fun i => hv i trivial
      exact ⟨ξ, funext fun i => (hξ i).symm⟩
    · rintro ⟨ξ, rfl⟩ i _
      exact ⟨ξ i, rfl⟩
  haveI : Countable G := by
    have : Function.Surjective (fun ξ : ι → F => (⟨fun i => algebraMap F (AF F) (ξ i), (hmemG _).2 ⟨ξ, rfl⟩⟩ : G)) := by
      rintro ⟨v, hv⟩
      obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
      exact ⟨ξ, rfl⟩
    exact this.countable
  have hFD := isFD_pi (ι := ι) ν hD
  have hmass : (Measure.pi fun _ : ι => ν) (Set.univ.pi fun _ : ι => D) = 1 := by
    rw [Measure.pi_pi]; simp [hD1]
  have hrat : ∀ (B : Matrix ι ι F) (ξ : ι → F), (B.map (algebraMap F (AF F))).mulVec (fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) (B.mulVec ξ i) := by
    intro B ξ
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) B ξ i).symm
  have hu := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map (R := AF F) A hA
  have hinv : (A.map (algebraMap F (AF F)))⁻¹ = A⁻¹.map (algebraMap F (AF F)) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have := map_eq_of_isFD (Measure.pi fun _ : ι => ν) G hFD (by rw [hmass]; simp) (by rw [hmass]; simp)
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE _ hu) ?_ ?_
  · exact this
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A⁻¹.mulVec ξ, ?_⟩
    change (A.map (algebraMap F (AF F)))⁻¹.mulVec _ = _
    rw [hinv, hrat]
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A.mulVec ξ, ?_⟩
    exact hrat A ξ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrixStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_one_invariant_under_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix | exact GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix | (intros; apply GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionInvariantMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionInvariantMatrix
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem fourier_prod_symm_preserving :
    ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  intro A _ _ ν _ ψ ι _ _ Bm hsym hemb hmap t f hf hint hinv
  have hψ : ∀ (s : Finset ι) (h : ι → A), ψ (∑ i ∈ s, h i) = ∏ i ∈ s, ψ (h i) := by
    intro s h
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  have hsplit : ∀ (g : A → ℂ) (x w : ι → A),
      (∏ i, g (x i)) * ψ (dotProduct x w) = ∏ i, (g (x i) * ψ (x i * w i)) := by
    intro g x w
    rw [Finset.prod_mul_distrib]
    congr 1
    exact hψ Finset.univ _
  have key : ∀ w : ι → A, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x w)
      ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (w i) := by
    intro w
    simp_rw [hsplit t]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => t x * ψ (x * w i))]
    exact Finset.prod_congr rfl fun i _ => (hf (w i)).symm
  refine ⟨fun y => key _, ?_, ?_⟩
  · have h1 : Integrable (fun w : ι → A => ∏ i, f (w i)) (Measure.pi fun _ : ι => ν) :=
      Integrable.fintype_prod (fun _ => hint)
    rw [← hmap] at h1
    exact (hemb.integrable_map_iff).1 h1
  · intro z
    have hdot : ∀ y : ι → A, dotProduct y (Bm.mulVec z) = dotProduct (Bm.mulVec y) z := by
      intro y
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose Bm y, ← hsym.eq]
      simp [hsym.eq]
    have hG : ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z))
          ∂(Measure.pi fun _ : ι => ν)
        = ∫ w : ι → A, (∏ i, f (w i)) * ψ (dotProduct w z)
          ∂((Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x)) := by
      rw [hemb.integral_map]
      simp_rw [hdot]
    rw [hG, hmap]
    simp_rw [hsplit f]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => f x * ψ (x * z i))]
    exact Finset.prod_congr rfl fun i _ => hinv (z i)

end GlobalTheory.CompanionTheory.BigCell
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionInvariantMatrixStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_inversion_invariant_matrix : ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | exact GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | (intros; apply GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityProductBumps
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityProductBumps
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem prod_coordinate_bumps :
    ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A]
      [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ),
      (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) →
      Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets →
      (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧
        HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧
        ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧
      Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop
        (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ _ e ρ hρ hlim
  have hsub : ∀ k, tsupport (fun T : G => ∏ i, ρ k (e T i)) ⊆
      e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k)) := by
    intro k
    apply closure_minimal
    · intro T hT
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      intro i
      apply subset_tsupport
      rw [Function.mem_support] at hT ⊢
      exact (Finset.prod_ne_zero_iff.mp hT) i (Finset.mem_univ i)
    · exact (isClosed_set_pi fun i _ => isClosed_tsupport (ρ k)).preimage (map_continuous e)
  refine ⟨fun k => ⟨?_, ?_, fun T => Finset.prod_nonneg fun i _ => (hρ k).2.2 _⟩, ?_⟩
  · exact continuous_finsetProd _ fun i _ => (hρ k).1.comp ((continuous_apply i).comp (map_continuous e))
  · have hS : IsCompact (e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k))) :=
      (Homeomorph.isCompact_preimage (e : G ≃ₜ (ι → A))).mpr (isCompact_univ_pi fun _ => (hρ k).2.1)
    exact IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub k)
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro U hU
    have hV : e.symm ⁻¹' U ∈ nhds (0 : ι → A) :=
      (map_continuous e.symm).continuousAt.preimage_mem_nhds (by rwa [map_zero])
    rw [nhds_pi, Filter.mem_pi] at hV
    obtain ⟨I, -, t, ht, hIt⟩ := hV
    have hW : (⋂ i, t i) ∈ nhds (0 : A) := Filter.iInter_mem.mpr fun i => by simpa using ht i
    filter_upwards [hlim _ hW] with k hk
    intro T hT
    have h1 := hsub k hT
    simp only [Set.mem_preimage, Set.mem_univ_pi] at h1
    have h2 : e T ∈ I.pi t := fun i _ => Set.mem_iInter.mp (hk (h1 i)) i
    simpa using hIt h2

end GlobalTheory.CompanionTheory.BigCell
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityProductBumpsStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximate_identity_product_bumps : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets → (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧ HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧ ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧ Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps | exact GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps | (intros; apply GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpen
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem preimage_box_shrinking : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ e U hU hlim
  refine ⟨fun k => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => (hU k).1)
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => (hU k).2.1).preimage e.continuous
  · show e 0 ∈ Set.pi Set.univ (fun _ => U k)
    rw [map_zero]
    exact Set.mem_univ_pi.2 fun _ => (hU k).2.2
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro t ht
    have hc : Filter.Tendsto e.symm (nhds 0) (nhds 0) := by
      have h0 : Filter.Tendsto e.symm (nhds 0) (nhds (e.symm 0)) := e.symm.continuous.tendsto 0
      rw [map_zero] at h0
      exact h0
    have h1 : e.symm ⁻¹' t ∈ nhds (0 : ι → A) := hc ht
    rw [nhds_pi, Filter.mem_pi'] at h1
    obtain ⟨I, s, hs, hsub⟩ := h1
    have hW : (⋂ i, s i) ∈ nhds (0 : A) := Filter.iInter_mem.2 hs
    filter_upwards [hlim _ hW] with k hk
    intro x hx
    have h2 : e x ∈ Set.pi (I : Set ι) s := fun i _ =>
      Set.mem_iInter.1 (hk (hx i (Set.mem_univ i))) i
    simpa using hsub h2

end GlobalTheory.CompanionTheory.BigCell
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpenStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_neighbourhoods_shrink_compact_open : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | exact GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | (intros; apply GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProduct
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

def powT {A ι : Type} [Fintype ι] (t : A → ℂ) (x : ι → A) : ℂ := ∏ i, t (x i)

def fouP {A ι : Type} [CommRing A] [Fintype ι] [MeasurableSpace A] (ψ : AddChar A ℂ) (Bm : Matrix ι ι A)
    (μ : Measure (ι → A)) (Φ : (ι → A) → ℂ) (y : ι → A) : ℂ :=
  ∫ x, Φ x * ψ (dotProduct x (Bm.mulVec y)) ∂μ

theorem powT_continuous {A ι : Type} [TopologicalSpace A] [Fintype ι] {t : A → ℂ} (h : Continuous t) :
    Continuous (powT t : (ι → A) → ℂ) :=
  continuous_finsetProd _ fun i _ => h.comp (continuous_apply i)

theorem powT_compact {A ι : Type} [TopologicalSpace A] [T2Space A] [Fintype ι] {t : A → ℂ} (h : HasCompactSupport t) :
    HasCompactSupport (powT t : (ι → A) → ℂ) := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ => tsupport t)
    (isCompact_univ_pi fun _ => h) fun x hx => ?_
  obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ x i ∉ tsupport t := by
    simpa [Set.mem_pi] using hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

theorem eval_mulVec {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (B : Matrix ι ι F)
    (v : HeightOneSpectrum (𝓞 F)) (y : ι → AF F) (i : ι) :
    (sndA F ((B.map (algebraMap F (AF F))).mulVec y i)) v =
      (B.map (algebraMap F (Fv F v))).mulVec (fun j => (sndA F (y j)) v) i := by
  let φ : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)
  change φ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

theorem core (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (hBs : B.IsSymm) (hBd : B.det ≠ 0)
    (μ : Measure (ι → AF F))
    (hμ : SelfDual μ (fun x y => ψ (dotProduct x ((B.map (algebraMap F (AF F))).mulVec y)))) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S →
      ∃ (ρ : ℕ → Ainf F → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
        (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧
        Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧
        (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : Fv F v) ∈ U k v) ∧
        (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : Fv F v)).smallSets) ∧
        (∀ k, Continuous (powT (testT (ρ k) S (U k)) : (ι → AF F) → ℂ) ∧
          HasCompactSupport (powT (testT (ρ k) S (U k)) : (ι → AF F) → ℂ)) ∧
        (∀ k, Integrable (fouP ψ (B.map (algebraMap F (AF F))) μ (powT (testT (ρ k) S (U k)))) μ) ∧
        (∀ k, ∫ x, powT (testT (ρ k) S (U k)) x ∂μ =
          (((∫ y, ρ k y ∂laminf : ℝ) : ℂ) * ∏ v ∈ S, (((lam v) (U k v)).toReal : ℂ)) ^ Fintype.card ι) ∧
        (∀ k y, ‖fouP ψ (B.map (algebraMap F (AF F))) μ (powT (testT (ρ k) S (U k))) y‖ ≤
          ‖∫ x, powT (testT (ρ k) S (U k)) x ∂μ‖) ∧
        ∀ y, Filter.Tendsto (fun k => fouP ψ (B.map (algebraMap F (AF F))) μ (powT (testT (ρ k) S (U k))) y /
            ∫ x, powT (testT (ρ k) S (U k)) x ∂μ) Filter.atTop
          (nhds ({x : ι → AF F | ∀ i, sndA F (x i) ∈ intF S}.indicator (fun _ => (1 : ℂ)) y)) := by
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne F
  obtain ⟨S₀, h₀⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx F hF ψ hψ ν hν laminf lam hinf hlam
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.matrix_preserves_integers_almost_all F ι B hBd
  refine ⟨S₀ ∪ S₂, fun S hS => ?_⟩
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, hb, hlim⟩ := h₀ S (Finset.subset_union_left.trans hS)
  haveI : ν.IsAddHaarMeasure := hν.1
  set Bm := B.map (algebraMap F (AF F)) with hBm
  set P : Measure (ι → AF F) := Measure.pi fun _ : ι => ν with hPdef
  have hpres : P.map (fun x => Bm.mulVec x) = P := GlobalTheory.T.covolume_one_invariant_under_matrix F ν hν ι B hBd
  have hu : IsUnit Bm.det := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map _ hBd
  have hemb : MeasurableEmbedding fun x : ι → AF F => Bm.mulVec x :=
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE Bm hu).toHomeomorph.measurableEmbedding
  have hT := fun k => GlobalTheory.T.fourier_inversion_invariant_matrix (AF F) ν ψ ι Bm (hBs.map _) hemb hpres (testT (ρ k) S (U k))
    (fouA ψ ν (testT (ρ k) S (U k))) (fun y => rfl) (hinv k).1 (hinv k).2
  have hc := fun k => GlobalTheory.T.continuous_and_hasCompactSupport_testT F (ρ k) S (U k) (hρ k).1 (hρ k).2.1 (fun v => ⟨(hU k v).1, (hU k v).2.1⟩)
  have hfou : ∀ k y, fouP ψ Bm P (powT (testT (ρ k) S (U k))) y =
      ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) := fun k y => (hT k).1 y
  have hP : P.IsAddHaarMeasure := inferInstance

  have hμP : μ = P := by
    obtain ⟨x₀, hx₀⟩ : ∃ x, ρ 0 x ≠ 0 := by
      by_contra hall
      push Not at hall
      have := (hρ 0).2.2.2
      simp [hall] at this
    have h0box : (0 : Af F) ∈ boxA S (U 0) :=
      ⟨fun v _ => (hU 0 v).2.2, fun v _ => zero_mem _⟩
    refine GlobalTheory.HermSD.eq_of_test_haar hμ hP (powT (testT (ρ 0) S (U 0)))
      (powT_continuous (hc 0).1) (powT_compact (hc 0).2) ?_ (fun _ => -(pairA F x₀ 0)) ?_ ?_
    · have e : (fun y => ∫ x, powT (testT (ρ 0) S (U 0)) x * ψ (dotProduct x (Bm.mulVec y)) ∂P) =
          fun y => ∏ i, fouA ψ ν (testT (ρ 0) S (U 0)) (Bm.mulVec y i) := funext (hfou 0)
      rw [e]
      exact (hT 0).2.1
    · refine (integral_congr_ae (ae_of_all _ fun y => ?_)).trans ((hT 0).2.2 _)
      exact congrArg (· * _) (hfou 0 y)
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simp only [Pi.neg_apply, neg_neg]
      have h1 : testT (ρ 0) S (U 0) (pairA F x₀ 0) = (ρ 0 x₀ : ℂ) := by
        have : sndA F (pairA F x₀ 0) ∈ boxA S (U 0) := h0box
        simp only [testT, Set.indicator_of_mem this, mul_one]
        rfl
      rw [h1]
      exact_mod_cast hx₀
  subst hμP
  have hintP : ∀ k, ∫ x, powT (testT (ρ k) S (U k)) x ∂P =
      (∫ y, testT (ρ k) S (U k) y ∂ν) ^ Fintype.card ι := fun k => by
    have := integral_fintype_prod_eq_prod (μ := fun _ : ι => ν) (𝕜 := ℂ) (fun _ => testT (ρ k) S (U k))
    simp only [powT]
    rw [this, Finset.prod_const, Finset.card_univ]
  refine ⟨ρ, U, hρ, hρt, hU, hUt, fun k => ⟨powT_continuous (hc k).1, powT_compact (hc k).2⟩, fun k => ?_,
    fun k => ?_, fun k y => ?_, fun y => ?_⟩
  · have e : fouP ψ Bm P (powT (testT (ρ k) S (U k))) =
        fun y => ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) := funext (hfou k)
    rw [e]
    exact (hT k).2.1
  · rw [hintP, hint k]
  · rw [hfou, hintP, norm_pow, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hb k _
  · have e : ∀ k, fouP ψ Bm P (powT (testT (ρ k) S (U k))) y / ∫ x, powT (testT (ρ k) S (U k)) x ∂P =
        ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) / ∫ w, testT (ρ k) S (U k) w ∂ν := fun k => by
      rw [hfou, hintP, ← Finset.card_univ, ← Finset.prod_const, Finset.prod_div_distrib]
    simp only [e]
    have hl : Filter.Tendsto (fun k => ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) /
        ∫ w, testT (ρ k) S (U k) w ∂ν) Filter.atTop
        (nhds (∏ i, (intF S).indicator (fun _ => (1 : ℂ)) (sndA F (Bm.mulVec y i)))) :=
      tendsto_finsetProd _ fun i _ => hlim _
    convert hl using 2
    have hiff : (∀ i, sndA F (Bm.mulVec y i) ∈ intF S) ↔ ∀ i, sndA F (y i) ∈ intF S := by
      have hv : ∀ v, v ∉ S → ((∀ i, (sndA F (Bm.mulVec y i)) v ∈ v.adicCompletionIntegers F) ↔
          ∀ i, (sndA F (y i)) v ∈ v.adicCompletionIntegers F) := fun v hvS => by
        simp only [hBm, eval_mulVec]
        exact h₂ v (fun h => hvS (hS (Finset.mem_union_right _ h))) _
      constructor
      · intro h i v hvS
        exact (hv v hvS).1 (fun j => h j v hvS) i
      · intro h i v hvS
        exact (hv v hvS).2 (fun j => h j v hvS) i
    by_cases hy : ∀ i, sndA F (y i) ∈ intF S
    · rw [Set.indicator_of_mem (by exact hy)]
      exact (Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hiff.2 hy i) _).symm
    · rw [Set.indicator_of_notMem (by exact hy)]
      obtain ⟨i, hi⟩ : ∃ i, sndA F (Bm.mulVec y i) ∉ intF S := by
        by_contra h
        push Not at h
        exact hy (hiff.1 h)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

theorem mem_latH_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (S : HermR (Fv F v) σ n) :
    S ∈ latH σ b v n ↔ ∀ i, hCo (Fv F v) σ b S i ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩ (i | ⟨k, p⟩)
    · exact h1 i
    · exact h2 _ _ p.2 k
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i j hij k => h (Sum.inr (k, ⟨(i, j), hij⟩))⟩

theorem hCo_fin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : HermR (AF F) σ n) (i : Idx n d) :
    hCo (Fv F v) σ b (hermV σ v (hermFin σ y)) i = (sndA F (hCo (AF F) σ b y i)) v := by
  rw [hermV, GlobalTheory.T.hermitian_coordinates_natural_in_ring, hermFin, GlobalTheory.T.hermitian_coordinates_natural_in_ring]
  rfl

theorem hCo_inf {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (y : HermR (AF F) σ n) (i : Idx n d) :
    hCo (Ainf F) σ b (hermInf σ y) i = fstA F (hCo (AF F) σ b y i) := by
  rw [hermInf, GlobalTheory.T.hermitian_coordinates_natural_in_ring]

theorem testH_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : HermR (AF F) σ n) :
    testH σ b (fun T => ∏ i, ρ (hCo (Ainf F) σ b T i)) S
        (fun v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U v)) y =
      powT (testT ρ S U) (hCo (AF F) σ b y) := by
  classical
  have hbox : hermFin σ y ∈ boxH σ b n S (fun v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U v)) ↔
      ∀ i, sndA F (hCo (AF F) σ b y i) ∈ boxA S U := by
    constructor
    · rintro ⟨h1, h2⟩ i
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := h1 v hv i trivial
        rwa [hCo_fin] at this
      · have := (mem_latH_iff σ b v n _).1 (h2 v hv) i
        rwa [hCo_fin] at this
    · intro h
      refine ⟨fun v hv i _ => ?_, fun v hv => (mem_latH_iff σ b v n _).2 fun i => ?_⟩
      · rw [hCo_fin]
        exact (h i).1 v hv
      · rw [hCo_fin]
        exact (h i).2 v hv
  simp only [testH, powT, testT, Finset.prod_mul_distrib, hCo_inf]
  push_cast
  congr 1
  by_cases hy : ∀ i, sndA F (hCo (AF F) σ b y i) ∈ boxA S U
  · rw [Set.indicator_of_mem (hbox.2 hy)]
    exact (Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hy i) _).symm
  · rw [Set.indicator_of_notMem (fun h => hy (hbox.1 h))]
    push Not at hy
    obtain ⟨i, hi⟩ := hy
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem mem_intH_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F))) (y : HermR (AF F) σ n) :
    hermFin σ y ∈ intH σ b n S ↔ ∀ i, sndA F (hCo (AF F) σ b y i) ∈ intF S := by
  constructor
  · intro h i v hv
    have := (mem_latH_iff σ b v n _).1 (h v hv) i
    rwa [hCo_fin] at this
  · intro h v hv
    refine (mem_latH_iff σ b v n _).2 fun i => ?_
    rw [hCo_fin]
    exact h i v hv

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

theorem exists_testH_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v ∧ 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k, Integrable (fouH σ ψ db (testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, fouH σ ψ db (testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖fouH σ ψ db (testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ w, testH σ b (ρ k) S (U k) w ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => fouH σ ψ db (testH σ b (ρ k) S (U k)) y / ∫ w, testH σ b (ρ k) S (U k) w ∂db) Filter.atTop (nhds ((intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ db hdb d b laminf lam hinf hlam
  classical
  have hF := hCM.1
  obtain ⟨t1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := t1
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := a1; haveI := a2; haveI := a3; haveI := a4
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : laminf.IsAddHaarMeasure := hinf.1
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  obtain ⟨eA, heA⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (AF F) d b n
  obtain ⟨eI, heI⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (Ainf F) d b n
  choose eV heV using fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (Fv F v) d b n
  obtain ⟨hBs, hBd⟩ := GlobalTheory.T.coordinate_form_symmetric_nondegenerate F E σ hCM d b n
  set B := coordForm σ b n with hB
  set Bm := B.map (algebraMap F (AF F)) with hBm
  have hpair : ∀ w y : HermR (AF F) σ n, pairHerm (AF F) σ n w y = dotProduct (eA w) (Bm.mulVec (eA y)) := by
    intro w y
    rw [heA, heA]
    exact GlobalTheory.T.hermitian_pairing_in_coordinates F E σ hCM (AF F) d b n w y
  have hdb' : SelfDual db (fun S T => ψ (pairHerm (AF F) σ n S T)) := hdb
  have hsd : SelfDual (db.map eA) (fun x y => ψ (dotProduct x (Bm.mulVec y))) := by
    have h := GlobalTheory.CompanionTheory.SW.SdAny.selfDual_map eA db _ hdb'
    simp only [hpair, ContinuousAddEquiv.apply_symm_apply] at h
    exact h
  have hemb : MeasurableEmbedding eA := eA.toHomeomorph.measurableEmbedding
  obtain ⟨S₁, hcore⟩ := core F hF ψ hψ laminf lam hinf hlam (Idx n d) B hBs hBd (db.map eA) hsd
  refine ⟨S₁, fun S hS => ?_⟩
  obtain ⟨ρ, U, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcore S hS
  have hcoI : ∀ T, hCo (Ainf F) σ b T = eI T := fun T => (heI T).symm
  have hcoV : ∀ v T, hCo (Fv F v) σ b T = eV v T := fun v T => (heV v T).symm
  obtain ⟨g1, g2⟩ := GlobalTheory.T.approximate_identity_product_bumps (HermR (Ainf F) σ n) (Ainf F) (Idx n d) eI ρ
    (fun k => ⟨(h1 k).1, (h1 k).2.1, (h1 k).2.2.1⟩) h2
  have g3 := fun v => GlobalTheory.T.product_neighbourhoods_shrink_compact_open (HermR (Fv F v) σ n) (Fv F v) (Idx n d) (eV v) (fun k => U k v)
    (fun k => h3 k v) (h4 v)
  have hρe : ∀ k, (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i)) = fun T => ∏ i, ρ k (eI T i) := fun k => by
    funext T
    rw [hcoI]
  have hUe : ∀ k v, hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v) =
      eV v ⁻¹' Set.pi Set.univ (fun _ => U k v) := fun k v => by
    ext T
    simp only [Set.mem_preimage, hcoV]
  set ρh : ℕ → HermR (Ainf F) σ n → ℝ := fun k T => ∏ i, ρ k (hCo (Ainf F) σ b T i) with hρh
  set Uh : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n) :=
    fun k v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v) with hUh
  have hτ : ∀ k, testH σ b (ρh k) S (Uh k) = fun y => powT (testT (ρ k) S (U k)) (eA y) := fun k => by
    funext y
    rw [heA]
    exact testH_eq σ b (ρ k) S (U k) y
  have hf : ∀ k, fouH σ ψ db (testH σ b (ρh k) S (Uh k)) =
      fun y => fouP ψ Bm (db.map eA) (powT (testT (ρ k) S (U k))) (eA y) := fun k => by
    funext y
    simp only [fouH, fouP]
    rw [hemb.integral_map]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hτ, hpair]
  have hI : ∀ k, ∫ w, testH σ b (ρh k) S (Uh k) w ∂db = ∫ x, powT (testT (ρ k) S (U k)) x ∂(db.map eA) := fun k => by
    rw [hemb.integral_map, hτ]
  have hmI : (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n).map eI = Measure.pi fun _ : Idx n d => laminf := by
    rw [← GlobalTheory.T.hermitian_coordinates_measure_preserving F E σ hCM (Ainf F) d b laminf hinf.1 n]
    congr 1
    funext T
    exact (heI T)
  have hmV : ∀ v, (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n).map (eV v) = Measure.pi fun _ : Idx n d => lam v := fun v => by
    rw [← GlobalTheory.T.hermitian_coordinates_measure_preserving F E σ hCM (Fv F v) d b (lam v) (hlam v).1 n]
    congr 1
    funext T
    exact (heV v T)
  have hembI : MeasurableEmbedding eI := eI.toHomeomorph.measurableEmbedding
  have hembV : ∀ v, MeasurableEmbedding (eV v) := fun v => (eV v).toHomeomorph.measurableEmbedding
  have hρI : ∀ k, ∫ y, ρh k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) =
      (∫ y, ρ k y ∂laminf) ^ Fintype.card (Idx n d) := fun k => by
    have e1 : ∫ y, ρh k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) =
        ∫ x, ∏ i, ρ k (x i) ∂((GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n).map eI) := by
      refine Eq.trans ?_ (hembI.integral_map (μ := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)
        (fun x => ∏ i, ρ k (x i))).symm
      exact integral_congr_ae (ae_of_all _ fun T => by simp only [hρh, hcoI])
    rw [e1, hmI, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ => ρ k), Finset.prod_const, Finset.card_univ]
  have hUV : ∀ k v, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (Uh k v) =
      (lam v (U k v)) ^ Fintype.card (Idx n d) := fun k v => by
    have e1 : Uh k v = eV v ⁻¹' Set.pi Set.univ (fun _ => U k v) := hUe k v
    rw [e1]
    calc GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (eV v ⁻¹' Set.pi Set.univ (fun _ => U k v))
        = ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n).map (eV v)) (Set.pi Set.univ (fun _ => U k v)) :=
          ((hembV v).map_apply (μ := GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) _).symm
      _ = (lam v (U k v)) ^ Fintype.card (Idx n d) := by
          rw [hmV, Measure.pi_pi, Finset.prod_const, Finset.card_univ]
  have hUpos : ∀ k v, 0 < lam v (U k v) := fun k v =>
    (h3 k v).2.1.measure_pos (lam v) ⟨0, (h3 k v).2.2⟩
  have hUfin : ∀ k v, lam v (U k v) ≠ ⊤ := fun k v => (h3 k v).1.measure_lt_top.ne
  have hUr : ∀ k v, (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (Uh k v)).toReal =
      (lam v (U k v)).toReal ^ Fintype.card (Idx n d) := fun k v => by
    rw [hUV, ENNReal.toReal_pow]
  have hcont : ∀ k, Continuous (testH σ b (ρh k) S (Uh k)) := fun k => by
    rw [hτ]
    exact (h5 k).1.comp eA.continuous
  have hcs : ∀ k, HasCompactSupport (testH σ b (ρh k) S (Uh k)) := fun k => by
    rw [hτ]
    exact (h5 k).2.comp_homeomorph eA.toHomeomorph
  have hint : ∀ k, Integrable (fouH σ ψ db (testH σ b (ρh k) S (Uh k))) db := fun k => by
    rw [hf]
    exact (hemb.integrable_map_iff).1 (h6 k)
  refine ⟨ρh, Uh, fun k => ?_, ?_, fun k v => ?_, fun v => ?_, fun k => ⟨hint k, fun z => ?_⟩, fun k => ?_,
    fun k y => ?_, fun y => ?_⟩
  · have e := hρe k
    refine ⟨?_, ?_, ?_, ?_⟩
    · change Continuous (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i))
      rw [e]
      exact (g1 k).1
    · change HasCompactSupport (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i))
      rw [e]
      exact (g1 k).2.1
    · intro T
      exact Finset.prod_nonneg fun i _ => (h1 k).2.2.1 _
    · rw [hρI]
      exact pow_pos (h1 k).2.2.2 _
  · have e : (fun k => tsupport (ρh k)) = fun k => tsupport (fun T => ∏ i, ρ k (eI T i)) := by
      funext k
      exact congrArg tsupport (hρe k)
    rw [e]
    exact g2
  · have e := hUe k v
    obtain ⟨c1, c2, c3⟩ := (g3 v).1 k
    refine ⟨?_, ?_, ?_, ?_⟩
    · change IsCompact (hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v))
      rw [e]
      exact c1
    · change IsOpen (hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v))
      rw [e]
      exact c2
    · change (0 : HermR (Fv F v) σ n) ∈ hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v)
      rw [e]
      exact c3
    · rw [hUr]
      exact pow_pos (ENNReal.toReal_pos (hUpos k v).ne' (hUfin k v)) _
  · have e : (fun k => Uh k v) = fun k => eV v ⁻¹' Set.pi Set.univ (fun _ => U k v) := funext fun k => hUe k v
    rw [e]
    exact (g3 v).2
  · exact hdb'.2 _ (hcont k) (hcs k) (hint k) z
  · rw [hI, h7, hρI, mul_pow]
    congr 1
    · push_cast
      rfl
    · simp only [hUr]
      push_cast
      rw [Finset.prod_pow]
  · rw [hf, hI]
    exact h8 k _
  · have hlim := h9 (eA y)
    simp only [hf, hI]
    have e : (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) =
        {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S}.indicator (fun _ => (1 : ℂ)) (eA y) := by
      by_cases hy : hermFin σ y ∈ intH σ b n S
      · have h' : eA y ∈ {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S} := by
          have := (mem_intH_iff σ b S y).1 hy
          rwa [← heA] at this
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem h']
      · have h' : eA y ∉ {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S} := by
          intro h
          apply hy
          refine (mem_intH_iff σ b S y).2 ?_
          rwa [← heA]
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem h']
    rw [e]
    exact hlim

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProductStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_measure_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v ∧ 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k, Integrable (fouH σ ψ db (testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, fouH σ ψ db (testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖fouH σ ψ db (testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ w, testH σ b (ρ k) S (U k) w ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => fouH σ ψ db (testH σ b (ρ k) S (U k)) y / ∫ w, testH σ b (ρ k) S (U k) w ∂db) Filter.atTop (nhds ((intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx <;> assumption)
end

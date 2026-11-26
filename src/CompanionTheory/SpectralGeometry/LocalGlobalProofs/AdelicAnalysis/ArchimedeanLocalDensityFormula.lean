module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanCoordinateMeasureTransport

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianRankOneHomeomorphBase
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.HermOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem sig_sig (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h⟩ := hcm
  let τ : E →+* ℂ := (inferInstance : Nonempty (E →+* ℂ)).some
  apply τ.injective
  rw [h τ, h τ, star_star]

theorem exists_sig_ne (hcm : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  obtain ⟨-, htc, -, h⟩ := hcm
  let τ : E →+* ℂ := (inferInstance : Nonempty (E →+* ℂ)).some
  have hc : (InfinitePlace.mk τ).IsComplex := htc.isComplex _
  rw [InfinitePlace.isComplex_mk_iff] at hc
  by_contra hall
  push_neg at hall
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h τ x
  rw [hall x] at this
  simpa using this.symm

theorem trace_sig (hcm : IsCMExt F E σ) (y : E) :
    Algebra.trace F E (σ y) = Algebra.trace F E y := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig hcm)) (AlgHom.ext (sig_sig hcm))
  have h : (e.toLinearEquiv).conj (Algebra.lmul F E y) = Algebra.lmul F E (σ y) := by
    ext z
    have h1 : e.toLinearEquiv.symm z = σ z := rfl
    have h2 : ∀ w, e.toLinearEquiv w = σ w := fun _ => rfl
    have h3 : ∀ w, e w = σ w := fun _ => rfl
    have h4 : ∀ w, e.symm w = σ w := fun _ => rfl
    simp [LinearEquiv.conj_apply, h1, h2, h3, h4, sig_sig hcm]
  rw [Algebra.trace_apply, Algebra.trace_apply]
  show LinearMap.trace F E (Algebra.lmul F E (σ y)) = LinearMap.trace F E (Algebra.lmul F E y)
  rw [← h, LinearMap.trace_conj']

theorem add_sig_eq_trace (hcm : IsCMExt F E σ) (y : E) :
    y + σ y = algebraMap F E (Algebra.trace F E y) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨x, hx⟩ := exists_sig_ne hcm
  set θ : E := x - σ x with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσθ : σ θ = -θ := by simp [hθ, sig_sig hcm]
  have htr : Algebra.trace F E θ = 0 := by
    have h := trace_sig hcm θ
    rw [hσθ, map_neg] at h
    have h2 : (2 : F) * Algebra.trace F E θ = 0 := by linear_combination -h
    simpa using h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσs : ∀ (c : F) (w : E), σ (c • w) = c • σ w := fun c w => by simp [Algebra.smul_def]
    have h2 := congrArg σ hst
    rw [map_add (f := _), hσs, hσs, map_one, hσθ, map_zero] at h2
    have h3 : (2 * t) • θ = 0 := by
      have : (2 * t) • θ = (s • (1 : E) + t • θ) - (s • (1 : E) + t • -θ) := by
        simp only [smul_neg, mul_smul, two_smul]
        abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by simpa [hθ0] using h3
    refine ⟨?_, ht⟩
    simpa [ht] using hst
  let bb : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hbb : ∀ i, bb i = ![(1 : E), θ] i := fun i => by
    simp [bb]
  have hmaps : (LinearMap.id + σ.toLinearMap : E →ₗ[F] E) =
      (Algebra.linearMap F E) ∘ₗ Algebra.trace F E := by
    refine bb.ext fun i => ?_
    fin_cases i
    · have h1 : Algebra.trace F E (1 : E) = 2 := by
        have := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
        simpa [hfr] using this
      simp [hbb, h1]
      rw [map_ofNat]
      norm_num
    · simp [hbb, htr, hσθ]
  simpa using LinearMap.congr_fun hmaps y

end Field

section Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]

theorem trace_tmul (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : r ⊗ₜ[F] e = r • ((1 : R) ⊗ₜ[F] e) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = (Algebra.lmul F E e).baseChange R := by
    ext z
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, Algebra.trace_apply]
  show r * LinearMap.trace R _ (Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)) = _
  rw [h2, LinearMap.trace_baseChange]

theorem add_sigR_eq_trace (hcm : IsCMExt F E σ) (z : R ⊗[F] E) :
    z + sigR R σ z = (Algebra.trace R (R ⊗[F] E) z) ⊗ₜ[F] (1 : E) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have h1 : sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by simp [sigR]
    rw [h1, ← TensorProduct.tmul_add, add_sig_eq_trace hcm, trace_tmul,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_comm]
  | add a c ha hc =>
    rw [map_add (f := _), map_add (f := _), TensorProduct.add_tmul, ← ha, ← hc]
    abel

end Ring

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]

def tH (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

theorem tH_hermScal (hcm : IsCMExt F E σ) (r : R) : tH R σ (hermScal R σ r) = r := by
  have h1 : Algebra.trace F E (1 : E) = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
    simpa [hcm.2.2.1] using this
  have h2 : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
    rw [← map_mul]
    norm_num
  show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r
  rw [trace_tmul, h1]
  linear_combination r * h2

theorem hermScal_tH (hcm : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (tH R σ S) = S := by
  apply Subtype.ext
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  set z : R ⊗[F] E := (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 with hz
  have hfix : sigR R σ z = z := S.2 0 0
  have hs := add_sigR_eq_trace R hcm z
  rw [hfix] at hs
  show (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z) ⊗ₜ[F] (1 : E) = z
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', ← hs, ← two_smul F z, smul_smul]
  norm_num

variable [TopologicalSpace R] [IsTopologicalRing R]

def hermHomeo (hcm : IsCMExt F E σ) : HermR R σ 1 ≃ₜ R :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { toFun := tH R σ
    invFun := hermScal R σ
    left_inv := hermScal_tH R hcm
    right_inv := tH_hermScal R hcm
    continuous_toFun := continuous_const.mul
      ((IsModuleTopology.continuous_of_linearMap (R := R) (Algebra.trace R (R ⊗[F] E))).comp
        ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)))
    continuous_invFun := Continuous.subtype_mk (continuous_pi fun _ => continuous_pi fun _ =>
      IsModuleTopology.continuous_of_linearMap (R := R) (Algebra.linearMap R (R ⊗[F] E))) _ }

variable [MeasurableSpace R] [BorelSpace R]

theorem map_coordHerm (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    [SigmaFinite lam] : (coordHerm R σ b lam 1).map (hermHomeo R hcm) = lam := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  haveI hT : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => by
      have h := p.2
      rw [Subsingleton.elim p.1.1 p.1.2] at h
      exact lt_irrefl _ h⟩
  let ψ : R → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun r => (fun _ => r, fun p => hT.elim p)
  have hψ : MeasurableEmbedding ψ := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun q => q.1 0) ?_ ?_ ?_ ?_
    · refine Measurable.prodMk (Measurable.of_eval fun _ => measurable_id) ?_
      exact Measurable.of_eval fun p => hT.elim p
    · have : Set.range ψ = Set.univ := by
        ext q
        simp only [Set.mem_range, Set.mem_univ, iff_true]
        refine ⟨q.1 0, Prod.ext ?_ (Subsingleton.elim _ _)⟩
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro r
      rfl
  ext s hs
  have hfun : (fun S : HermR R σ 1 =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} =>
          (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))) = ψ ∘ hermHomeo R hcm := by
    funext S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  have hemb : MeasurableEmbedding (ψ ∘ hermHomeo R hcm) :=
    hψ.comp (hermHomeo R hcm).measurableEmbedding
  have hpi : Measure.pi (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam) =
      Measure.dirac (fun p => hT.elim p) := Measure.pi_of_empty _ _
  have himg : (ψ ∘ hermHomeo R hcm) '' (hermHomeo R hcm ⁻¹' s) =
      ((fun a : Fin 1 → R => a 0) ⁻¹' s) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨hS, Set.mem_univ _⟩
    · rintro ⟨hq, -⟩
      refine ⟨(hermHomeo R hcm).symm (q.1 0), ?_, ?_⟩
      · simpa using hq
      · refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp [ψ]
  rw [Measure.map_apply (hermHomeo R hcm).measurable hs, coordHerm, hfun, hemb.comap_apply, hpi, himg,
    Measure.prod_prod, measure_univ, mul_one]
  exact (measurePreserving_funUnique lam (Fin 1)).measure_preimage hs.nullMeasurableSet

end Main

end GlobalTheory.CompanionTheory.SW.BB.HermOne
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfDens

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
  [Algebra F R]

theorem sigR_sigR (hs : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [sigR, hs]
  | add a c ha hc => rw [map_add (f := _), map_add (f := _), ha, hc]

theorem sigR_inclR (y : E) : sigR R σ (inclR R y) = inclR R (σ y) := by
  simp [sigR, inclR]

theorem sigR_hR (hs : ∀ x, σ (σ x) = x) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R hs, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gramR_mem (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := fun a c => sigR_hR R hs hJ (X c) (X a)

end Alg

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem e_half_trace {σ : E →ₐ[F] E} {M d : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → Ainf F ⊗[F] E,
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) =
        cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y))
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (gramR (Ainf F) σ J X 0 0)) w =
      (1 / 2 : ℝ) * (xw e b X w ⬝ᵥ (B.map (ρ w) *ᵥ xw e b X w)) := by
  let ew : Ainf F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (e : Ainf F →+* _)
  have hew : ∀ a, ew a = e a w := fun _ => rfl
  have hcomp : ew.comp (algebraMap F (Ainf F)) = ρ w := RingHom.ext fun x => hρ x w
  have hx : xw e b X w = ew ∘ cv (Ainf F) b (X 0) := rfl
  have hm : B.map (ρ w) = (B.map (algebraMap F (Ainf F))).map ew := by
    rw [← hcomp]
    ext i j
    rfl
  have hhalf : ρ w (1 / 2) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [← hew, map_mul, hew, hρ, hhalf]
  show _ * ew (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J (X 0) (X 0))) = _
  rw [hB, hx, hm, RingHom.map_dotProduct]
  have hv : ⇑ew ∘ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b (X 0)) =
      (B.map (algebraMap F (Ainf F))).map ew *ᵥ (⇑ew ∘ cv (Ainf F) b (X 0)) :=
    funext fun i => RingHom.map_mulVec ew _ _ i
  rw [hv]

end Real

theorem infDens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM d b B hB ρ e he hρ Pm laminf hlam hmap Dinf hDc hD0 hDinf U hU
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
  haveI : SigmaFinite laminf := inferInstance
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at h1
    simpa using h1.symm
  have hs : ∀ x, σ (σ x) = x := HermOne.sig_sig hcm
  set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.2 (Real.sqrt_nonneg _)

  let tt := HermOne.hermHomeo (Ainf F) (σ := σ) hcm
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  let τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ) := tt.trans eH
  have hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) *
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)) :=
    fun _ => rfl
  have hpush : (coordHerm (Ainf F) σ b laminf 1).map τ = ENNReal.ofReal κ • volume := by
    have h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt := rfl
    rw [h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable,
      HermOne.map_coordHerm (Ainf F) hcm b laminf, hmap]
  set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' U with hU'def
  have hU' : MeasurableSet U' := τ.symm.measurable hU
  have hpre : τ ⁻¹' U' = U := by
    ext S
    simp [hU'def]

  have hR1 : ∫⁻ S in U, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))))
        ∂(coordHerm (Ainf F) σ b laminf 1) =
      ENNReal.ofReal (κ ^ (2 * M)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have h2 := setLIntegral_map (μ := coordHerm (Ainf F) σ b laminf 1) (g := τ)
      (f := fun y => ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y)) hU'
      (continuous_const.mul hDc).measurable.ennreal_ofReal τ.measurable
    rw [hpre, hpush] at h2
    simp only [hτ] at h2
    rw [← h2, Measure.restrict_smul, lintegral_smul_measure]
    have h3 : ∀ y, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y) =
        ENNReal.ofReal (κ ^ (2 * M - 1)) * ENNReal.ofReal (Dinf y) :=
      fun y => ENNReal.ofReal_mul (pow_nonneg hκ0 _)
    simp only [h3]
    rw [lintegral_const_mul _ (hDc.measurable.ennreal_ofReal), smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul hκ0, ← pow_succ', show 2 * M - 1 + 1 = 2 * M by omega]

  let Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ) :=
    fun X w => xw e b X w
  have hcoord := (GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hcm (Ainf F) d b laminf hlam M).2.1
  have hΦm : Measurable Φ := by
    have hc : Continuous fun (z : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) =>
        e (z p) w :=
      continuous_pi fun w => continuous_pi fun p =>
        (continuous_apply w).comp (eH.continuous.comp (continuous_apply p))
    exact hc.measurable.comp hcoord.measurable
  have hpushL := GlobalTheory.T.archimedean_coordinate_measure_transport F E σ hcm M d b e he laminf hlam hmap
  let Q : (InfinitePlace F → Fin M × Fin d → ℝ) → (InfinitePlace F → ℝ) :=
    fun x w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))
  have hQc : Continuous Q := by
    refine continuous_pi fun w => continuous_const.mul ?_
    exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
  let G : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)))
  have hGm : Measurable G := by
    have hc : Continuous fun x : InfinitePlace F → Fin M × Fin d → ℝ =>
        Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)) := by
      refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact hc.measurable.ennreal_ofReal
  have hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U) = Φ ⁻¹' (Q ⁻¹' U') := by
    ext X
    have hmem := gramR_mem (Ainf F) hs hJ.1 X
    have hQ : Q (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩ := by
      funext w
      rw [hτ]
      exact (e_half_trace b B hB ρ e hρ X w).symm
    simp only [Set.mem_preimage, hU'def]
    rw [hQ, Homeomorph.symm_apply_apply]
    constructor
    · rintro ⟨S, hS, hSX⟩
      have : (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S := Subtype.ext hSX.symm
      rwa [this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hL1 : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X)
        ∂(coordW (Ainf F) b laminf 1 M) =
      ENNReal.ofReal (κ ^ (M * d)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have hA : MeasurableSet (Q ⁻¹' U') := hQc.measurable hU'
    have h2 := setLIntegral_map (μ := coordW (Ainf F) b laminf 1 M) hA hGm hΦm
    rw [hset]
    have h3 : ∀ X, ENNReal.ofReal (gaussQ e b Pm X) = G (Φ X) := fun _ => rfl
    simp only [h3]
    rw [← h2]
    have h4 : (coordW (Ainf F) b laminf 1 M).map Φ =
        ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) :=
      hpushL
    rw [h4, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    exact congrArg _ (hDinf U' hU')
  rw [hL1, hR1, hd, mul_comm M 2]

end GlobalTheory.CompanionTheory.SW.BB.InfDens
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_density_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | exact GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | (intros; apply GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens <;> assumption)
end

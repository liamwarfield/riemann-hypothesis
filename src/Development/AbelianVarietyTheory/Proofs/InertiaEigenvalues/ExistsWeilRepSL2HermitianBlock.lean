module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSelfDualPiHaarTraceStarDotProductUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSelfDualPiHaarTraceStarDotProductUnramified
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PiSelfDual

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem finite : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)

theorem isModuleTopology : IsModuleTopology F E := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Module.Finite F E := finite
  exact IsModuleTopology.iso (R := F) (A := Fin 2 → F)
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Unram.finrank_eq (F := F) (E := E)]))

theorem star_smul_F {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, Unram.star_fix (E := E) a, mul_comm]

theorem trace_star (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  apply (algebraMap F E).injective
  rw [(GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1, (GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1, star_star, add_comm]

def trForm (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp [star_add, add_dotProduct])
    (fun a c b => by rw [star_smul_F, smul_dotProduct, LinearMap.map_smul])
    (fun c b b' => by simp [dotProduct_add])
    (fun a c b => by rw [dotProduct_smul, LinearMap.map_smul])

theorem trForm_apply (r : ℕ) (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trForm_isSymm (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [trForm_apply, trForm_apply, star_dotProduct, trace_star]

theorem trForm_separatingLeft (r : ℕ) (c : Fin r → E) (hc : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  classical
  funext i
  obtain ⟨e, -, he⟩ := (GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).2.1
  have h0 := hc (Pi.single i (c i * e))
  rw [trForm_apply, dotProduct_single, Pi.star_apply] at h0
  have h1 : algebraMap F E (Algebra.trace F E (star (c i) * (c i * e))) = star (c i) * c i * (e + star e) := by
    rw [(GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1]
    simp only [star_mul, star_star]
    ring
  rw [h0, map_zero, he, mul_one] at h1
  rcases mul_eq_zero.1 h1.symm with h | h
  · simpa using h
  · simpa using h

theorem trForm_nondegenerate (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate :=
  ⟨fun c hc => trForm_separatingLeft r c hc, fun b hb => trForm_separatingLeft r b (fun c => by
    rw [(trForm_isSymm (F := F) r).eq]; exact hb c)⟩

def intLat (r : ℕ) : AddSubgroup (Fin r → E) :=
  haveI : IsUltrametricDist E := Unram.ultraE F
  { carrier := {b | ∀ i, ‖b i‖ ≤ 1}
    add_mem' := fun {a b} ha hb i => by
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    zero_mem' := fun i => by simp
    neg_mem' := fun {a} ha i => by simpa using ha i }

theorem intLat_eq (r : ℕ) :
    ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) =
      Set.univ.pi (fun _ => Metric.closedBall (0 : E) 1) := by
  ext b
  simp [intLat, Metric.mem_closedBall, dist_zero_right]

theorem dual_intLat (r : ℕ) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    {y : Fin r → E | ∀ x ∈ intLat (F := F) (E := E) r, ψ (trForm (F := F) r x y) = 1} =
      ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
  classical
  haveI : IsUltrametricDist E := Unram.ultraE F
  have key := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  ext y
  constructor
  · intro hy i
    refine (key (y i)).1 (fun e he => ?_)
    have hx : Pi.single i (star e) ∈ intLat (F := F) (E := E) r := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [Unram.norm_star (F := F), he]
      · simp [Pi.single_apply, hj]
    have := hy _ hx
    rwa [trForm_apply, Pi.star_single, star_star, single_dotProduct] at this
  · intro hy x hx
    have hn : ‖star x ⬝ᵥ y‖ ≤ 1 := by
      unfold dotProduct
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
      rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hy i)
    have := (key 1).2 (by simp) (star x ⬝ᵥ y) hn
    rwa [mul_one] at this

end GlobalTheory.JR.PiSelfDual


open GlobalTheory.JR.PiSelfDual in
theorem GlobalTheory.JR.selfDual_pi_trace : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  intro F E _ _ _ _ _ r M ψ hψ
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : LocallyCompactSpace E := Unram.lcE F
  haveI : IsUltrametricDist E := Unram.ultraE F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : Module.Finite F E := finite
  haveI : IsModuleTopology F E := isModuleTopology
  haveI : BorelSpace (Fin r → E) := Pi.borelSpace
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hvol : (Measure.pi fun _ : Fin r => M.μE) ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) = 1 := by
    rw [intLat_eq, Measure.pi_pi]
    simp [M.volE]
  have hopen : IsOpen ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero)
  have hcpt : IsCompact ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have h := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_isSymm r) (trForm_nondegenerate r)
    (Measure.pi fun _ => M.μE) inferInstance).1 (intLat r) hopen hcpt |>.1
  refine h.2 ?_
  rw [dual_intLat r ψ hψ, hvol, one_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  first | exact @GlobalTheory.JR.selfDual_pi_trace | exact GlobalTheory.JR.selfDual_pi_trace | (intros; apply GlobalTheory.JR.selfDual_pi_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportSelfDualHaarMeasureKernelAddEquiv
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TransportSD

theorem map_map_equiv_left {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · have hg' : ¬ AEMeasurable (g ∘ e) μ := by rwa [← aemeasurable_map_equiv_iff e]
    by_cases hμ : μ = 0
    · simp [hμ]
    · have heμ : Measure.map e μ ≠ 0 := (Measure.map_ne_zero_iff e.measurable.aemeasurable).mpr hμ
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hg heμ,
        Measure.map_of_not_aemeasurable_of_ne_zero hg' hμ]

open scoped Classical in
theorem map_map_equiv_right {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) :
    (if AEMeasurable T μ then μ.map T else 0).map e =
      (if AEMeasurable (e ∘ T) μ then μ.map (e ∘ T) else 0) := by
  by_cases hT : AEMeasurable T μ
  · have hT' := e.measurable.comp_aemeasurable hT
    simpa only [if_pos hT, if_pos hT'] using
      AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hT
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro h
      apply hT
      have := e.symm.measurable.comp_aemeasurable h
      simpa [Function.comp_def] using this
    simp only [if_neg hT, if_neg hT', Measure.map_zero]

end GlobalTheory.TransportSD

open GlobalTheory.TransportSD in
theorem GlobalTheory.transport_selfDual_fourB :
    ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V']
    (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ),
    (SelfDual μ B ∧ (∀ x : V, AEMeasurable (x + ·) μ) →
      SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y)) ∧
        (∀ x : V', AEMeasurable (x + ·) (Measure.map h.symm μ))) ∧
    ∀ (f : V' → ℂ) (y : V'),
      fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y =
        fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  let he : V ≃ₜ V' := { toEquiv := h.symm.toEquiv, continuous_toFun := hs, continuous_invFun := hc }
  let e : V ≃ᵐ V' := he.toMeasurableEquiv
  have he_eq : (e : V → V') = h.symm := rfl
  have hμ : Measure.map h.symm μ = Measure.map e μ := by rw [he_eq]
  have four : ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
    intro f y
    unfold fourB
    rw [hμ, integral_map_equiv]
    congr 1
    funext v
    rw [he_eq]
    simp
  -- The old zero fallback in `Measure.map` made left invariance imply AE measurability.
  refine ⟨fun ⟨hsd, hAe⟩ => ?_, four⟩
  have hcomp (x' : V') :
      (fun y' => x' + y') ∘ (e : V → V') = (e : V → V') ∘ (fun v => h x' + v) := by
    funext v; rw [he_eq]; simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨hH, -⟩ := hsd
    rw [hμ]
    have h1 : IsFiniteMeasureOnCompacts (Measure.map e μ) := by
      refine ⟨fun K hK => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have : (e : V → V') ⁻¹' K = h '' K := by
        ext v; rw [he_eq]; simp [Set.mem_image]
        constructor
        · intro hv; exact ⟨h.symm v, hv, by simp⟩
        · rintro ⟨w, hw, rfl⟩; simpa using hw
      rw [this]
      exact (hK.image hc).measure_lt_top
    have h2 : (Measure.map e μ).IsAddLeftInvariant := by
      refine ⟨fun x' => ?_⟩
      rw [map_map_equiv_left, hcomp,
        ← AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable (hAe (h x')),
        hH.toIsAddLeftInvariant.map_add_left_eq_self (h x')]
    have h3 : (Measure.map e μ).IsOpenPosMeasure := by
      refine ⟨fun U hU hne => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have hU' : IsOpen ((e : V → V') ⁻¹' U) := hU.preimage (by rw [he_eq]; exact hs)
      have hne' : ((e : V → V') ⁻¹' U).Nonempty := by
        obtain ⟨u, hu⟩ := hne
        exact ⟨h u, by rw [he_eq]; simpa using hu⟩
      exact hU'.measure_ne_zero μ hne'
    exact { toIsFiniteMeasureOnCompacts := h1, toIsAddLeftInvariant := h2, toIsOpenPosMeasure := h3 }
  · intro f hf y
    have hf' : IsTest (fun v => f (h.symm v)) :=
      ⟨hf.1.comp_continuous hs, hf.2.comp_homeomorph he⟩
    rw [four]
    have : (fun v => fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f (h.symm v)) =
        fourB μ B (fun v => f (h.symm v)) := by
      funext v; rw [four]; simp
    rw [this, hsd.2 _ hf' (h y)]
    simp
  · intro x'
    rw [hμ, aemeasurable_map_equiv_iff e, hcomp]
    exact e.measurable.comp_aemeasurable (hAe (h x'))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEqSumCoordsOfAlgEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEqSumCoordsOfAlgEquiv
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_pi_fin_self {F : Type} [Field F] (r : ℕ) (x : Fin r → F) :
    Algebra.trace F (Fin r → F) x = ∑ i, x i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun F (Fin r)), Matrix.trace]
  congr 1
  ext i
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_apply]

theorem trace_eq_sum_coords_of_algEquiv {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ)
    (e : K ≃ₐ[F] (Fin r → F)) (k : K) : Algebra.trace F K k = ∑ i, e k i := by
  rw [← Algebra.trace_eq_of_algEquiv e k, trace_pi_fin_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEqSumCoordsOfAlgEquivStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eq_sum_of_algEquiv_pi : ∀ {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ) (e : K ≃ₐ[F] (Fin r → F)) (k : K), Algebra.trace F K k = ∑ i, e k i := by
  first | exact @GlobalTheory.trace_eq_sum_coords_of_algEquiv | exact GlobalTheory.trace_eq_sum_coords_of_algEquiv | (intros; apply GlobalTheory.trace_eq_sum_coords_of_algEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceTowerFiniteEtaleHermitianPair
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceTowerFiniteEtaleHermitianPair
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_tower_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (z : A.L), Algebra.trace F A.K (Algebra.trace A.K A.L z) = Algebra.trace F E (Algebra.trace E A.L z) := by
  intro F E _ _ _ _ hU A z
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  have hE : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  have hK : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free E A.L := Module.Free.of_equiv hE.equiv
  haveI : Module.Finite E A.L := Module.Finite.equiv hE.equiv
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hK.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hK.equiv
  rw [Algebra.trace_trace, Algebra.trace_trace]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceTowerFiniteEtaleHermitianPairStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_tower_finiteEtaleHermitianPair : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (z : A.L), Algebra.trace F A.K (Algebra.trace A.K A.L z) = Algebra.trace F E (Algebra.trace E A.L z) := by
  first | exact @GlobalTheory.trace_tower_et | exact GlobalTheory.trace_tower_et | (intros; apply GlobalTheory.trace_tower_et <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitEtaleHermitianPairIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitEtaleHermitianPairIsometry
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.SplitEt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem algebraMap_norm_eq_mul_star (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut)
    (fun x => by rw [starRingAut_apply]; exact Unram.star_fix (E := E) x)
  have hσz : ∀ y, σ y = star y := fun y => rfl
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    intro h
    apply hy
    rw [← hσz, ← h]
    rfl
  classical
  have hle := AlgEquiv.card_le (F := F) (K := E)
  have hge : ({1, σ} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) := Finset.card_le_univ _
  rw [Finset.card_pair hσ] at hge
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, h2])
  have huniv : ({1, σ} : Finset (E ≃ₐ[F] E)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hσ, hcard])
  rw [Algebra.norm_eq_prod_automorphisms, ← huniv, Finset.prod_pair hσ, hσz]
  rfl

def piCoord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (r : ℕ) :
    (Fin r → E) ≃ₗ[Fin r → F] (ι → (Fin r → F)) where
  toFun y k i := b.repr (y i) k
  invFun c i := ∑ k, c k i • b k
  map_add' y y' := by ext k i; simp
  map_smul' x y := by ext k i; simp
  left_inv y := by funext i; simp [b.sum_repr]
  right_inv c := by classical ext k i; simp [Finsupp.single_apply]

theorem norm_pi_apply (r : ℕ) (y : Fin r → E) (i : Fin r) :
    Algebra.norm (Fin r → F) y i = Algebra.norm F (y i) := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  classical
  let b := Module.finBasis F E
  let B := Module.Basis.ofEquivFun (piCoord b r)
  have hB : ∀ k, B k = fun _ => b k := by
    intro k; rw [Module.Basis.coe_ofEquivFun]; funext i; simp [piCoord, Pi.single_apply, ite_apply, ite_smul]
  have hBr : ∀ z k, B.repr z k = fun i => b.repr (z i) k := fun z k => by
    rw [Module.Basis.ofEquivFun_repr_apply]; rfl
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det b]
  rw [show (det (Algebra.leftMulMatrix B y)) i = Pi.evalRingHom (fun _ => F) i (det _) from rfl, RingHom.map_det]
  congr 1
  ext k l
  simp [RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul, hB, hBr]

theorem trace_pi_apply (r : ℕ) (z : Fin r → E) : Algebra.trace E (Fin r → E) z = ∑ i, z i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E (Fin r))]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.SplitEt

namespace GlobalTheory.JR.SplitEt

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem push_pi (r : ℕ) : Algebra.IsPushout F E (Fin r → F) (Fin r → E) := by
  refine ⟨?_⟩
  have h := IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap F E)
  have e : (IsScalarTower.toAlgHom F (Fin r → F) (Fin r → E)).toLinearMap = (Algebra.linearMap F E).compLeft (Fin r) :=
    LinearMap.ext fun _ => rfl
  rw [e]
  exact h

abbrev splitEt (r : ℕ) : Et F E :=
  haveI : LocallyCompactSpace F := Unram.lcF E
  letI : MeasurableSpace (Fin r → F) := borel (Fin r → F)
  haveI : BorelSpace (Fin r → F) := ⟨rfl⟩
  letI tL : TopologicalSpace (Fin r → E) := moduleTopology F (Fin r → E)
  letI : MeasurableSpace (Fin r → E) := borel (Fin r → E)
  haveI : BorelSpace (Fin r → E) := ⟨rfl⟩
  haveI : IsModuleTopology F (Fin r → E) := ⟨rfl⟩
  { K := Fin r → F
    L := Fin r → E
    push := push_pi F E r
    star_K := fun x => by funext i; exact Unram.star_fix (E := E) (x i)
    star_E := fun y => rfl }

end GlobalTheory.JR.SplitEt

theorem GlobalTheory.JR.exists_split_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  intro F E _ _ _ _ _ r
  refine ⟨SplitEt.splitEt F E r, AlgEquiv.refl, LinearEquiv.refl E _, ?_, ?_⟩
  · intro y y'
    show star y ⬝ᵥ y' = Algebra.trace E (Fin r → E) (algebraMap (Fin r → F) (Fin r → E) 1 * star y * y')
    rw [map_one, one_mul, SplitEt.trace_pi_apply]
    simp [dotProduct]
  · intro y i
    show algebraMap F E (Algebra.norm (Fin r → F) y i) = y i * star (y i)
    rw [SplitEt.norm_pi_apply, SplitEt.algebraMap_norm_eq_mul_star]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitEtaleHermitianPairIsometryStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_etaleHermitianPair_isometry : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  first | exact @GlobalTheory.JR.exists_split_et | exact GlobalTheory.JR.exists_split_et | (intros; apply GlobalTheory.JR.exists_split_et <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuous
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem et_equiv_continuous (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous j ∧ Continuous j.symm := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : CompleteSpace F := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace F
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : FiniteDimensional F (Fin r → E) := inferInstance
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  refine ⟨?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)
  · exact LinearMap.continuous_of_finiteDimensional (j.symm.toLinearMap.restrictScalars F)

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuousStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), Continuous j ∧ Continuous j.symm := by
  first | exact @GlobalTheory.JR.et_equiv_continuous | exact GlobalTheory.JR.et_equiv_continuous | (intros; apply GlobalTheory.JR.et_equiv_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApply
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApply
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem slices_test {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P]
    [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ) (hT : ∀ φ, IsTest φ → IsTest (T φ)) (hT0 : T 0 = 0)
    (f : P × V × Q → ℂ) (hf : IsTest f) :
    (∀ p q, IsTest (fun v => f (p, v, q))) ∧
      IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hC : IsCompact (tsupport f) := hcs
  have hz : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have h1 : ∀ p q, IsTest (fun v => f (p, v, q)) := by
    intro p q
    refine ⟨hlc.comp_continuous (by fun_prop), ?_⟩
    have hcl : IsClosed ({x : P × V × Q | x.1 = p} ∩ {x | x.2.2 = q}) :=
      (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const)
    refine HasCompactSupport.intro ((hC.inter_right hcl).image (continuous_fst.comp continuous_snd)) ?_
    intro v hv
    apply hz
    intro hmem
    exact hv ⟨(p, v, q), ⟨hmem, rfl, rfl⟩, rfl⟩
  refine ⟨h1, ?_⟩
  set Φ : P × Q → V → ℂ := fun a v => f (a.1, v, a.2) with hΦdef
  set CV : Set V := (fun x : P × V × Q => x.2.1) '' tsupport f with hCV
  have hCVc : IsCompact CV := hC.image (continuous_fst.comp continuous_snd)
  have hoff : ∀ (a : P × Q) v, v ∉ CV → f (a.1, v, a.2) = 0 := by
    intro a v hv
    exact hz _ (fun h => hv ⟨_, h, rfl⟩)
  have hΦ : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a0
    have hn : IsOpen {z : (P × Q) × V | f (z.1.1, z.2, z.1.2) = f (a0.1, z.2, a0.2)} := by
      have g1 : IsLocallyConstant (fun z : (P × Q) × V => f (z.1.1, z.2, z.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have g2 : IsLocallyConstant (fun z : (P × Q) × V => f (a0.1, z.2, a0.2)) :=
        hlc.comp_continuous (by fun_prop)
      refine isOpen_iff_mem_nhds.2 fun z hz' => ?_
      filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 g1 z, (IsLocallyConstant.iff_eventually_eq _).1 g2 z]
        with y hy1 hy2
      show f (y.1.1, y.2, y.1.2) = f (a0.1, y.2, a0.2)
      rw [hy1, hy2]
      exact hz'
    obtain ⟨u, w, hu, -, hau, hCVw, huw⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := a0)) hCVc hn (by
        rintro ⟨a, v⟩ ⟨ha, -⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rfl)
    filter_upwards [hu.mem_nhds (hau rfl)] with a ha
    funext v
    by_cases hv : v ∈ CV
    · exact huw (show (a, v) ∈ u ×ˢ w from ⟨ha, hCVw hv⟩)
    · show f (a.1, v, a.2) = f (a0.1, v, a0.2)
      rw [hoff a v hv, hoff a0 v hv]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x0
    have e1 : ∀ᶠ x in 𝓝 x0, Φ (x.1, x.2.2) = Φ (x0.1, x0.2.2) :=
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 hΦ _)
    have e2 : ∀ᶠ x in 𝓝 x0, T (Φ (x0.1, x0.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1 :=
      ((continuous_fst.comp continuous_snd).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 (hT _ (h1 _ _)).1 _)
    filter_upwards [e1, e2] with x h h'
    show T (Φ (x.1, x.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1
    rw [h]
    exact h'
  · set K : Set (P × Q) := (fun x : P × V × Q => (x.1, x.2.2)) '' tsupport f with hKdef
    have hK : IsCompact K := hC.image (by fun_prop)
    have hΦK : ∀ a, a ∉ K → Φ a = 0 := by
      intro a ha
      funext v
      exact hz _ (fun h => ha ⟨_, h, rfl⟩)
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hfin : (Set.range (fun a : K => Φ a)).Finite :=
      (hΦ.comp_continuous continuous_subtype_val).range_finite
    set U : Set V := ⋃ h ∈ Set.range (fun a : K => Φ a), tsupport (T h) with hUdef
    have hU : IsCompact U := hfin.isCompact_biUnion (fun h hh => by
      obtain ⟨a, rfl⟩ := hh
      exact (hT _ (h1 _ _)).2.isCompact)
    have hL : IsCompact ((fun z : (P × Q) × V => (z.1.1, z.2, z.1.2)) '' (K ×ˢ U)) :=
      (hK.prod hU).image (by fun_prop)
    refine HasCompactSupport.intro hL ?_
    intro x hx
    by_contra hne
    apply hx
    have ha : (x.1, x.2.2) ∈ K := by
      by_contra hK'
      apply hne
      show T (Φ (x.1, x.2.2)) x.2.1 = 0
      rw [hΦK _ hK', hT0]
      rfl
    refine ⟨((x.1, x.2.2), x.2.1), ⟨ha, ?_⟩, rfl⟩
    exact Set.mem_biUnion ⟨⟨(x.1, x.2.2), ha⟩, rfl⟩ (subset_tsupport _ hne)

theorem slices_test' : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) :=
  fun T hT hT0 f hf => slices_test T hT hT0 f hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApplyStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  first | exact @GlobalTheory.slices_test' | exact GlobalTheory.slices_test' | (intros; apply GlobalTheory.slices_test' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2HermitianBlock
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem sl2Map_nS {F K : Type} [Field F] [CommRing K] [Algebra F K] (t : F) :
    SpecialLinearGroup.map (algebraMap F K) (nS t) = nS (algebraMap F K t) := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![1, t; 0, 1] = !![1, algebraMap F K t; 0, 1]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem sl2Map_wS {F K : Type} [Field F] [CommRing K] [Algebra F K] :
    SpecialLinearGroup.map (algebraMap F K) (wS F) = wS K := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![0, 1; -1, 0] = !![0, 1; -1, 0]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem weilSL2_hermitian : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  intro hW hG F E _ _ _ _ _ r M ψ hψ
  obtain ⟨A, e, j, hj, hNe⟩ := GlobalTheory.T.exists_split_etaleHermitianPair_isometry F E r
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  haveI : CharZero F := Unram.charZero (E := E)
  letI mE : MeasurableSpace E := M.mE
  haveI : BorelSpace E := M.bE
  obtain ⟨hjc, hjsc⟩ := GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous F E A r j
  let jh : A.L ≃ₜ (Fin r → E) := { j.toEquiv with continuous_toFun := hjc, continuous_invFun := hjsc }
  let μE : Measure (Fin r → E) := Measure.pi fun _ => M.μE
  let B : (Fin r → E) → (Fin r → E) → ℂ := fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))
  have hsd : SelfDual μE B := GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified F E r M ψ hψ
  obtain ⟨hT1, hT2⟩ := GlobalTheory.transport_selfDual_fourB j.toAddEquiv hjc hjsc μE B
  have hker : A.kerL ψ ((1 : A.Kˣ) : A.K) = fun x y => B (j.toAddEquiv x) (j.toAddEquiv y) := by
    funext x y
    have h1 := hj x y
    simp only [map_one, one_mul] at h1
    show ψ (Algebra.trace F A.K (((1 : A.Kˣ) : A.K) * Algebra.trace A.K A.L (star x * y))) = ψ (Algebra.trace F E (star (j x) ⬝ᵥ j y))
    rw [Units.val_one, one_mul, GlobalTheory.T.trace_tower_finiteEtaleHermitianPair, h1]
  have hsdL : SelfDual (Measure.map j.toAddEquiv.symm μE) (A.kerL ψ ((1 : A.Kˣ) : A.K)) := by
    rw [hker]; exact (hT1 ⟨hsd, fun x => (continuous_const.add continuous_id).aemeasurable⟩).1
  obtain ⟨γ, Wk, hWk⟩ := hW F E A ψ hψ 1 _ hsdL
  have hγ : γ = 1 := hG F E A ψ hψ 1 _ hsdL A.etaK γ Wk hWk r j (by simpa using hj)
  obtain ⟨hTrE, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  have htr2 : ∀ a : F, Algebra.trace F E (algebraMap F E a) = 2 * a := by
    intro a
    apply (algebraMap F E).injective
    rw [hTrE, Unram.star_fix (F := F) (E := E) a, map_mul, map_ofNat]; ring
  have hnorm : ∀ y : A.L, Algebra.trace F A.K (A.NL y) = Algebra.trace F E (star (j y) ⬝ᵥ j y) / 2 := by
    intro y
    have : star (j y) ⬝ᵥ j y = algebraMap F E (∑ i, e (A.NL y) i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Pi.star_apply, map_sum, hNe y, mul_comm]
    rw [this, htr2, GlobalTheory.T.trace_eq_sum_of_algEquiv_pi r e]; field_simp
  have testj : ∀ φ : (Fin r → E) → ℂ, IsTest φ → IsTest (fun y : A.L => φ (j y)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjc, hφ.2.comp_homeomorph jh⟩
  have testjs : ∀ φ : A.L → ℂ, IsTest φ → IsTest (fun b => φ (j.symm b)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjsc, hφ.2.comp_homeomorph jh.symm⟩
  have hz : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have hW0 : ∀ G, Wk G 0 = 0 := by
    intro G
    have := hWk.1.2.2.2 G 1 0 0 hz hz
    simp only [one_smul, add_zero] at this
    simpa using this
  let ι : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) A.K := SpecialLinearGroup.map (algebraMap F A.K)
  let T : SpecialLinearGroup (Fin 2) F → ((Fin r → E) → ℂ) → (Fin r → E) → ℂ :=
    fun g φ b => Wk (ι g) (fun y => φ (j y)) (j.symm b)
  have hTt : ∀ g φ, IsTest φ → IsTest (T g φ) := fun g φ hφ => testjs _ (hWk.1.1 _ _ (testj φ hφ))
  have hT0 : ∀ g, T g 0 = 0 := by
    intro g; funext b
    show Wk (ι g) (fun y => (0 : (Fin r → E) → ℂ) (j y)) (j.symm b) = 0
    have : (fun y => (0 : (Fin r → E) → ℂ) (j y)) = 0 := rfl
    rw [this, hW0]; rfl
  have hsl : ∀ f : Hn r F E → ℂ, IsTest f → ∀ X : Hn r F E, IsTest (fun y : A.L => f (X.1, j y, X.2.2)) :=
    fun f hf X => testj _ ((GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T 1) (hTt 1) (hT0 1) f hf).1 X.1 X.2.2)
  refine ⟨fun g f X => T g (fun v => f (X.1, v, X.2.2)) X.2.1, ⟨fun g f hf => (GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T g) (hTt g) (hT0 g) f hf).2, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf; funext X
    show Wk (ι 1) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = f X
    rw [map_one, hWk.1.2.1 _ (hsl f hf X)]
    simp
  · intro g h f hf; funext X
    show Wk (ι (g * h)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = Wk (ι g) (fun y => Wk (ι h) (fun y' => f (X.1, j y', X.2.2)) (j.symm (j y))) (j.symm X.2.1)
    simp only [LinearEquiv.symm_apply_apply]
    rw [map_mul, hWk.1.2.2.1 _ _ _ (hsl f hf X)]
  · intro g c f f' hf hf'; funext X
    show Wk (ι g) (fun y => (c • f + f') (X.1, j y, X.2.2)) (j.symm X.2.1) = c * Wk (ι g) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) + Wk (ι g) (fun y => f' (X.1, j y, X.2.2)) (j.symm X.2.1)
    have key : (fun y => (c • f + f') (X.1, j y, X.2.2)) = c • (fun y => f (X.1, j y, X.2.2)) + (fun y => f' (X.1, j y, X.2.2)) := rfl
    rw [key, hWk.1.2.2.2 _ _ _ _ (hsl f hf X) (hsl f' hf' X)]
    rfl
  · intro f hf
    refine ⟨fun t X => ?_, ?_⟩
    · have hι : ι (nS t) = nS (algebraMap F A.K t) := by
        exact sl2Map_nS t
      show Wk (ι (nS t)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = _
      rw [hι, (hWk.2 _ (hsl f hf X)).1]
      have hy := hnorm (j.symm X.2.1)
      rw [LinearEquiv.apply_symm_apply] at hy
      simp only [LinearEquiv.apply_symm_apply, Et.psiK, Units.val_one, mul_one, ← Algebra.smul_def, map_smul, smul_eq_mul, hy, mul_div_assoc]
    · have hι : ι (wS F) = wS A.K := by
        exact sl2Map_wS
      funext X
      show Wk (ι (wS F)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = fourU M ψ f X
      rw [hι, (hWk.2 _ (hsl f hf X)).2.2, hγ, one_mul, hker, hT2]
      have e1 : j.toAddEquiv (j.symm X.2.1) = X.2.1 := j.apply_symm_apply _
      rw [e1]
      show ∫ c, f (X.1, j (j.symm c), X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂μE = ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
      simp only [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2HermitianBlockStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRepSL2_hermitianBlock : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  first | exact @GlobalTheory.weilSL2_hermitian | exact GlobalTheory.weilSL2_hermitian | (intros; apply GlobalTheory.weilSL2_hermitian <;> assumption)
end

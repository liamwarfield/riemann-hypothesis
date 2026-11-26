module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContribution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmallEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsLast
open NumberField

namespace GlobalTheory.SmallIntegerVanishing

theorem eq_zero_of_small (E : Type) [Field E] [NumberField E] (x : RingOfIntegers E)
    (h : ∀ w : InfinitePlace E, w (x : E) < 1) : x = 0 := by
  classical
  by_contra hx
  have hnn : ∀ (w : InfinitePlace E) (y : E), 0 ≤ w y := fun w y => w.1.nonneg y
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have h1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : E)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hne
    exact_mod_cast this
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm] at h1
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at h1
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun w _ => pow_nonneg (hnn w _) _) fun w _ => pow_le_one₀ (hnn w _) (h w).le
  have hlt : w0 (x : E) ^ w0.mult < 1 :=
    pow_lt_one₀ (hnn w0 _) (h w0) NumberField.InfinitePlace.mult_ne_zero
  have h3 : w0 (x : E) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ w0 (x : E) ^ w0.mult :=
    mul_le_of_le_one_right (pow_nonneg (hnn w0 _) _) hle
  linarith

theorem exists_denominator (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ d : RingOfIntegers E, d ≠ 0 ∧ ∀ y ∈ Λ, ∀ a, ∃ x : RingOfIntegers E,
      (x : E) = (d : E) * y a := by
  classical
  obtain ⟨S, hS⟩ := hΛ
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun g => Finset.univ.image fun a => g a)
  refine ⟨(y : RingOfIntegers E), by exact_mod_cast hy0, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    have hint := hy (g a) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨⟨y • g a, hint⟩, ?_⟩
    simp [zsmul_eq_mul]
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add u w _ _ hu hw =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    obtain ⟨x2, h2⟩ := hw a
    refine ⟨x1 + x2, ?_⟩
    calc ((x1 + x2 : RingOfIntegers E) : E) = (x1 : E) + (x2 : E) := rfl
      _ = _ := by rw [h1, h2, Pi.add_apply, mul_add]
  | smul r u _ hu =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    refine ⟨r * x1, ?_⟩
    calc ((r * x1 : RingOfIntegers E) : E) = (r : E) * (x1 : E) := rfl
      _ = (r : E) * (((y : RingOfIntegers E) : E) * u a) := by rw [h1]
      _ = ((y : RingOfIntegers E) : E) * (r • u) a := by
        rw [Pi.smul_apply, Algebra.smul_def]
        show _ = _ * ((r : E) * u a)
        ring

theorem main (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ,
      (∀ (w : InfinitePlace E) (a : Fin j), w (y a) < δ) → y = 0 := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_denominator E j Λ hΛ
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hnn : ∀ (w : InfinitePlace E) (z : E), 0 ≤ w z := fun w z => w.1.nonneg z
  set M : ℝ := ∑ w : InfinitePlace E, w (d : E) with hM
  have hwM : ∀ w : InfinitePlace E, w (d : E) ≤ M := fun w =>
    Finset.single_le_sum (f := fun w : InfinitePlace E => w (d : E)) (fun w _ => hnn w _) (Finset.mem_univ w)
  have hMpos : 0 < M := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    exact lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hdE) (hwM w0)
  refine ⟨1 / M, by positivity, fun y hy hsmall => ?_⟩
  funext a
  obtain ⟨x, hx⟩ := hd y hy a
  have hx0 : x = 0 := eq_zero_of_small E x fun w => by
    rw [hx, map_mul]
    calc w (d : E) * w (y a) ≤ M * w (y a) := mul_le_mul_of_nonneg_right (hwM w) (hnn w _)
      _ < M * (1 / M) := mul_lt_mul_of_pos_left (hsmall w a) hMpos
      _ = 1 := by field_simp
  have hza : (d : E) * y a = 0 := by rw [← hx, hx0]; rfl
  simpa [hdE] using hza

end GlobalTheory.SmallIntegerVanishing
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.StrictDom

open Topology Filter

theorem exists_small_eq_zero (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ, (∀ (w : InfinitePlace E) a, w (y a) < δ) → y = 0 := by
  first
  | exact @_root_.GlobalTheory.SmallIntegerVanishing.main
  | exact _root_.GlobalTheory.SmallIntegerVanishing.main
  | (apply _root_.GlobalTheory.SmallIntegerVanishing.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallIntegerVanishing.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallIntegerVanishing.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallIntegerVanishing.main ..)

theorem eventually_eq_one (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsFullLattice E Λ)
    (x : InfinitePlace E → Fin j → Fin j → ℂ) (hx : ∀ w, (Matrix.of (x w)).det ≠ 0) :
    ∀ᶠ h in 𝓝 x, ∀ γ : Matrix (Fin j) (Fin j) E, (∀ y ∈ Λ, γ *ᵥ y ∈ Λ) →
      (∀ w : InfinitePlace E, Matrix.of (h w) = γ.map w.embedding * Matrix.of (x w)) → γ = 1 := by
  classical
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_eq_zero E j Λ hΛ.fg
  obtain ⟨s, hs⟩ := hΛ.fg
  have hev : ∀ᶠ h in 𝓝 x, ∀ y ∈ s, ∀ (w : InfinitePlace E) (a : Fin j),
      ‖((Matrix.of (h w) * (Matrix.of (x w))⁻¹) *ᵥ (fun b => w.embedding (y b))) a
        - w.embedding (y a)‖ < δ := by
    refine (Filter.eventually_all_finset s).2 fun y _ => Filter.eventually_all.2 fun w =>
      Filter.eventually_all.2 fun a => ?_
    have hc : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ =>
        ‖((Matrix.of (h w) * (Matrix.of (x w))⁻¹) *ᵥ (fun b => w.embedding (y b))) a
          - w.embedding (y a)‖ := by
      have h1 : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (h w) :=
        continuous_apply w
      exact (((continuous_apply a).comp
        ((h1.matrix_mul continuous_const).matrix_mulVec continuous_const)).sub continuous_const).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hx w)), Matrix.one_mulVec]
    simpa using hδ
  filter_upwards [hev] with h hh γ hγ hw
  have hfix : ∀ y ∈ s, γ *ᵥ y = y := fun y hy => by
    have hyΛ : y ∈ Λ := hs ▸ Submodule.subset_span hy
    refine sub_eq_zero.1 (hsmall _ (Λ.sub_mem (hγ y hyΛ) hyΛ) fun w a => ?_)
    have := hh y hy w a
    rw [hw w, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hx w)),
      Matrix.mul_one] at this
    rw [← InfinitePlace.norm_embedding_eq, Pi.sub_apply, map_sub, RingHom.map_mulVec]
    exact this
  have hspan : Submodule.span E (s : Set (Fin j → E)) = ⊤ := by
    have := Submodule.IsFullLattice.span_eq_top (self := hΛ)
    rwa [← hs, Submodule.span_span_of_tower] at this
  have hall : ∀ y, γ *ᵥ y = y := fun y => by
    have hy : y ∈ Submodule.span E (s : Set (Fin j → E)) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hfix y hy
    | zero => simp
    | add y y' _ _ h h' => rw [Matrix.mulVec_add, h, h']
    | smul c y _ h => rw [Matrix.mulVec_smul, h]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

theorem exists_strictDomain : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ e : GL (Fin j) E → MatInf E j, (∀ γ w a b, e γ w a b = w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)) → ∀ S : Subgroup (GL (Fin j) E), (∀ γ ∈ S, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ ∀ g, 0 < detNorm E j g → ∃! γ : GL (Fin j) E, γ ∈ S ∧ e γ * g ∈ D := by
  intro E _ _ j Λ hΛ e he S hS
  have hof : ∀ γ w, Matrix.of (e γ w) = (γ : Matrix (Fin j) (Fin j) E).map w.embedding :=
    fun γ w => by ext a b; exact he γ w a b
  have hpos : ∀ γ (g : MatInf E j), 0 < detNorm E j g → 0 < detNorm E j (e γ * g) := fun γ g hg => by
    rw [MeanDual.detNorm_mul]
    refine mul_pos ((MeanDual.detNorm_pos_iff E j _).2 fun w => ?_) hg
    rw [hof, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  have hone : ∀ g : MatInf E j, e 1 * g = g := fun g => MeanDual.matInf_ext E j fun w => by
    rw [MeanDual.of_mul, hof]; simp
  have hmul : ∀ γ γ' (g : MatInf E j), e (γ * γ') * g = e γ * (e γ' * g) := fun γ γ' g =>
    MeanDual.matInf_ext E j fun w => by
      simp only [MeanDual.of_mul, hof, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  have hcont : ∀ γ, Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ =>
      (show InfinitePlace E → Fin j → Fin j → ℂ from (e γ * (show MatInf E j from g) : MatInf E j)) := fun γ =>
    continuous_pi fun w => (continuous_const.matrix_mul
      (show Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (h w) from
        continuous_apply w) : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ =>
          Matrix.of (e γ w) * Matrix.of (h w))
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  haveI : Countable (GL (Fin j) E) := Units.val_injective.countable
  let U : Set (InfinitePlace E → Fin j → Fin j → ℂ) := {g | 0 < detNorm E j g}
  have hU : MeasurableSet U := MeanDual.measurableSet_detNorm_pos E j
  letI : MulAction S U :=
    { smul := fun γ g => ⟨(e γ * (show MatInf E j from g.1) : MatInf E j), hpos γ g.1 g.2⟩
      one_smul := fun g => Subtype.ext (hone g.1)
      mul_smul := fun γ γ' g => Subtype.ext (hmul γ γ' g.1) }
  have hsm : ∀ (γ : S) (g : U), (γ • g).1 = (e γ * (show MatInf E j from g.1) : MatInf E j) :=
    fun _ _ => rfl
  have hc : ∀ γ : S, Continuous fun g : U => γ • g := fun γ =>
    ((hcont γ).comp continuous_subtype_val).subtype_mk _
  haveI : MeasurableConstSMul S U := ⟨fun γ => (hc γ).measurable⟩
  have hdisc : ∀ x : U, ∃ V ∈ 𝓝 x, ∀ γ : S, γ • x ∈ V → γ = 1 := fun x => by
    have h := eventually_eq_one E j Λ hΛ x.1 ((MeanDual.detNorm_pos_iff E j _).1 x.2)
    refine ⟨_, continuous_subtype_val.continuousAt.eventually h, fun γ hγ => ?_⟩
    refine Subtype.ext (Units.ext (hγ _ (fun y hy => (hS γ γ.2 y).2 hy) fun w => ?_))
    rw [← hof]; rfl
  have hfree : ∀ (γ : S) (x : U), γ • x = x → γ = 1 := fun γ x h => by
    obtain ⟨V, hV, hV'⟩ := hdisc x
    exact hV' γ (h.symm ▸ mem_of_mem_nhds hV)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := S) (X := U)
    (fun γ => (isClosed_eq (hc γ) continuous_id).measurableSet)
    (fun x => by
      obtain ⟨V, hV, hV'⟩ := hdisc x
      exact ⟨V, hV, fun γ hγ => by rw [hV' γ hγ, one_smul]⟩)
  refine ⟨Subtype.val '' D, hU.subtype_image hD, ?_, fun g hg => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · obtain ⟨γ, hγ⟩ := hcov ⟨g, hg⟩
    refine ⟨γ, ⟨γ.2, _, hγ, rfl⟩, ?_⟩
    rintro k ⟨hk, x, hx, hxe⟩
    have hx' : x = (⟨k, hk⟩ : S) • (⟨g, hg⟩ : U) := Subtype.ext hxe
    have := hu _ hγ (⟨k, hk⟩ * γ⁻¹) (by rw [mul_smul, inv_smul_smul, ← hx']; exact hx)
    exact congrArg Subtype.val (mul_inv_eq_one.1 (hfree _ _ this))

end GlobalTheory.StrictDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbits
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.PairOrbit

theorem tsum_lintegral_le {X G I J : Type} [MeasurableSpace X] [Countable G] [Countable I] [Countable J]
    (μ : Measure X) (t : G → X → X) (D : I → Set X) (D' : J → Set X) (f : I → X → ENNReal) (f' : J → X → ENNReal)
    (R : I → J → G → Prop) (ht : ∀ γ, MeasurePreserving (t γ) μ μ) (he : ∀ γ, MeasurableEmbedding (t γ))
    (hD : ∀ i, MeasurableSet (D i)) (hD' : ∀ j, MeasurableSet (D' j))
    (hf : ∀ i j γ, R i j γ → ∀ x ∈ D i, f i x = f' j (t γ x))
    (hc : ∀ i, ∀ x ∈ D i, ∃ j γ, R i j γ ∧ t γ x ∈ D' j)
    (hu : ∀ j i i' γ γ' x x', R i j γ → R i' j γ' → x ∈ D i → x' ∈ D i' → t γ x = t γ' x' → i = i' ∧ γ = γ') :
    ∑' i, ∫⁻ x in D i, f i x ∂μ ≤ ∑' j, ∫⁻ x in D' j, f' j x ∂μ := by
  let A : I → J → G → Set X := fun i j γ => {x | R i j γ ∧ x ∈ D i ∧ t γ x ∈ D' j}
  have hA : ∀ i j γ, MeasurableSet (A i j γ) := fun i j γ =>
    (MeasurableSet.const _).inter ((hD i).inter ((he γ).measurable (hD' j)))
  have h1 : ∀ i, ∫⁻ x in D i, f i x ∂μ ≤ ∑' j, ∑' γ, ∫⁻ x in t γ '' A i j γ, f' j x ∂μ := by
    intro i
    have hsub : D i ⊆ ⋃ j, ⋃ γ, A i j γ := fun x hx => by
      obtain ⟨j, γ, h, h'⟩ := hc i x hx
      exact Set.mem_iUnion₂.2 ⟨j, γ, h, hx, h'⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans
      (ENNReal.tsum_le_tsum fun j => (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum fun γ => ?_)))
    rw [← (ht γ).setLIntegral_comp_emb (he γ)]
    exact (setLIntegral_congr_fun (hA i j γ) fun x hx => hf i j γ hx.1 x hx.2.1).le
  refine (ENNReal.tsum_le_tsum h1).trans ?_
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [← ENNReal.tsum_prod (f := fun i γ => ∫⁻ x in t γ '' A i j γ, f' j x ∂μ),
    ← lintegral_iUnion (s := fun p : I × G => t p.2 '' A p.1 j p.2)
      (fun p => (he p.2).measurableSet_image.2 (hA _ _ _))]
  · refine lintegral_mono_set (Set.iUnion_subset fun p => ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2.2
  · intro p q hpq
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', h⟩
    obtain ⟨h1, h2⟩ := hu j p.1 q.1 p.2 q.2 x x' hx.1 hx'.1 hx.2.1 hx'.2.1 h.symm
    exact hpq (Prod.ext h1 h2)

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

def emb (γ : GL (Fin j) E) : MatInf E j := fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

def vecAt (y : Fin j → E) (g : MatInf E j) : VecInf E j :=
  fun w => (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a)

def Carries (γ : GL (Fin j) E) (L L' : Submodule (𝓞 E) (Fin j → E)) : Prop :=
  ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ L' ↔ y ∈ L

omit [NumberField E] in
theorem carries_one (L : Submodule (𝓞 E) (Fin j → E)) : Carries 1 L L := fun y => by simp

omit [NumberField E] in
theorem Carries.mul {γ δ : GL (Fin j) E} {L L' L'' : Submodule (𝓞 E) (Fin j → E)} (h' : Carries δ L' L'')
    (h : Carries γ L L') : Carries (δ * γ) L L'' := fun y => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h', h]

omit [NumberField E] in
theorem mul_mulVec (γ δ : GL (Fin j) E) (y : Fin j → E) :
    ((γ * δ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y =
      (γ : Matrix (Fin j) (Fin j) E) *ᵥ ((δ : Matrix (Fin j) (Fin j) E) *ᵥ y) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

omit [NumberField E] in
theorem inv_mulVec (γ : GL (Fin j) E) (y : Fin j → E) :
    ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ ((γ : Matrix (Fin j) (Fin j) E) *ᵥ y) = y := by
  rw [← mul_mulVec, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

omit [NumberField E] in
theorem mulVec_inv (γ : GL (Fin j) E) (y : Fin j → E) :
    (γ : Matrix (Fin j) (Fin j) E) *ᵥ (((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) = y := by
  rw [← mul_mulVec, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

omit [NumberField E] in
theorem Carries.inv {γ : GL (Fin j) E} {L L' : Submodule (𝓞 E) (Fin j → E)} (h : Carries γ L L') :
    Carries γ⁻¹ L' L := fun y => by
  rw [← h, mulVec_inv]

omit [NumberField E] in
theorem of_emb_mul (γ : GL (Fin j) E) (g : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((emb γ * g) w) = (γ : Matrix (Fin j) (Fin j) E).map w.embedding * Matrix.of (g w) := rfl

omit [NumberField E] in
theorem emb_mul_mul (γ δ : GL (Fin j) E) (g : MatInf E j) : emb (γ * δ) * g = emb γ * (emb δ * g) := by
  funext w
  apply Matrix.of.injective
  rw [of_emb_mul, of_emb_mul, of_emb_mul, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] in
theorem emb_one_mul (g : MatInf E j) : emb (1 : GL (Fin j) E) * g = g := by
  funext w
  apply Matrix.of.injective
  rw [of_emb_mul, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

omit [NumberField E] in
theorem det_map_ne_zero (γ : GL (Fin j) E) (w : InfinitePlace E) :
    ((γ : Matrix (Fin j) (Fin j) E).map w.embedding).det ≠ 0 := by
  have := (IsUnit.mk0 _ (Matrix.GeneralLinearGroup.det_ne_zero γ)).map w.embedding
  rw [RingHom.map_det] at this
  exact this.ne_zero

theorem detNorm_pos_iff (g : MatInf E j) : 0 < detNorm E j g ↔ ∀ w, (Matrix.of (g w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem detNorm_emb_pos (γ : GL (Fin j) E) : 0 < detNorm E j (emb γ) :=
  (detNorm_pos_iff _).2 fun w => det_map_ne_zero γ w

theorem detNorm_emb_mul_pos (γ : GL (Fin j) E) {g : MatInf E j} (hg : 0 < detNorm E j g) :
    0 < detNorm E j (emb γ * g) := by
  rw [detNorm_pos_iff] at hg ⊢
  intro w
  rw [of_emb_mul, Matrix.det_mul]
  exact mul_ne_zero (det_map_ne_zero γ w) (hg w)

theorem vecAt_emb (γ : GL (Fin j) E) (y : Fin j → E) (g : MatInf E j) :
    vecAt ((γ : Matrix (Fin j) (Fin j) E) *ᵥ y) (emb γ * g) = vecAt y g := by
  funext w
  have h2 : (fun a => w.embedding (((γ : Matrix (Fin j) (Fin j) E) *ᵥ y) a)) =
      (γ : Matrix (Fin j) (Fin j) E).map w.embedding *ᵥ fun a => w.embedding (y a) := by
    funext a; simp [Matrix.mulVec, dotProduct]
  unfold vecAt
  rw [of_emb_mul, h2, Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ (det_map_ne_zero γ w)), Matrix.mul_one]

theorem latAt_emb {γ : GL (Fin j) E} {L L' : Submodule (𝓞 E) (Fin j → E)} (h : Carries γ L L') (g : MatInf E j) :
    latAt E j L' (emb γ * g) = latAt E j L g := by
  unfold latAt
  congr 1
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, (h.inv y).2 hy, ?_⟩
    have := vecAt_emb γ (((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) g
    rw [mulVec_inv] at this
    exact this.symm
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (h y).2 hy, vecAt_emb γ y g⟩

def vecHom (g : MatInf E j) : (Fin j → E) →+ VecInf E j where
  toFun y := vecAt y g
  map_zero' := by
    funext w
    simp only [vecAt, Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero _
  map_add' y z := by
    funext w
    simp only [vecAt, Pi.add_apply, map_add (f := _)]
    exact Matrix.mulVec_add _ _ _

theorem mem_latAt (L : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) (x : VecInf E j) :
    x ∈ latAt E j L g ↔ ∃ y ∈ L, vecAt y g = x := by
  refine ⟨fun hx => ?_, fun ⟨y, hy, h⟩ => Submodule.subset_span ⟨y, hy, h⟩⟩
  induction hx using Submodule.span_induction with
  | mem y h => exact h
  | zero => exact ⟨0, zero_mem _, (vecHom g).map_zero⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    exact ⟨p + q, add_mem hp hq, (vecHom g).map_add p q⟩
  | smul n a _ ha =>
    obtain ⟨p, hp, rfl⟩ := ha
    exact ⟨n • p, zsmul_mem hp n, (vecHom g).map_zsmul n p⟩

theorem vecHom_injective {g : MatInf E j} (hg : 0 < detNorm E j g) : Function.Injective (vecHom g) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h1 : (Matrix.of (g w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = 0 := congrFun hy w
  have h2 := congrArg (fun v => Matrix.of (g w) *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
  rw [Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ ((detNorm_pos_iff g).1 hg w)), Matrix.one_mulVec] at h2
  funext a
  exact (map_eq_zero w.embedding).1 (congrFun h2 a)

theorem tsum_latAt (L : Submodule (𝓞 E) (Fin j → E)) {g : MatInf E j} (hg : 0 < detNorm E j g)
    (Φ : VecInf E j → ENNReal) :
    ∑' x : {x : VecInf E j // x ∈ latAt E j L g ∧ x ≠ 0}, Φ x.1 =
      ∑' y : {y : Fin j → E // y ∈ L ∧ y ≠ 0}, Φ (vecAt y.1 g) := by
  let φ : {y : Fin j → E // y ∈ L ∧ y ≠ 0} → {x : VecInf E j // x ∈ latAt E j L g ∧ x ≠ 0} := fun y =>
    ⟨vecAt y.1 g, (mem_latAt L g _).2 ⟨y.1, y.2.1, rfl⟩,
      fun h => y.2.2 (vecHom_injective hg (h.trans (vecHom g).map_zero.symm))⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (vecHom_injective hg (congrArg Subtype.val h)), fun x => ?_⟩
    obtain ⟨y, hy, h⟩ := (mem_latAt L g _).1 x.2.1
    refine ⟨⟨y, hy, ?_⟩, Subtype.ext h⟩
    rintro rfl
    exact x.2.2 (h.symm.trans (vecHom g).map_zero)
  exact ((Equiv.ofBijective φ hφ).tsum_eq fun x => Φ x.1).symm

theorem measurable_vecAt (y : Fin j → E) : Measurable fun g : MatInf E j => vecAt y g := by
  change Measurable fun g : InfinitePlace E → Fin j → Fin j → ℂ => vecAt y g
  refine Measurable.of_eval fun w => Measurable.of_eval fun a => ?_
  have hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (g w) : Matrix (Fin j) (Fin j) ℂ) :=
    continuous_apply w
  simp only [vecAt, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  refine hc.matrix_det.measurable.inv.mul (Continuous.measurable ?_)
  exact (continuous_apply a).comp (hc.matrix_adjugate.matrix_mulVec continuous_const)

local instance countable_GL : Countable (GL (Fin j) E) := by
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  exact Units.val_injective.countable

theorem covol_eq_lintegral (S : Subgroup (GL (Fin j) E)) (Γ : Set (MatInf E j))
    (hΓ : ∀ x, x ∈ Γ ↔ ∃ γ ∈ S, emb γ = x) (D : Set (MatInf E j)) (hD : MeasurableSet D)
    (hDU : D ⊆ {g | 0 < detNorm E j g})
    (hs : ∀ g, 0 < detNorm E j g → ∃! γ : GL (Fin j) E, γ ∈ S ∧ emb γ * g ∈ D)
    (F : MatInf E j → ENNReal) (hF : ∀ γ ∈ S, ∀ g, F (emb γ * g) = F g) :
    covol Γ ((haarGL E j).withDensity F) {g | 0 < detNorm E j g} = ∫⁻ g in D, F g ∂(haarGL E j) := by
  unfold covol
  apply le_antisymm
  · refine iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le ?_ (withDensity_apply _ hD).le))
    intro g hg
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := hs g hg
    exact ⟨emb γ, (hΓ _).2 ⟨γ, h1, rfl⟩, h2⟩
  · refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
    rw [withDensity_apply _ hD']
    have := tsum_lintegral_le (I := Unit) (J := Unit) (haarGL E j) (fun (γ : GL (Fin j) E) g => emb γ * g)
      (fun _ => D) (fun _ => D') (fun _ => F) (fun _ => F) (fun _ _ γ => γ ∈ S)
      (fun γ => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j _ (detNorm_emb_pos γ)).2) (fun γ => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j _ (detNorm_emb_pos γ)).1)
      (fun _ => hD) (fun _ => hD') (fun _ _ γ hγ g _ => (hF γ hγ g).symm) ?_ ?_
    · simpa using this
    · intro _ g hg
      obtain ⟨x, hx, h⟩ := hc g (hDU hg)
      obtain ⟨γ, hγ, rfl⟩ := (hΓ x).1 hx
      exact ⟨(), γ, hγ, h⟩
    · intro _ _ _ γ γ' g g' hγ hγ' hg hg' h
      refine ⟨rfl, inv_injective ((hs _ (detNorm_emb_mul_pos γ (hDU hg))).unique ⟨S.inv_mem hγ, ?_⟩
        ⟨S.inv_mem hγ', ?_⟩)⟩
      · rwa [← emb_mul_mul, inv_mul_cancel, emb_one_mul]
      · rwa [h, ← emb_mul_mul, inv_mul_cancel, emb_one_mul]

theorem pair_le {I J : Type} [Countable I] [Countable J]
    (Λ : I → Submodule (𝓞 E) (Fin j → E)) (x : I → Fin j → E) (D : I → Set (MatInf E j))
    (Λ' : J → Submodule (𝓞 E) (Fin j → E)) (x' : J → Fin j → E) (D' : J → Set (MatInf E j))
    (hD : ∀ i, MeasurableSet (D i)) (hD' : ∀ i, MeasurableSet (D' i))
    (hu : ∀ i i' γ, ∀ g ∈ D i, Carries γ (Λ i) (Λ i') → (γ : Matrix (Fin j) (Fin j) E) *ᵥ x i = x i' →
      emb γ * g ∈ D i' → i = i' ∧ γ = 1)
    (hc : ∀ i, ∀ g ∈ D i, ∃ i' γ, (Carries γ (Λ i) (Λ' i') ∧ (γ : Matrix (Fin j) (Fin j) E) *ᵥ x i = x' i') ∧
      emb γ * g ∈ D' i')
    (F : Submodule ℤ (VecInf E j) → VecInf E j → ENNReal) :
    ∑' i, ∫⁻ g in D i, F (latAt E j (Λ i) g) (vecAt (x i) g) ∂(haarGL E j) ≤
      ∑' i, ∫⁻ g in D' i, F (latAt E j (Λ' i) g) (vecAt (x' i) g) ∂(haarGL E j) := by
  refine tsum_lintegral_le (haarGL E j) (fun (γ : GL (Fin j) E) g => emb γ * g) D D' _ _
    (fun i i' γ => Carries γ (Λ i) (Λ' i') ∧ (γ : Matrix (Fin j) (Fin j) E) *ᵥ x i = x' i')
    (fun γ => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j _ (detNorm_emb_pos γ)).2) (fun γ => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j _ (detNorm_emb_pos γ)).1)
    hD hD' ?_ hc ?_
  · rintro i i' γ ⟨h1, h2⟩ g -
    rw [latAt_emb h1, ← h2, vecAt_emb]
  · rintro l i i' γ γ' g g' ⟨h1, h2⟩ ⟨h1', h2'⟩ hg hg' h
    obtain ⟨e1, e2⟩ := hu i i' (γ'⁻¹ * γ) g hg (h1'.inv.mul h1) (by rw [mul_mulVec, h2, ← h2', inv_mulVec])
      (by rwa [emb_mul_mul, h, ← emb_mul_mul, inv_mul_cancel, emb_one_mul])
    exact ⟨e1, (inv_mul_eq_one.1 e2).symm⟩


variable (E j) in
abbrev Cls : Type :=
  Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1)

omit [NumberField E] in
theorem cls_exists (L : Submodule (𝓞 E) (Fin j → E)) (hL : Submodule.IsFullLattice E L) :
    ∃ (c : Cls E j) (γ : GL (Fin j) E), Carries γ L (Quot.out c).1 := by
  have he : Equivalence (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1) :=
    ⟨fun Λ => ⟨1, carries_one _⟩, fun ⟨γ, h⟩ => ⟨γ⁻¹, Carries.inv h⟩,
      fun ⟨γ, h⟩ ⟨δ, h'⟩ => ⟨δ * γ, Carries.mul h' h⟩⟩
  let c : Cls E j := Quot.mk _ ⟨L, hL⟩
  have h : (Quot.mk _ ⟨L, hL⟩ : Cls E j) = Quot.mk _ (Quot.out c) := (Quot.out_eq c).symm
  exact ⟨c, he.eqvGen_iff.1 (Quot.eqvGen_exact h)⟩

omit [NumberField E] in
theorem cls_eq {c c' : Cls E j} {γ : GL (Fin j) E} (h : Carries γ (Quot.out c).1 (Quot.out c').1) : c = c' := by
  rw [← Quot.out_eq c, ← Quot.out_eq c']
  exact Quot.sound ⟨γ, h⟩

local instance countable_field : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv

local instance countable_cls : Countable (Cls E j) := by
  have : Countable {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} := by
    have h : ∀ Λ : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ}, ∃ s : Finset (Fin j → E),
        Submodule.span (𝓞 E) (s : Set (Fin j → E)) = Λ.1 := fun Λ => Λ.2.toIsLattice.fg
    choose s hs using h
    exact Function.Injective.countable (f := s) fun a b hab => Subtype.ext (by rw [← hs a, ← hs b, hab])
  infer_instance

local instance countable_ideal : Countable (Ideal (𝓞 E)) := by
  have : Countable (𝓞 E) := RingOfIntegers.coe_injective.countable
  have h : ∀ 𝔞 : Ideal (𝓞 E), ∃ s : Finset (𝓞 E), Ideal.span (s : Set (𝓞 E)) = 𝔞 := fun 𝔞 =>
    IsNoetherian.noetherian 𝔞
  choose s hs using h
  exact Function.Injective.countable (f := s) fun a b hab => by rw [← hs a, ← hs b, hab]

def autSub (L : Submodule (𝓞 E) (Fin j → E)) : Subgroup (GL (Fin j) E) where
  carrier := {γ | Carries γ L L}
  mul_mem' ha hb := Carries.mul ha hb
  one_mem' := carries_one L
  inv_mem' ha := Carries.inv ha

def stabSub (L : Submodule (𝓞 E) (Fin j → E)) (x : Fin j → E) : Subgroup (GL (Fin j) E) where
  carrier := {γ | Carries γ L L ∧ (γ : Matrix (Fin j) (Fin j) E) *ᵥ x = x}
  mul_mem' ha hb := ⟨Carries.mul ha.1 hb.1, by rw [mul_mulVec, hb.2, ha.2]⟩
  one_mem' := ⟨carries_one L, by simp⟩
  inv_mem' {a} ha := ⟨Carries.inv ha.1, by
    have := inv_mulVec a x
    rwa [ha.2] at this⟩

omit [NumberField E] in
theorem mem_autGL (L : Submodule (𝓞 E) (Fin j → E)) (x : MatInf E j) :
    x ∈ autGL E j L ↔ ∃ γ ∈ autSub L, emb γ = x :=
  ⟨fun ⟨γ, h, h'⟩ => ⟨γ, h, funext fun w => funext fun a => funext fun b => (h' w a b).symm⟩,
    fun ⟨γ, h, h'⟩ => ⟨γ, h, fun w a b => by rw [← h']; rfl⟩⟩

theorem mem_stab {k : ℕ} (L : Submodule (𝓞 E) (Fin (k + 1) → E)) (x : MatInf E (k + 1)) :
    x ∈ {x | x ∈ autGL E (k + 1) L ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ↔
      ∃ γ ∈ stabSub L (Pi.single 0 1), emb γ = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  constructor
  · rintro ⟨h, h'⟩
    obtain ⟨γ, hγ, rfl⟩ := (mem_autGL L x).1 h
    refine ⟨γ, ⟨hγ, ?_⟩, rfl⟩
    funext a
    apply w.embedding.injective
    have := h' w a
    simp only [emb] at this
    simp [this, Pi.single_apply, apply_ite w.embedding]
  · rintro ⟨γ, ⟨h, h'⟩, rfl⟩
    refine ⟨(mem_autGL L _).2 ⟨γ, h, rfl⟩, fun w a => ?_⟩
    have := congrFun h' a
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    simp [emb, this, apply_ite w.embedding]

omit [NumberField E] in
theorem vecAt_single {k : ℕ} (g : MatInf E (k + 1)) :
    (fun u a => (Matrix.of (g u))⁻¹ a 0) = vecAt (Pi.single 0 1 : Fin (k + 1) → E) g := by
  funext u a
  simp [vecAt, Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite u.embedding]

omit [NumberField E] in
theorem exists_block {k : ℕ} (δ : GL (Fin k) E) : ∃ γ : GL (Fin (k + 1)) E,
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ = δ ∧
    ∀ b : Fin k, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ = 0 := by
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) E :=
    Matrix.of (Fin.cons (Fin.cons 1 0) fun a => Fin.cons 0 ((δ : Matrix (Fin k) (Fin k) E) a))
  have h1 : M.submatrix Fin.succ Fin.succ = δ := by ext a b; simp [M]
  have hd : M.det ≠ 0 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    rw [Fin.succAbove_zero, h1]
    simpa [M] using Matrix.GeneralLinearGroup.det_ne_zero δ
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hd, ?_, h1, fun b => by simp [M]⟩
  funext a
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [M]

omit [NumberField E] in
theorem exists_sub {k : ℕ} (γ : GL (Fin (k + 1)) E)
    (h : (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Pi.single 0 1 = Pi.single 0 1) : ∃ δ : GL (Fin k) E,
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ = δ := by
  have h0 : ∀ a, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) a 0 = if a = 0 then 1 else 0 := fun a => by
    have := congrFun h a
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using this
  have hd := Matrix.GeneralLinearGroup.det_ne_zero γ
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ] at hd
  have hd' : ((γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ).det ≠ 0 := by
    simpa [h0] using hd
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd', rfl⟩

theorem latMean_sum_eq_tsum_orbits : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → latMean E (k + 1) (fun L => w (covAt E (k + 1) L) * ∑' x : {x : VecInf E (k + 1) // x ∈ L ∧ x ≠ 0}, Φ x.1) = ∑' 𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥}, ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsFullLattice E Λ} => ∃ γ : GL (Fin k) E, ∀ y, (γ : Matrix (Fin k) (Fin k) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1), covol {x | x ∈ autGL E (k + 1) (Lf 𝔞.1 (Quot.out c).1) ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞.1 (Quot.out c).1) g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} := by
  intro E _ _ hE k Lf hLf w Φ hw hΦ
  obtain ⟨hA1, hA2, hA3⟩ := GlobalTheory.LatVecPair.classes E k Lf hLf
  choose D hD hDU hs using fun c : Cls E (k + 1) =>
    GlobalTheory.StrictDom.exists_strictDomain E (k + 1) (Quot.out c).1 (Quot.out c).2 emb (fun _ _ _ _ => rfl) (autSub (Quot.out c).1)
      fun _ h => h
  choose D' hD' hDU' hs' using fun p : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥} × Cls E k =>
    GlobalTheory.StrictDom.exists_strictDomain E (k + 1) (Lf p.1.1 (Quot.out p.2).1) (hA1 _ _ p.1.2 (Quot.out p.2).2).1 emb (fun _ _ _ _ => rfl)
      (stabSub (Lf p.1.1 (Quot.out p.2).1) (Pi.single 0 1)) fun _ h => h.1
  let F : Submodule ℤ (VecInf E (k + 1)) → VecInf E (k + 1) → ENNReal := fun L x => w (covAt E (k + 1) L) * Φ x
  have hL : latMean E (k + 1) (fun L => w (covAt E (k + 1) L) *
      ∑' x : {x : VecInf E (k + 1) // x ∈ L ∧ x ≠ 0}, Φ x.1) =
      ∑' i : (Σ c : Cls E (k + 1), {y : Fin (k + 1) → E // y ∈ (Quot.out c).1 ∧ y ≠ 0}),
        ∫⁻ g in D i.1, F (latAt E (k + 1) (Quot.out i.1).1 g) (vecAt i.2.1 g) ∂(haarGL E (k + 1)) := by
    rw [latMean, ENNReal.tsum_sigma']
    refine tsum_congr fun c => ?_
    rw [covol_eq_lintegral (autSub (Quot.out c).1) _ (mem_autGL _) (D c) (hD c) (hDU c) (hs c) _
      (fun γ hγ g => by rw [latAt_emb (show Carries γ _ _ from hγ) g])]
    dsimp only
    rw [← lintegral_tsum]
    · refine setLIntegral_congr_fun (hD c) fun g hg => ?_
      simp only [F]
      rw [tsum_latAt _ (hDU c hg), ENNReal.tsum_mul_left]
    · intro y
      refine AEMeasurable.mul ?_ (hΦ.comp (measurable_vecAt _)).aemeasurable
      have hweight := (GlobalTheory.T.measurable_translatedLattice_functions E hE (k + 1)
        w Φ hw hΦ (Quot.out c).1 (Quot.out c).2).1
      refine hweight.aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem (hD c)] with g hg
      exact Set.indicator_of_mem (hDU c hg) _
  rw [hL, ← ENNReal.tsum_prod]
  have hR : ∀ p : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥} × Cls E k,
      covol {x | x ∈ autGL E (k + 1) (Lf p.1.1 (Quot.out p.2).1) ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0}
        ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf p.1.1 (Quot.out p.2).1) g)) *
          Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} =
      ∫⁻ g in D' p, F (latAt E (k + 1) (Lf p.1.1 (Quot.out p.2).1) g) (vecAt (Pi.single 0 1) g)
        ∂(haarGL E (k + 1)) := by
    intro p
    simp only [vecAt_single]
    refine covol_eq_lintegral _ _ (mem_stab _) (D' p) (hD' p) (hDU' p) (hs' p) _ fun γ hγ g => ?_
    have := vecAt_emb γ (Pi.single 0 1) g
    rw [hγ.2] at this
    rw [latAt_emb hγ.1, this]
  rw [tsum_congr hR]
  apply le_antisymm
  · refine pair_le (I := Σ c : Cls E (k + 1), {y : Fin (k + 1) → E // y ∈ (Quot.out c).1 ∧ y ≠ 0})
      _ _ _ _ _ _ (fun i => hD i.1) hD' ?_ ?_ F
    · rintro ⟨c, y⟩ ⟨c', y'⟩ γ g hg h1 h2 h3
      obtain rfl : c = c' := cls_eq h1
      obtain rfl : γ = 1 := (hs c g (hDU c hg)).unique ⟨h1, h3⟩ ⟨one_mem _, by rwa [emb_one_mul]⟩
      obtain rfl : y = y' := Subtype.ext (by simpa using h2)
      exact ⟨rfl, rfl⟩
    · rintro ⟨c, y⟩ g hg
      obtain ⟨γ, 𝔞, Λ', h𝔞, hΛ', h1, h2⟩ := hA2 _ (Quot.out c).2 y.1 y.2.1 y.2.2
      obtain ⟨c', δ, hδ⟩ := cls_exists Λ' hΛ'
      obtain ⟨β, b1, b2, b3⟩ := exists_block δ
      have hβ : Carries β (Lf 𝔞 Λ') (Lf 𝔞 (Quot.out c').1) :=
        (hA3 𝔞 𝔞 Λ' _ h𝔞 h𝔞 hΛ' (Quot.out c').2 β b1).2
          ⟨rfl, by rw [b2]; exact hδ, fun y _ t _ => ⟨0, by simp [b3, dotProduct]⟩⟩
      obtain ⟨σ, ⟨s1, s2⟩, -⟩ := hs' (⟨𝔞, h𝔞⟩, c') _ (detNorm_emb_mul_pos (β * γ) (hDU c hg))
      refine ⟨(⟨𝔞, h𝔞⟩, c'), σ * (β * γ), ⟨Carries.mul s1.1 (hβ.mul h2), ?_⟩, by rwa [emb_mul_mul]⟩
      rw [mul_mulVec, mul_mulVec, h1, b1, s1.2]
  · refine pair_le (J := Σ c : Cls E (k + 1), {y : Fin (k + 1) → E // y ∈ (Quot.out c).1 ∧ y ≠ 0})
      _ _ _ _ _ _ hD' (fun i => hD i.1) ?_ ?_ F
    · rintro ⟨𝔞, c⟩ ⟨𝔟, c'⟩ γ g hg h1 h2 h3
      obtain ⟨e1, e2, -⟩ := (hA3 𝔞.1 𝔟.1 _ _ 𝔞.2 𝔟.2 (Quot.out c).2 (Quot.out c').2 γ h2).1 h1
      obtain ⟨δ, hδ⟩ := exists_sub γ h2
      rw [hδ] at e2
      obtain rfl : c = c' := cls_eq e2
      obtain rfl : 𝔞 = 𝔟 := Subtype.ext e1
      exact ⟨rfl, (hs' (𝔞, c) g (hDU' _ hg)).unique ⟨⟨h1, h2⟩, h3⟩ ⟨one_mem _, by rwa [emb_one_mul]⟩⟩
    · rintro ⟨𝔞, c⟩ g hg
      obtain ⟨h1, h2⟩ := hA1 𝔞.1 _ 𝔞.2 (Quot.out c).2
      obtain ⟨c', δ, hδ⟩ := cls_exists _ h1
      obtain ⟨σ, ⟨s1, s2⟩, -⟩ := hs c' _ (detNorm_emb_mul_pos δ (hDU' _ hg))
      have hc : Carries (σ * δ) _ _ := Carries.mul s1 hδ
      refine ⟨⟨c', ⟨_, (hc _).2 h2, fun h0 => ?_⟩⟩, σ * δ, ⟨hc, rfl⟩, by rwa [emb_mul_mul]⟩
      have := inv_mulVec (σ * δ) (Pi.single 0 1)
      rw [h0, Matrix.mulVec_zero] at this
      simpa using congrFun this 0

end GlobalTheory.PairOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbitsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → latMean E (k + 1) (fun L => w (covAt E (k + 1) L) * ∑' x : {x : VecInf E (k + 1) // x ∈ L ∧ x ≠ 0}, Φ x.1) = ∑' 𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥}, ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsFullLattice E Λ} => ∃ γ : GL (Fin k) E, ∀ y, (γ : Matrix (Fin k) (Fin k) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1), covol {x | x ∈ autGL E (k + 1) (Lf 𝔞.1 (Quot.out c).1) ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞.1 (Quot.out c).1) g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} := by
  exact @GlobalTheory.PairOrbit.latMean_sum_eq_tsum_orbits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanSumNonzeroUnfold
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.SiegelUnfold


open Filter Topology in
theorem lseriesSummable_idealCount (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

theorem hasSum_zetaE (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    HasSum (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹)
      (zetaE K l) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := Complex.hasSum_re (lseriesSummable_idealCount K hs).hasSum
  unfold zetaE dedekindZeta LSeries
  simp only [Complex.ofReal_natCast] at h
  convert h using 2 with n
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]

theorem tsum_absNorm_pow_inv (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (zetaE K l) := by
  have hl0 : l ≠ 0 := by omega
  have h1 : ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ∑' 𝔞 : Ideal (𝓞 K), ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹) := by
    refine tsum_subtype_eq_of_support_subset (s := {𝔞 : Ideal (𝓞 K) | 𝔞 ≠ ⊥})
      (f := fun 𝔞 : Ideal (𝓞 K) => ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹)) ?_
    rintro 𝔞 h rfl
    exact h (by simp [hl0])
  have h := hasSum_zetaE K hl
  rw [h1, ← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable,
    ← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  have key : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ENNReal.ofReal (((Ideal.absNorm
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I) ⟨n, I⟩) : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (((n : ℝ) ^ l)⁻¹) := by
    rintro ⟨I, rfl⟩; rfl
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  haveI := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  rw [tsum_congr key, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.card_eq_fintype_card]

def sumLat (E : Type) [Field E] [NumberField E] (k : ℕ) (𝔞 : Ideal (𝓞 E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule (𝓞 E) (Fin (k + 1) → E) where
  carrier := {y | (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ'}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun t ht => ?_, Λ'.add_mem ha' hb'⟩
    rw [Pi.add_apply, mul_add]
    exact add_mem (ha t ht) (hb t ht)
  zero_mem' := ⟨fun t _ => by simp, Λ'.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨fun t ht => ?_, Λ'.smul_mem c ha'⟩
    have := ha (t * c) (𝔞.mul_mem_right c ht)
    simpa [Algebra.smul_def, mul_assoc] using this

theorem latMean_sum_ne_zero : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro E _ _ hE j hj w Φ hw hΦ
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) := by
    unfold Formalism.HermitianLatticesTheory.vInv; positivity
  rw [GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits E hE k (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ]
  simp only [fun (𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥})
      (Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsFullLattice E Λ}) =>
    GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution E hE k (by omega) (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ 𝔞.1 Λ'.1 𝔞.2 Λ'.2]
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.ofReal_mul hv,
    Nat.add_sub_cancel, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rw [tsum_absNorm_pow_inv E hj]
  rfl

end GlobalTheory.FlagBase.SiegelUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanSumNonzeroUnfoldStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeClassMean_sum_nonzero_unfold : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  exact @GlobalTheory.FlagBase.SiegelUnfold.latMean_sum_ne_zero
end

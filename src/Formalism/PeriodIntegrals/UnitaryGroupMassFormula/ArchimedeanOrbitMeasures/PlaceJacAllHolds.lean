module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PjRows
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NormSqDetOfUnitary
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceAll
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

theorem pi_smul_measure {V : Type} [Fintype V] {X : V → Type} [∀ v, MeasurableSpace (X v)]
    (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)] (c : V → ℝ≥0) :
    Measure.pi (fun v => c v • μ v) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi μ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem pi_map_smul {V : Type} [Fintype V] {X Y : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (Y v)] (μ : ∀ v, Measure (X v)) (ν : ∀ v, Measure (Y v)) [∀ v, SigmaFinite (ν v)]
    (f : ∀ v, X v → Y v) (hf : ∀ v, Measurable (f v)) (c : V → ℝ≥0)
    (hc : ∀ v, (μ v).map (f v) = c v • ν v) :
    (Measure.pi μ).map (fun x v => f v (x v)) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi ν := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v =>
    SigmaFinite.of_map (μ v) (hf v).aemeasurable (by rw [hc v]; infer_instance)
  rw [← pi_smul_measure]
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun x : ∀ v, X v => fun v => f v (x v)) :=
    Measurable.of_eval fun v => (hf v).comp (measurable_pi_apply v)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ v, X v => fun v => f v (x v)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun v => f v ⁻¹' s v) := by
    ext x
    simp
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← hc v, Measure.map_apply (hf v) (hs v)]

theorem bij_of_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] F) (c : ℝ≥0∞) (h0 : c ≠ 0) (htop : c ≠ ⊤) (h : μ.map f = c • ν) : Function.Bijective f := by
  have key : ∀ s : Set F, MeasurableSet s → μ ((f : E → F) ⁻¹' s) = c * ν s := by
    intro s hs
    have h1 := congrArg (fun ρ : Measure F => ρ s) h
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rwa [Measure.map_apply (LinearMap.continuous_of_finiteDimensional f).measurable hs] at h1
  have hsurj : Function.Surjective f := by
    by_contra hns
    have hr : LinearMap.range f ≠ ⊤ := fun hh => hns (LinearMap.range_eq_top.mp hh)
    have h0 : ν (LinearMap.range f : Set F) = 0 := Measure.addHaar_submodule ν _ hr
    have hm : MeasurableSet (LinearMap.range f : Set F) :=
      (Submodule.closed_of_finiteDimensional (LinearMap.range f)).measurableSet
    have h1 := key _ hm
    rw [h0, mul_zero] at h1
    have hpre : (f : E → F) ⁻¹' (LinearMap.range f : Set F) = Set.univ := by
      ext x
      simp
    rw [hpre] at h1
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' h1
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := by
    set K : Set F := Metric.closedBall 0 1 with hKdef
    have hKc : IsCompact K := isCompact_closedBall 0 1
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    have hK0 : ν K ≠ 0 := (Metric.measure_closedBall_pos ν (0 : F) one_pos).ne'
    have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
    open Pointwise in
    have h2m : MeasurableSet ((2 : ℝ) • K) := (hKc.smul (2 : ℝ)).isClosed.measurableSet
    open Pointwise in
    have hpre : (f : E → F) ⁻¹' ((2 : ℝ) • K) = (2 : ℝ) • ((f : E → F) ⁻¹' K) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
        · rw [map_smul, ← hxy, smul_smul]
          norm_num
          exact hy
        · rw [smul_smul]
          norm_num
      · rintro ⟨y, hy, rfl⟩
        exact ⟨f y, hy, (map_smul f (2 : ℝ) y).symm⟩
    have e1 := key _ h2m
    rw [hpre, Measure.addHaar_smul, key K hKm, Measure.addHaar_smul] at e1
    set X := c * ν K with hX
    have hX0 : X ≠ 0 := mul_ne_zero h0 hK0
    have hXt : X ≠ ⊤ := ENNReal.mul_ne_top htop hKt
    have e2 : ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ E| * X =
        ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ F| * X := by
      rw [e1, hX]
      ring
    have hu : IsUnit X := isUnit_iff_exists_inv.mpr ⟨X⁻¹, ENNReal.mul_inv_cancel hX0 hXt⟩
    have e3 := hu.mul_left_inj.mp e2
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e3
    have e4 : (2 : ℕ) ^ Module.finrank ℝ E = 2 ^ Module.finrank ℝ F := by
      have e5 : ((2 : ℕ) : ℝ) ^ Module.finrank ℝ E = ((2 : ℕ) : ℝ) ^ Module.finrank ℝ F := by
        simpa using e3
      exact_mod_cast e5
    exact Nat.pow_right_injective (le_refl 2) e4
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

theorem norm_reimE_sq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖reimE (r := a) (m := b) M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [reimE, reim, Real.norm_eq_abs, sq_abs, sq]


set_option maxHeartbeats 800000 in
theorem place_split {V : Type} [Fintype V] {a b : ℕ} {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin a) (Fin b) ℂ)) (Q : V → Matrix (Fin a) (Fin b) ℂ → Prop)
    (hQ : ∀ x v, Q v (L x v)) (hQ0 : ∀ v, Q v 0)
    (hn : ∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2)
    (hs : ∀ M : V → Matrix (Fin a) (Fin b) ℂ, (∀ v, Q v (M v)) → ∃ x, L x = M) :
    ∃ (κ : V → Type) (_ : ∀ v, Fintype (κ v)) (Lv : ∀ v, EuclideanSpace ℝ (κ v) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ)
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (κ v)),
      (∀ v y, Q v (Lv v y)) ∧ (∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2) ∧
      (∀ v M, Q v M → ∃ y, Lv v y = M) ∧ (∀ x v, Lv v (T x v) = L x v) ∧ Function.Bijective T ∧
      (∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) := by
  classical
  let R : Matrix (Fin a) (Fin b) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a × Fin b × Bool) := reimE (r := a) (m := b)
  have hRn : ∀ M : Matrix (Fin a) (Fin b) ℂ, ‖R M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := fun M => norm_reimE_sq M
  let S : V → Submodule ℝ (EuclideanSpace ℝ (Fin a × Fin b × Bool)) := fun v =>
    LinearMap.range (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
  have hmem : ∀ v (M : Matrix (Fin a) (Fin b) ℂ), R M ∈ S v ↔ Q v M := by
    intro v M
    constructor
    · intro hM
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hM
      have hx' : R (L x v) = R M := by simpa using hx
      rw [← R.injective hx']
      exact hQ x v
    · intro hq
      obtain ⟨x, hx⟩ := hs (Pi.single v M) (fun w => by
        by_cases hw : w = v
        · subst hw
          rw [Pi.single_eq_same]
          exact hq
        · rw [Pi.single_eq_of_ne hw]
          exact hQ0 w)
      refine LinearMap.mem_range.mpr ⟨x, ?_⟩
      simp [hx]
  let n : V → ℕ := fun v => Module.finrank ℝ (S v)
  let B : ∀ v, OrthonormalBasis (Fin (n v)) ℝ (S v) := fun v => stdOrthonormalBasis ℝ (S v)
  let Lv : ∀ v, EuclideanSpace ℝ (Fin (n v)) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ := fun v =>
    R.symm.toLinearMap ∘ₗ (S v).subtype ∘ₗ (B v).repr.symm.toLinearEquiv.toLinearMap
  have hLv_apply : ∀ v y, R (Lv v y) = ((B v).repr.symm y : EuclideanSpace ℝ (Fin a × Fin b × Bool)) := by
    intro v y
    simp [Lv]
  have hLv_norm : ∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2 := by
    intro v y
    rw [← hRn, hLv_apply]
    exact congrArg (fun t => t ^ 2) ((B v).repr.symm.norm_map y)
  have hLvQ : ∀ v y, Q v (Lv v y) := by
    intro v y
    refine (hmem v _).mp ?_
    rw [hLv_apply]
    exact ((B v).repr.symm y).2
  have hLvSurj : ∀ v M, Q v M → ∃ y, Lv v y = M := by
    intro v M hq
    refine ⟨(B v).repr ⟨R M, (hmem v M).mpr hq⟩, ?_⟩
    apply R.injective
    rw [hLv_apply, LinearIsometryEquiv.symm_apply_apply]
  have hLvinj : ∀ v, Function.Injective (Lv v) := by
    intro v
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hLv_norm v y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hn y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  let Tv : ∀ v, EuclideanSpace ℝ ι →ₗ[ℝ] S v := fun v =>
    LinearMap.codRestrict (S v) (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
      (fun x => LinearMap.mem_range_self _ x)
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (Fin (n v)) :=
    LinearMap.pi fun v => (B v).repr.toLinearEquiv.toLinearMap ∘ₗ Tv v
  have hTL : ∀ x v, Lv v (T x v) = L x v := by
    intro x v
    apply R.injective
    rw [hLv_apply]
    simp [T, Tv]
  have hTinj : Function.Injective T := by
    intro x x' hxx
    apply hLinj
    funext v
    rw [← hTL x v, ← hTL x' v, hxx]
  have hTsurj : Function.Surjective T := by
    intro y
    obtain ⟨x, hx⟩ := hs (fun v => Lv v (y v)) (fun v => hLvQ v (y v))
    refine ⟨x, ?_⟩
    funext v
    apply hLvinj v
    rw [hTL, hx]
  have hTnorm : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← hn x]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hLv_norm v (T x v), hTL]
  exact ⟨fun v => Fin (n v), fun v => inferInstance, Lv, T, hLvQ, hLv_norm, hLvSurj, hTL, ⟨hTinj, hTsurj⟩, hTnorm⟩

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

section Lin

variable {n m : ℕ} {α β : Type} [Fintype α] [Fintype β]

def jacM (w : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (Lv : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (Hv : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    (EuclideanSpace ℝ α × EuclideanSpace ℝ β) →ₗ[ℝ] (Fin n → Fin m → ℂ) where
  toFun z := (Lv z.1 * w + (1 / 2 : ℂ) • (B * Hv z.2) : Matrix (Fin n) (Fin m) ℂ)
  map_add' z z' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Matrix.add_mul, Matrix.mul_add, smul_add]
    abel
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply]
    rw [smul_comm]
    exact (smul_add _ _ _).symm

def mulCR (c : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (reimE (r := n) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) c).restrictScalars ℝ) ∘ₗ
    (reimE (r := n) (m := m)).symm.toLinearMap

theorem mulCR_apply (c : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    mulCR c y = reim (c * Matrix.of ((reimE (r := n) (m := m)).symm y)) := by
  unfold mulCR
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, mulLC_apply]
  rfl

end Lin

def flatL (V β : Type) [Fintype V] [Fintype β] :
    (∀ _ : V, EuclideanSpace ℝ β) →ₗ[ℝ] EuclideanSpace ℝ (V × β) where
  toFun z := WithLp.toLp 2 (fun p : V × β => z p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatL_pres (V β : Type) [Fintype V] [Fintype β] :
    (Measure.pi fun _ : V => (volume : Measure (EuclideanSpace ℝ β))).map (flatL V β) = volume := by
  classical
  have hmeas : Measurable (fun z : V → β → ℝ => Function.uncurry z) := by
    have h := (MeasurableEquiv.curry V β ℝ).symm.measurable
    rw [MeasurableEquiv.coe_curry_symm] at h
    exact h
  have hU : MeasurePreserving (fun z : V → β → ℝ => Function.uncurry z) volume volume := by
    refine ⟨hmeas, ?_⟩
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun z : V → β → ℝ => Function.uncurry z) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun v => Set.pi Set.univ (fun b => s (v, b))) := by
      ext z
      simp [Function.uncurry]
    rw [hpre, volume_pi, Measure.pi_pi]
    simp only [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  have hP := volume_preserving_pi (fun _ : V => PiLp.volume_preserving_ofLp β)
  have hT := PiLp.volume_preserving_toLp (V × β)
  have h := (hT.comp hU).comp hP
  have hf : (⇑(flatL V β)) = (WithLp.toLp 2 ∘ fun z : V → β → ℝ => Function.uncurry z) ∘
      (fun z : V → EuclideanSpace ℝ β => fun v => WithLp.ofLp (z v)) := by
    funext z
    rfl
  rw [hf]
  exact h.map_eq

theorem detJm_ne {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> norm_num)

theorem normSq_det_of_unitary {n : ℕ} (ε : Fin n → Bool) (c : Matrix (Fin n) (Fin n) ℂ)
    (hc : cᴴ * Formalism.REAL.Jm ε * c = Formalism.REAL.Jm ε) : Complex.normSq c.det = 1 := by
  have h := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := detJm_ne ε
  have h2 : star c.det * c.det = 1 := by
    have e : (star c.det * c.det) * (Formalism.REAL.Jm ε).det = 1 * (Formalism.REAL.Jm ε).det := by
      rw [one_mul]
      nth_rewrite 2 [← h]
      ring
    exact mul_right_cancel₀ hJ e
  have h3 : ((Complex.normSq c.det : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, mul_comm]
    exact h2
  exact_mod_cast h3

theorem placeJacAll_of (h : PlaceJac) : PlaceJacAll := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    intro V _ n m ε S w c ι κ _ _ L H hn hw hG hc hL1 hL2 hL3 hH1 hH2 hH3
    obtain ⟨ιv, _, Lv, T, hLQ, hLn, hLs, hLT, hTb, hTn⟩ := place_split L
      (fun v M => Mᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M i j = 0)
      hL1 (fun v => ⟨by simp, fun i _ j _ => rfl⟩) hL2 hL3
    obtain ⟨κv, _, Hv, T', hHQ, hHn, hHs, hHT, hT'b, hT'n⟩ := place_split H (fun v M => Mᴴ = M)
      hH1 (fun v => by simp) hH2 hH3
    let G : V → Matrix (Fin m) (Fin m) ℂ := fun v => (w v)ᴴ * Formalism.REAL.Jm (ε v) * w v
    let cst : V → ℝ := fun v => 2 ^ (n * m) / ‖(G v).det‖ ^ (S v).card
    have hcst : ∀ v, 0 < cst v := fun v => div_pos (by positivity) (pow_pos (norm_pos_iff.2 (hG v)) _)
    let Φ : ∀ v, (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
      fun v => mulCR (c v) ∘ₗ (reimE (r := n) (m := m)).toLinearMap ∘ₗ jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)
    have hΦ : ∀ v z, Φ v z = reim (c v * (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := by
      intro v z
      simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, mulCR_apply]
      congr 2
    have hPJ : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map
        (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) =
        ENNReal.ofReal (cst v) • volume :=
      fun v => h n m (ε v) (S v) (w v) (Lv v) (Hv v) (hn v) (hw v) (hG v) (hLQ v) (hLn v)
        (fun M h1 h2 => hLs v M ⟨h1, h2⟩) (hHQ v) (hHn v) (hHs v)
    have hd : ∀ v, (c v).det ≠ 0 := fun v h0 => by
      have := normSq_det_of_unitary (ε v) (c v) (hc v)
      rw [h0] at this
      simp at this
    have hΦm : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map (Φ v) =
        ((cst v).toNNReal : ℝ≥0∞) • volume := by
      intro v
      have e : (Φ v : _ → _) = (mulCR (m := m) (c v)) ∘
          (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := rfl
      have hm1 : Measurable (fun z : EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) =>
          reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) :=
        ((reimE (r := n) (m := m)).toLinearMap ∘ₗ
          jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)).continuous_of_finiteDimensional.measurable
      rw [e, ← Measure.map_map (mulCR (m := m) (c v)).continuous_of_finiteDimensional.measurable hm1, hPJ v,
        Measure.map_smul]
      have hC : (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool))).map (mulCR (m := m) (c v)) = volume := by
        have e2 : (mulCR (m := m) (c v) : _ → _) =
            fun y => reim (c v * Matrix.of ((reimE (r := n) (m := m)).symm y)) := funext (mulCR_apply (c v))
        rw [e2, map_mulL (c v) (hd v), normSq_det_of_unitary (ε v) (c v) (hc v)]
        simp
      rw [hC]
      rfl
      exact (mulCR (m := m) (c v)).continuous_of_finiteDimensional.measurable.aemeasurable
    let F : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →ₗ[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
      flatL V (Fin n × Fin m × Bool) ∘ₗ
        (LinearMap.pi fun v => Φ v ∘ₗ LinearMap.prodMap (LinearMap.proj v ∘ₗ T) (LinearMap.proj v ∘ₗ T'))
    have hF : ∀ z, F z = reimV (fun v => c v * (L z.1 v * w v +
        (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v))) := by
      intro z
      have e1 : F z = flatL V (Fin n × Fin m × Bool) (fun v => Φ v (T z.1 v, T' z.2 v)) := rfl
      rw [e1]
      simp only [hΦ, hLT, hHT]
      rfl
    have hmT := PI.AprimeInfG.measurePreserving_of_normSq T hTb hTn
    have hmT' := PI.AprimeInfG.measurePreserving_of_normSq T' hT'b hT'n
    have h12 := hmT.prod hmT'
    have h3 := MeasurePreserving.symm (PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v))
      (fun v => EuclideanSpace ℝ (κv v))) (PI.AprimeInfG.measurePreserving_piProdEquiv
      (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v)) (fun v => volume) (fun v => volume))
    have h123 := h3.comp h12
    have hPm : Measurable (fun x : ∀ v, EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) => fun v => Φ v (x v)) :=
      Measurable.of_eval fun v => (Φ v).continuous_of_finiteDimensional.measurable.comp (measurable_pi_apply v)
    have h4 := pi_map_smul (fun v => (volume : Measure (EuclideanSpace ℝ (ιv v))).prod volume)
      (fun v => (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool)))) (fun v => Φ v)
      (fun v => (Φ v).continuous_of_finiteDimensional.measurable) (fun v => (cst v).toNNReal)
      (fun v => by rw [ENNReal.smul_def]; exact hΦm v)
    have hfun : (F : _ → _) = flatL V (Fin n × Fin m × Bool) ∘ ((fun x v => Φ v (x v)) ∘
        ((PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v))).symm ∘
          Prod.map T T')) := rfl
    have hmap : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map F =
        ENNReal.ofReal (∏ v, cst v) • volume := by
      rw [hfun, ← Measure.map_map (flatL V (Fin n × Fin m × Bool)).continuous_of_finiteDimensional.measurable
        (hPm.comp h123.measurable), ← Measure.map_map hPm h123.measurable,
        show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl,
        h123.map_eq, h4, Measure.map_smul, flatL_pres, ENNReal.ofReal_prod_of_nonneg (fun v _ => (hcst v).le)]
      rfl
      exact (flatL V (Fin n × Fin m × Bool)).continuous_of_finiteDimensional.measurable.aemeasurable
    have hpos : ENNReal.ofReal (∏ v, cst v) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Finset.prod_pos fun v _ => hcst v
    have : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).IsAddHaarMeasure := by
      rw [show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl]
      infer_instance
    have hbij := bij_of_map (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) volume F _ hpos
      ENNReal.ofReal_ne_top hmap
    exact ⟨(LinearEquiv.ofBijective F hbij).toContinuousLinearEquiv, fun z => hF z, hmap⟩

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceJacHolds
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

theorem const_alg (N P : ℝ) (k m : ℕ) (hN : N ≠ 0) (hP : P ≠ 0) :
    ((1 / P * N) ^ k)⁻¹ * (((P * N) ^ m)⁻¹ * ((1 / P ^ 2 * (N * (N ^ 2)⁻¹)) ^ m)⁻¹) = P ^ m * P ^ k / N ^ k := by
  have h1 : N * (N ^ 2)⁻¹ = N⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  have h2 : 1 / P ^ 2 * N⁻¹ = (P ^ 2 * N)⁻¹ := by
    rw [one_div, mul_inv]
  rw [h1, h2, inv_pow, inv_inv, one_div, mul_pow, mul_pow, mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul]
  field_simp
  ring

private theorem sum_eq_sum_compl_equiv_of_eq_zero_on {n m : ℕ} (S : Finset (Fin n)) (eU : Fin m ≃ {i // i ∉ S})
    (f : Fin n → ℂ) (hf : ∀ i ∈ S, f i = 0) : ∑ i, f i = ∑ c, f (eU c) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f,
    Finset.sum_eq_zero (fun i _ => hf i.1 i.2), zero_add]
  exact (Equiv.sum_comp eU (fun i => f i)).symm

private theorem rowsM_mul {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X : Matrix (Fin k) (Fin m) ℂ) (Y Z : Matrix (Fin m) (Fin m) ℂ) :
    rowsM S eS eU X Y * Z = rowsM S eS eU (X * Z) (Y * Z) := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi, Matrix.mul_apply]

private theorem rowsM_add_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X X' : Matrix (Fin k) (Fin m) ℂ) (Y Y' : Matrix (Fin m) (Fin m) ℂ) :
    rowsM S eS eU X Y + rowsM S eS eU X' Y' = rowsM S eS eU (X + X') (Y + Y') := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi]

private theorem smul_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (c : ℂ) (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    c • rowsM S eS eU X Y = rowsM S eS eU (c • X) (c • Y) := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi]

private theorem xiF_mul_eq_rowsM {n k m : ℕ} {η : Type} [Fintype η] (ε : Fin n → Bool) (S : Finset (Fin n))
    (eS : Fin k ≃ ↥S) (eU : Fin m ≃ {i // i ∉ S}) (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) :
    xiF ε S eS eU H z * w = rowsM S eS eU (Matrix.of (cpx z.1) * (r2 • Matrix.of fun b j => w (eU b) j))
      (Matrix.diagonal (fun a => sgn ε (eU a)) * (Complex.I • H z.2) * Matrix.of fun b j => w (eU b) j) := by
  ext i j
  rw [Matrix.mul_apply, sum_eq_sum_compl_equiv_of_eq_zero_on S eU _ (fun l hl => by rw [hw l hl, mul_zero])]
  by_cases hi : i ∈ S
  · obtain ⟨a, rfl⟩ : ∃ a, ((eS a : ↥S) : Fin n) = i := ⟨eS.symm ⟨i, hi⟩, by simp⟩
    rw [rowsM_S]
    simp only [xi_SU, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨a, rfl⟩ : ∃ a, ((eU a : {i // i ∉ S}) : Fin n) = i := ⟨eU.symm ⟨i, hi⟩, by simp⟩
    rw [rowsM_U, Matrix.mul_apply]
    simp only [xi_UU, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

private theorem mul_eq_rowsM_zero_of_zero_on {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    w * X = rowsM S eS eU 0 ((Matrix.of fun b j => w (eU b) j) * X) := by
  ext i j
  by_cases hi : i ∈ S
  · simp [rowsM, hi, Matrix.mul_apply, hw i hi]
  · simp [rowsM, hi, Matrix.mul_apply]

private theorem conjTranspose_mul_Jm_mul_eq_of_zero_on {n m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n))
    (eU : Fin m ≃ {i // i ∉ S}) (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0) :
    wᴴ * Formalism.REAL.Jm ε * w = (Matrix.of fun b j => w (eU b) j)ᴴ *
      Matrix.diagonal (fun a => sgn ε (eU a)) * (Matrix.of fun b j => w (eU b) j) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply, sum_eq_sum_compl_equiv_of_eq_zero_on S eU _ (fun i hi => by rw [hw i hi b, mul_zero])]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Formalism.REAL.Jm, Matrix.mul_diagonal, sgn, Matrix.conjTranspose_apply]

private theorem rsL_reim_eq_reim_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    rsL S eS eU (reim X, reim Y) = reim (rowsM S eS eU X Y) := by
  have h1 : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ), Matrix.of (cpx (reim Z)) = Z := by
    intro p q Z
    ext a b
    exact cpx_reim Z a b
  rw [rsL_apply, h1, h1]

private theorem dg_smul_mul_add_half_eq_half_mul_add {m : ℕ} (W0 Dg Hz Ht : Matrix (Fin m) (Fin m) ℂ) (hW : W0.det ≠ 0)
    (hD : Dg * Dg = 1) :
    Dg * (Complex.I • Hz) * W0 + (1 / 2 : ℂ) • (W0 * (W0ᴴ * Dg * W0)⁻¹ * Ht) =
      ((1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹)) *
        (Complex.I • ((((Real.sqrt 2 : ℝ) : ℂ) • W0)ᴴ * Hz * (((Real.sqrt 2 : ℝ) : ℂ) • W0)) + Ht) := by
  have hWu : IsUnit W0.det := isUnit_iff_ne_zero.mpr hW
  have hWHu : IsUnit W0ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  have hDinv : Dg⁻¹ = Dg := Matrix.inv_eq_left_inv hD
  have hG : W0 * (W0ᴴ * Dg * W0)⁻¹ = Dg * W0ᴴ⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDinv, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul]
  have hB : (((Real.sqrt 2 : ℝ) : ℂ) • W0)ᴴ * Hz * (((Real.sqrt 2 : ℝ) : ℂ) • W0) =
      (2 : ℂ) • (W0ᴴ * Hz * W0) := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hG, hB]
  have hP : W0ᴴ⁻¹ * W0ᴴ = 1 := Matrix.nonsing_inv_mul _ hWHu
  simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W0ᴴ⁻¹ W0ᴴ, hP, Matrix.one_mul]
  congr 1
  congr 1
  ring

private theorem of_reimE_reim {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix.of ((reimE (r := p) (m := q)).symm (reim Z)) = Z :=
  (reimE (r := p) (m := q)).symm_apply_apply Z

private theorem continuous_reim {p q : ℕ} : Continuous (fun Y : Matrix (Fin p) (Fin q) ℂ => reim Y) :=
  (reimL (n := p) (m := q)).continuous_of_finiteDimensional.congr fun Y => reimL_apply Y


set_option maxHeartbeats 800000 in
private theorem key_lemma_12 {n m : ℕ} {ι η : Type} [Fintype ι] [Fintype η] (ε : Fin n → Bool)
    (S : Finset (Fin n)) (eS : Fin S.card ≃ ↥S) (eU : Fin m ≃ {i // i ∉ S})
    (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) (hH : ∀ t, (H t)ᴴ = H t)
    (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M)
    (Λ : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hLΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z) (W0 Dg B A2 : Matrix (Fin m) (Fin m) ℂ)
    (hW0def : W0 = Matrix.of fun b j => w (eU b) j) (hDgdef : Dg = Matrix.diagonal fun a => sgn ε (eU a))
    (hBdef : B = ((Real.sqrt 2 : ℝ) : ℂ) • W0) (hA2def : A2 = (1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹))
    (hW0 : W0.det ≠ 0) (hDD : Dg * Dg = 1)
    (z1 : EuclideanSpace ℝ (Fin S.card × Fin m × Bool)) (z2 t : EuclideanSpace ℝ η) :
    reim (L (Λ (z1, z2)) * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H t)) =
      rsL S eS eU (reim (Matrix.of ((reimE (r := S.card) (m := m)).symm z1) * (r2 • W0)),
        reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
          (psiLp H (congH H hH hnH hsH B z2, t))))) := by
  subst hBdef hA2def
  rw [hLΛ, xiF_mul_eq_rowsM ε S eS eU H w hw, mul_eq_rowsM_zero_of_zero_on S eS eU w hw, rowsM_mul, smul_rowsM,
    rowsM_add_rowsM, psiLp_apply, of_reimE_reim, ← cpx_eq, rsL_reim_eq_reim_rowsM, congH_spec,
    conjTranspose_mul_Jm_mul_eq_of_zero_on ε S eU w hw, ← hW0def, ← hDgdef]
  congr 2
  · rw [Matrix.zero_mul, smul_zero, add_zero]
  · exact dg_smul_mul_add_half_eq_half_mul_add W0 Dg (H z2) (H t) hW0 hDD


set_option maxHeartbeats 800000 in
private theorem map_volume_reim_block_eq_of_det_ne_zero {m : ℕ} {η : Type} [Fintype η]
    (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) (hH : ∀ t, (H t)ᴴ = H t)
    (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M)
    (B A2 : Matrix (Fin m) (Fin m) ℂ) (hB : B.det ≠ 0) (hA : A2.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map
      (fun p => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
        (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))) =
      (ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ * ENNReal.ofReal (Complex.normSq A2.det ^ m)⁻¹) •
        volume := by
  have hc2 : Continuous fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      Matrix.of ((reimE (r := m) (m := m)).symm y) :=
    (reimE (r := m) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hmulLm : Measurable fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y)) :=
    (continuous_reim.comp (continuous_const.matrix_mul hc2)).measurable
  have hpsim : Measurable (psiLp H) := (psiLp H).continuous_of_finiteDimensional.measurable
  have hcgm : Measurable (congH H hH hnH hsH B) :=
    (congH H hH hnH hsH B).continuous_of_finiteDimensional.measurable
  have hPm : Measurable (Prod.map (congH H hH hnH hsH B)
      (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η)) := Measurable.prodMap hcgm measurable_id
  have hcg : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map
      (Prod.map (congH H hH hnH hsH B) id) =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hcgm measurable_id,
      cong_factor H hH hnH hsH B hB, Measure.map_id, Measure.prod_smul_left]
  have e : (fun p => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
      (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))) =
      (fun y => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y))) ∘ (psiLp H) ∘
        (Prod.map (congH H hH hnH hsH B) id) := rfl
  rw [e, ← Measure.map_map hmulLm (hpsim.comp hPm), ← Measure.map_map hpsim hPm, hcg,
    Measure.map_smul, (psi_mp H hH hnH hsH).map_eq, Measure.map_smul, map_mulL A2 hA, smul_smul]
  all_goals first | exact hmulLm.aemeasurable | exact hpsim.aemeasurable

private theorem inv_pow_mul_inv_pow_eq_two_pow_div_pow (N : ℝ) (m k : ℕ) (hN : N ≠ 0) :
    ((1 / (2 : ℝ) ^ m * N) ^ k)⁻¹ * ((((2 : ℝ) ^ m * N) ^ m)⁻¹ * (((1 / 4 : ℝ) ^ m * N⁻¹) ^ m)⁻¹) =
      2 ^ ((m + k) * m) / N ^ k := by
  have h4 : (1 / 4 : ℝ) ^ m * N⁻¹ = 1 / ((2 : ℝ) ^ m) ^ 2 * (N * (N ^ 2)⁻¹) := by
    rw [show N * (N ^ 2)⁻¹ = N⁻¹ by rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN, one_mul],
      show ((2 : ℝ) ^ m) ^ 2 = 4 ^ m by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      _root_.one_div_pow]
  rw [h4, const_alg N (2 ^ m) k m hN (by positivity), ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring


set_option maxHeartbeats 800000 in
theorem placeJac_holds : PlaceJac := by
  intro n m ε S w ι η _ _ L H hn hw hG hL hnL hLs hH hnH hsH
  classical
  have hcardU : Fintype.card {i // i ∉ S} = m := by
    simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    omega
  obtain ⟨eS⟩ : Nonempty (Fin S.card ≃ ↥S) := ⟨S.equivFin.symm⟩
  obtain ⟨eU⟩ : Nonempty (Fin m ≃ {i // i ∉ S}) := ⟨(Fintype.equivFinOfCardEq hcardU).symm⟩
  obtain ⟨W0, hW0def⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = Matrix.of fun b j => w (eU b) j := ⟨_, rfl⟩
  obtain ⟨Dg, hDgdef⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = Matrix.diagonal fun a => sgn ε (eU a) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = ((Real.sqrt 2 : ℝ) : ℂ) • W0 := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = (1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹) := ⟨_, rfl⟩
  have hgram : wᴴ * Formalism.REAL.Jm ε * w = W0ᴴ * Dg * W0 := by
    rw [hW0def, hDgdef]
    exact conjTranspose_mul_Jm_mul_eq_of_zero_on ε S eU w hw
  have hDD : Dg * Dg = 1 := by
    rw [hDgdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [sgn]
    split_ifs <;> norm_num
  have hDnorm : ‖Dg.det‖ = 1 := by
    rw [hDgdef, Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [sgn]
    split_ifs <;> simp
  have hW0 : W0.det ≠ 0 := by
    intro h0
    apply hG
    rw [hgram, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hWHu : IsUnit W0ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW0)
  have hDdet : Dg.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDnorm
    exact zero_ne_one hDnorm
  have hBdet : B.det ≠ 0 := by
    rw [hBdef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')) hW0
  have hA2det : A2.det ≠ 0 := by
    rw [hA2def, Matrix.det_smul, Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero hDdet (Matrix.isUnit_nonsing_inv_det _ hWHu).ne_zero)
  have hR : (r2 • W0).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).ne')) hW0

  obtain ⟨Λ, hΛ, hLΛ⟩ := dom_exists (ε := ε) (S := S) (eS := eS) (eU := eU) (H := H)
    L hL hnL hLs hH hnH hsH

  have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
      Matrix.of ((reimE (r := S.card) (m := m)).symm y) :=
    (reimE (r := S.card) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hc2 : Continuous fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      Matrix.of ((reimE (r := m) (m := m)).symm y) :=
    (reimE (r := m) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hΦ1m : Measurable fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
      reim (Matrix.of ((reimE (r := S.card) (m := m)).symm y) * (r2 • W0)) :=
    (continuous_reim.comp (hc1.matrix_mul continuous_const)).measurable
  have hmulLm : Measurable fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y)) :=
    (continuous_reim.comp (continuous_const.matrix_mul hc2)).measurable
  have hpsim : Measurable (psiLp H) := (psiLp H).continuous_of_finiteDimensional.measurable
  have hcgm : Measurable (congH H hH hnH hsH B) :=
    (congH H hH hnH hsH B).continuous_of_finiteDimensional.measurable
  have hPm : Measurable (Prod.map (congH H hH hnH hsH B)
      (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η)) := Measurable.prodMap hcgm measurable_id
  have hΦ2m : Measurable fun p : EuclideanSpace ℝ η × EuclideanSpace ℝ η =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
        (psiLp H (Prod.map (congH H hH hnH hsH B) id p)))) := hmulLm.comp (hpsim.comp hPm)
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hHc : Continuous H := H.continuous_of_finiteDimensional
  have hFc : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2) := by
    have h1 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => L z.1 * w :=
      (hLc.comp continuous_fst).matrix_mul continuous_const
    have h2 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2 :=
      continuous_const.matrix_mul (hHc.comp continuous_snd)
    have h3 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2) := h2.const_smul (1 / 2 : ℂ)
    exact h1.add h3
  have hFm : Measurable fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2)) :=
    (continuous_reim.comp hFc).measurable
  have hrsm : Measurable (rsL S eS eU) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact (rsL S eS eU).continuous_of_finiteDimensional.measurable
  have hΦm := Measurable.prodMap hΦ1m hΦ2m

  have hPre : MeasurePreserving (Prod.map Λ (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η))
      (volume : Measure ((EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η) ×
        EuclideanSpace ℝ η)) (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) := by
    rw [Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η)
      (EuclideanSpace ℝ η), Measure.volume_eq_prod (EuclideanSpace ℝ ι) (EuclideanSpace ℝ η)]
    exact hΛ.prod (MeasurePreserving.id _)
  have hAssoc := measurePreserving_prodAssoc
    (volume : Measure (EuclideanSpace ℝ (Fin S.card × Fin m × Bool)))
    (volume : Measure (EuclideanSpace ℝ η)) (volume : Measure (EuclideanSpace ℝ η))
  have hfun : (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2))) ∘ Prod.map Λ id =
      (rsL S eS eU) ∘ (Prod.map (fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
        reim (Matrix.of ((reimE (r := S.card) (m := m)).symm y) * (r2 • W0)))
        (fun p : EuclideanSpace ℝ η × EuclideanSpace ℝ η => reim (A2 * Matrix.of
          ((reimE (r := m) (m := m)).symm (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))))
        ∘ (MeasurableEquiv.prodAssoc) := by
    funext ⟨⟨z1, z2⟩, t⟩
    exact key_lemma_12 ε S eS eU w hw L H hH hnH hsH Λ hLΛ W0 Dg B A2 hW0def hDgdef hBdef hA2def hW0 hDD
      z1 z2 t
  rw [← hPre.map_eq, Measure.map_map hFm hPre.measurable, hfun,
    ← Measure.map_map hrsm (hΦm.comp MeasurableEquiv.prodAssoc.measurable),
    ← Measure.map_map hΦm MeasurableEquiv.prodAssoc.measurable,
    Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η)
      (EuclideanSpace ℝ η),
    Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool)) (EuclideanSpace ℝ η),
    hAssoc.map_eq, ← Measure.map_prod_map _ _ hΦ1m hΦ2m,
    ← Measure.volume_eq_prod (EuclideanSpace ℝ η) (EuclideanSpace ℝ η),
    map_volume_reim_block_eq_of_det_ne_zero H hH hnH hsH B A2 hBdet hA2det, map_mulR (r2 • W0) hR,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
    ← Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool))
      (EuclideanSpace ℝ (Fin m × Fin m × Bool)), (rs_mp S eS eU).map_eq]
  all_goals try exact hrsm.aemeasurable

  congr 1
  have hN : Complex.normSq W0.det ≠ 0 := (Complex.normSq_pos.mpr hW0).ne'
  have e1 : Complex.normSq (r2 • W0).det = 1 / (2 : ℝ) ^ m * Complex.normSq W0.det := by
    rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    congr 1
    simp only [r2, Complex.normSq_ofReal]
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_pow]
  have e2 : Complex.normSq B.det = (2 : ℝ) ^ m * Complex.normSq W0.det := by
    rw [hBdef, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdinv : Complex.normSq (W0ᴴ⁻¹).det = (Complex.normSq W0.det)⁻¹ := by
    have h1 : (W0ᴴ⁻¹).det * W0ᴴ.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hWHu, Matrix.det_one]
    have h3 := congrArg Complex.normSq h1
    rw [map_mul, map_one, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_conj] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hDsq : Complex.normSq Dg.det = 1 := by
    rw [Complex.normSq_eq_norm_sq, hDnorm, one_pow]
  have h12 : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    norm_num
  have e3 : Complex.normSq A2.det = (1 / 4) ^ m * (Complex.normSq W0.det)⁻¹ := by
    rw [hA2def, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, map_mul, map_mul, map_pow, hDsq,
      hdinv, h12, one_mul]
  have e4 : ‖(wᴴ * Formalism.REAL.Jm ε * w).det‖ = Complex.normSq W0.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hDnorm, mul_one,
      Matrix.det_conjTranspose, norm_star, Complex.normSq_eq_norm_sq, sq]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (Complex.normSq_nonneg _) _)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (Complex.normSq_nonneg _) _))]
  congr 1
  rw [e1, e2, e3, e4, show n * m = (m + S.card) * m from congrArg (· * m) hn,
    inv_pow_mul_inv_pow_eq_two_pow_div_pow _ m S.card hN]

end PI.AprimeInfW
end
end

namespace PI.AprimeInfW

theorem placeJacAll_holds : PlaceJacAll := placeJacAll_of placeJac_holds

end PI.AprimeInfW

module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne
theorem UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] (y : R →ₐ[ℤ_[l]] PadicAlgCl l),
    ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (O := ℤ_[l]) y a ha
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GLRealOpen
theorem UpperTheory.Reformulated.B.GLRealOpen.glR_open :
    ∀ {K : Type} [inst : CommRing K] [inst_1 : TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
      IsOpen (↑R : Set K) → ∀ (n : ℕ), IsOpen (↑(UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n) : Set (GL (Fin n) K)) := by
  intro K _ _ _ R hR n
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R} := by
    have e : {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R}
        = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) K => M i j) ⁻¹' (R : Set K) := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [e]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hR.preimage (continuous_id.matrix_elem i j)
  have h1 : Continuous fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv
  exact (hM.preimage h1).inter (hM.preimage h2)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalSituation
theorem UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : Fin r → E),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • w ∈ X.Λ := by
  intro E _ _ _ r X w
  have hw : w ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact X.Λ.smul_mem b hax
    · rw [mul_smul]; exact X.Λ.smul_mem a hby
  | smul t x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) t
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      simpa using hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      ext i
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
      field_simp
    rw [key]
    exact X.Λ.smul_mem p hax
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreBis
theorem UpperTheory.Reformulated.B.Qf46.cover :
    ∀ {G Y : Type} [inst : Group G] [Countable G] [inst_2 : MeasurableSpace Y] [inst_3 : MulAction G Y]
      (μ : MeasureTheory.Measure Y),
      UpperTheory.Esk.Pres G μ →
        ∀ (b : Y → ℝ),
          UpperTheory.Esk.IsCut G b →
            ∀ (S : Set Y),
              MeasurableSet S →
                (∀ (y : Y), ∃ (g : G), g • y ∈ S) → ∫⁻ (y : Y), ENNReal.ofReal (b y) ∂μ ≤ (μ : Set Y → ENNReal) S := by
  intro G Y _ _ _ _ μ hP b hb S hS hc
  have hB : Measurable fun y => ENNReal.ofReal (b y) := hb.meas.ennreal_ofReal
  have hF : ∀ g : G, Measurable (S.indicator fun y => ENNReal.ofReal (b (g⁻¹ • y))) :=
    fun g => (hB.comp (hP g⁻¹).measurable).indicator hS
  have hone : ∀ y, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
    intro y
    have h : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ∑' g : G, ENNReal.ofReal (b (g • y)) :=
      (Equiv.inv G).tsum_eq (fun g : G => ENNReal.ofReal (b (g • y)))
    rw [h, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq,
      ENNReal.ofReal_one]
  calc ∫⁻ y, ENNReal.ofReal (b y) ∂μ
      ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ := by
        refine MeasureTheory.lintegral_mono fun y => ?_
        obtain ⟨g, hg⟩ := hc y
        refine le_trans ?_ (ENNReal.le_tsum g)
        rw [Set.indicator_of_mem hg, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ :=
        MeasureTheory.lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        (MeasureTheory.lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ := by
        refine MeasureTheory.lintegral_congr fun y => ?_
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, hone, Pi.one_apply]
        · simp only [Set.indicator_of_notMem hy, tsum_zero]
    _ = μ S := MeasureTheory.lintegral_indicator_one hS
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirCommutation
theorem UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm :
    ∀ {A : Type} [inst : Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A),
      Formalism.REAL.GlRel E → ∀ (c d : Fin n), ε c = ε d → Formalism.REAL.CasK ε E * E c d = E c d * Formalism.REAL.CasK ε E := by
  intro A _ n ε E h c d hcd
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a := by
    intro a b
    have h1 := h b a c d
    have h2 := h a b c d
    have : E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a
        = E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0))
          + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
      noncomm_ring
    rw [this, ← h1, ← h2]
    noncomm_ring
  have S1 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
      = ∑ b, if ε c = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have S4 : ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0)
      = ∑ b, if ε d = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have S2 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
      = ∑ a, if ε a = ε d then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have S3 : ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
      = ∑ a, if ε a = ε c then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e : Formalism.REAL.CasK ε E * E c d - E c d * Formalism.REAL.CasK ε E =
      ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) := by
    simp only [Formalism.REAL.CasK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0)
      = ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
        - ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
        + ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
        - ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [key]
    split_ifs <;> simp
  rw [← sub_eq_zero, e, e2, S1, S2, S3, S4, hcd]
  abel
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvectorExistence
private theorem common_eigenvector_commuting_family {T D : Type}
    [AddCommGroup D] [_root_.Module ℂ D] [FiniteDimensional ℂ D] (φ : T → _root_.Module.End ℂ D)
    (hc : ∀ (s t : T), Commute (φ s) (φ t)) :
    ∀ (n : ℕ) (W : Submodule ℂ D), _root_.Module.finrank ℂ W = n → W ≠ ⊥ →
      (∀ (t : T), ∀ x ∈ W, φ t x ∈ W) →
      ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hW hinv
    by_cases hs : ∀ t, ∃ c : ℂ, ∀ x ∈ W, φ t x = c • x
    · choose a ha using hs
      obtain ⟨l, hlW, hl⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨l, a, hl, fun t => ha t l hlW⟩
    · push Not at hs
      obtain ⟨t, ht⟩ := hs
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨c, hcv⟩ := _root_.Module.End.exists_eigenvalue ((φ t).restrict (hinv t))
      obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
      have hv0 : (v : D) ≠ 0 := fun h => hv.2 (Subtype.ext h)
      have hv1 : φ t (v : D) = c • (v : D) := by
        have := congrArg Subtype.val hv.apply_eq_smul
        simpa using this
      let E : Submodule ℂ D := W ⊓ _root_.Module.End.eigenspace (φ t) c
      have hE : ∀ y, y ∈ E ↔ y ∈ W ∧ φ t y = c • y := by
        intro y
        simp [E, Submodule.mem_inf, _root_.Module.End.mem_eigenspace_iff]
      have hEbot : E ≠ ⊥ := by
        intro h
        have : (v : D) ∈ E := (hE _).2 ⟨v.2, hv1⟩
        rw [h] at this
        exact hv0 (by simpa using this)
      have hlt : E < W := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hxW, hx⟩ := ht c
        exact hx ((hE x).1 (h ▸ hxW)).2
      have hfr : _root_.Module.finrank ℂ E < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      refine ih _ hfr E rfl hEbot ?_
      intro s y hy
      obtain ⟨hyW, hyc⟩ := (hE y).1 hy
      refine (hE _).2 ⟨hinv s y hyW, ?_⟩
      have h1 : φ t (φ s y) = φ s (φ t y) := by
        have := (hc t s).eq
        exact congrArg (fun f : _root_.Module.End ℂ D => f y) this
      rw [h1, hyc, map_smul]

theorem UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector :
    ∀ {T D : Type}
    [inst : AddCommGroup D] [inst_1 : _root_.Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D] (φ : T → Module.End ℂ D),
    (∀ (s t : T), Commute (φ s) (φ t)) → ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro T D _ _ _ _ φ hc
  exact common_eigenvector_commuting_family φ hc _ ⊤ rfl top_ne_bot (fun _ _ _ => Submodule.mem_top)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoundedSums
noncomputable def UpperTheory.Reformulated.B.BoundedSums.Bdd :
    {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop :=
    fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), V.Ge K (s n)

noncomputable def UpperTheory.Reformulated.B.BoundedSums.BddS :
    {C : Type} → [inst : Field C] → {σ : Type} → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → MvPowerSeries σ C) → Prop :=
    fun {C : Type} [Field C] {σ : Type} (V : Formalism.L2.FormalSeriesBounds.VF C) (f : ℕ → MvPowerSeries σ C) ↦
      ∀ (μ : σ →₀ ℕ), UpperTheory.Reformulated.B.BoundedSums.Bdd V fun (n : ℕ) ↦ (MvPowerSeries.coeff μ : MvPowerSeries σ C → C) (f n)

private theorem UpperTheory.Reformulated.B.BoundedSums.bdd_sum {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {α : Type}
    (T : Finset α) (s : α → ℕ → C) (h : ∀ a ∈ T, UpperTheory.Reformulated.B.BoundedSums.Bdd V (s a)) :
    UpperTheory.Reformulated.B.BoundedSums.Bdd V fun n ↦ ∑ a ∈ T, s a n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simpa using Formalism.L2.FormalSeriesBounds.VF.Ge.zero (V := V) 0⟩
  | insert a T ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨L, hL⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨min K L, fun n => ?_⟩
    show V.Ge (min K L) (∑ b ∈ insert a T, s b n)
    rw [Finset.sum_insert ha]
    exact ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))

private theorem UpperTheory.Reformulated.B.BoundedSums.bddS_mul {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ : Type}
    {f g : ℕ → MvPowerSeries σ C} (hf : UpperTheory.Reformulated.B.BoundedSums.BddS V f)
    (hg : UpperTheory.Reformulated.B.BoundedSums.BddS V g) : UpperTheory.Reformulated.B.BoundedSums.BddS V fun n ↦ f n * g n := by
  classical
  intro μ
  have h := UpperTheory.Reformulated.B.BoundedSums.bdd_sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (fun p n => MvPowerSeries.coeff p.1 (f n) * MvPowerSeries.coeff p.2 (g n)) (fun p _ => by
      obtain ⟨K, hK⟩ := hf p.1
      obtain ⟨L, hL⟩ := hg p.2
      exact ⟨K + L, fun n => (hK n).mul (hL n)⟩)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n => ?_⟩
  show V.Ge K (MvPowerSeries.coeff μ (f n * g n))
  rw [MvPowerSeries.coeff_mul]
  exact hK n

theorem UpperTheory.Reformulated.B.BoundedSums.prod :
    ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C},
      (∀ i ∈ S, UpperTheory.Reformulated.B.BoundedSums.BddS V (f i)) → UpperTheory.Reformulated.B.BoundedSums.BddS V fun (n : ℕ) ↦ ∏ i ∈ S, f i n := by
  intro C _ V σ ι S f h
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro μ
    refine ⟨0, fun n => ?_⟩
    show V.Ge 0 (MvPowerSeries.coeff μ (∏ i ∈ (∅ : Finset ι), f i n))
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | insert a S ha ih =>
    have h2 := UpperTheory.Reformulated.B.BoundedSums.bddS_mul (h a (Finset.mem_insert_self a S))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.prod_insert ha] using h2
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonemptyNormalModelOfPresentation
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfFiniteOverNormal
namespace UpperTheory

open nonZeroDivisors

private theorem finite_of_finite_over_normal (P A K : Type*) [CommRing P] [IsDomain P]
    [CharZero P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A]
    [Algebra P A] [FaithfulSMul P A] [Module.Finite P A] [Field K] [Algebra A K]
    [IsFractionRing A K] : Module.Finite A (integralClosure A K) := by
  letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance
  haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  haveI : CharZero (FractionRing P) := IsFractionRing.charZero P
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : IsIntegralClosure (integralClosure A K) P K :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩
  haveI : Module.Finite P (integralClosure A K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A K)

theorem integralClosure_finite (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K

end UpperTheory
end

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R S : Type) [CommRing R] [Nontrivial R] [Algebra ℂ R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hπ : Function.Surjective π) (hJ : RingHom.ker π = J)
    (hinj : Function.Injective (algebraMap R S))
    (hfrac : ∀ s : S, ∃ a b : R, b ≠ 0 ∧ algebraMap R S b * s = algebraMap R S a) :
    Nonempty (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  let φ : MvPolynomial (Fin n ⊕ Fin m) ℂ →+* S :=
    eval₂Hom ((algebraMap R S).comp (algebraMap ℂ R))
      (Sum.elim (fun i => algebraMap R S (π (X i))) s)
  have hcomp : φ.comp (rename Sum.inl :
      MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      = (algebraMap R S).comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h : π (C r) = algebraMap ℂ R r := π.commutes r
      simp [φ, h]
    · intro i
      simp [φ]
  have hren : ∀ q, φ (rename Sum.inl q) = algebraMap R S (π q) := fun q =>
    RingHom.congr_fun hcomp q
  have hY : ∀ i, φ (X (Sum.inr i)) = s i := fun i => by simp [φ]
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hy
    choose p hp using fun i => hπ (c i)
    refine ⟨∑ i, rename Sum.inl (p i) * X (Sum.inr i), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hren, hY, hp, Algebra.smul_def]
  refine ⟨⟨m, RingHom.ker φ, RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective hsurj).symm, ?_, ?_, ?_⟩⟩
  · ext q
    rw [Ideal.mem_comap, RingHom.mem_ker, hren, ← hJ, RingHom.mem_ker,
      map_eq_zero_iff _ hinj]
  · intro i
    obtain ⟨Q, hQ, hQ0⟩ : IsIntegral R (s i) := Algebra.IsIntegral.isIntegral _
    obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (f := π.toRingHom) (Polynomial.mem_lifts_of_surjective hπ Q) hQ
    refine ⟨P, hPm, ?_⟩
    rw [RingHom.mem_ker, Polynomial.hom_eval₂, hcomp, hY, ← Polynomial.eval₂_map, hP, hQ0]
  · intro i
    obtain ⟨a, b, hb, hab⟩ := hfrac (s i)
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    refine ⟨a, b, ?_, ?_⟩
    · rw [← hJ, RingHom.mem_ker]
      exact hb
    · rw [RingHom.mem_ker, map_sub, map_mul, hren, hren, hY, hab, sub_self]

theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation :
    ∀ {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type) [inst : CommRing R] [IsDomain R] [inst_2 : Algebra ℂ R]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R),
    Function.Surjective (⇑π : MvPolynomial (Fin n) ℂ → R) →
      RingHom.ker π = J →
        Nonempty
          (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel
            J) := by
  intro n J R _ _ _ π hπ hJ
  haveI : Algebra.FiniteType ℂ R := Algebra.FiniteType.of_surjective π hπ
  haveI : Module.Finite R (integralClosure R (FractionRing R)) := UpperTheory.integralClosure_finite ℂ R (FractionRing R)
  haveI : IsIntegrallyClosed (integralClosure R (FractionRing R)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  refine UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension J R
    (integralClosure R (FractionRing R)) π hπ hJ ?_ ?_
  · intro x y hxy
    exact IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hxy)
  · intro s
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (s : FractionRing R)
    refine ⟨a, b, nonZeroDivisors.coe_ne_zero b, Subtype.ext ?_⟩
    rw [mul_comm] at hab
    exact hab
end

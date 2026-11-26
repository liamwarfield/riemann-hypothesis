module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFrameKTypeDecomposition

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBound
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem setIntegral_translate_of_iff {X : Type} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (m : Measure X)
    [m.IsAddHaarMeasure] {A D : Set X} (hA : MeasurableSet A) (hD : MeasurableSet D) (g : X)
    (h : ∀ y, g + y ∈ A ↔ y ∈ D) (f : X → ℂ) :
    ∫ x in A, f x ∂m = ∫ y in D, f (g + y) ∂m := by
  rw [← integral_indicator hA, ← integral_indicator hD,
    ← integral_add_left_eq_self (μ := m) (Set.indicator A f) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ D
  · simp [Set.indicator, hy, (h y).2 hy]
  · have : g + y ∉ A := fun hh => hy ((h y).1 hh)
    simp [Set.indicator, hy, this]

theorem weyl_sq_compact_open : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ) (B : X → X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) →
    (∀ x y, q (x + y) = q x * q y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    ∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤
      (m (L : Set X)).toReal * (m {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1}).toReal := by
  intro X _ _ _ _ _ _ _ m _ L hLc hLo q B hq hq1 hqB hB1 hB2 x₀
  set C : Set X := {y | y - x₀ ∈ L} with hCdef
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hCo : IsOpen C := hLo.preimage (continuous_id.sub continuous_const)
  have hCm : MeasurableSet C := hCo.measurableSet
  have hLfin : m (L : Set X) < ⊤ := hLc.measure_lt_top
  have hmC : m C = m (L : Set X) := by
    have : C = (fun h => -x₀ + h) ⁻¹' (L : Set X) := by
      ext y; simp [hCdef, sub_eq_neg_add]
    rw [this, measure_preimage_add]
  have hCfin : m C < ⊤ := hmC ▸ hLfin
  haveI : IsFiniteMeasure (m.restrict C) := ⟨by simpa using hCfin⟩
  haveI : IsFiniteMeasure (m.restrict (L : Set X)) := ⟨by simpa using hLfin⟩
  have hq0 : ∀ x, q x ≠ 0 := fun x h => by simpa [h] using hq1 x
  have hBnorm : ∀ x y, ‖B x y‖ = 1 := fun x y => by
    have := congrArg norm (hqB x y)
    simpa [hq1] using this.symm
  have hBform : ∀ x y, B x y = q (x + y) / (q x * q y) := fun x y => by
    rw [hqB x y]; field_simp [hq0 x, hq0 y]
  have hBc : Continuous (Function.uncurry B) := by
    have : Function.uncurry B = fun p : X × X => q (p.1 + p.2) / (q p.1 * q p.2) := by
      funext p; exact hBform p.1 p.2
    rw [this]
    exact (hq.comp (continuous_fst.add continuous_snd)).div
      ((hq.comp continuous_fst).mul (hq.comp continuous_snd)) fun p => mul_ne_zero (hq0 _) (hq0 _)
  have hconj : ∀ x, (starRingEnd ℂ) (q x) * q x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hq1]; simp
  set I : ℂ := ∫ x in C, q x ∂m with hI
  set J : X → ℂ := fun y => ∫ x in C, B x y ∂m with hJ

  have hstep : I * (starRingEnd ℂ) I = ∫ y in (L : Set X), q y * J y ∂m := by
    have h1 : I * (starRingEnd ℂ) I = ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m := by
      rw [integral_mul_const, integral_conj, mul_comm]
    have h2 : ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m
        = ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m := by
      refine setIntegral_congr_fun hCm fun x' hx' => ?_
      have hx'' : x' - x₀ ∈ L := hx'
      have ht : I = ∫ y in (L : Set X), q (x' + y) ∂m := by
        refine setIntegral_translate_of_iff m hCm hLm x' (fun y => ?_) q
        have e : x' + y - x₀ = (x' - x₀) + y := by abel
        simp only [hCdef, Set.mem_setOf_eq, e, SetLike.mem_coe]
        exact L.add_mem_cancel_left hx''
      rw [ht, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [hqB x' y]
      calc _ = ((starRingEnd ℂ) (q x') * q x') * (q y * B x' y) := by ring
        _ = _ := by rw [hconj, one_mul]
    have h3 : ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m
        = ∫ y in (L : Set X), ∫ x' in C, q y * B x' y ∂m ∂m := by
      refine integral_integral_swap ?_
      have hc : Continuous (Function.uncurry fun x' y => q y * B x' y) :=
        (hq.comp continuous_snd).mul hBc
      refine Integrable.of_bound hc.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.uncurry, hq1, hBnorm]
    rw [h1, h2, h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hJ]
    rw [integral_const_mul]
  have hJle : ∀ y, ‖J y‖ ≤ (m (L : Set X)).toReal := fun y => by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := C) (f := fun x => B x y) (C := 1)
      hCfin (fun x _ => (hBnorm x y).le)
    simpa [Measure.real, hmC] using this
  have hJ0 : ∀ y l, l ∈ L → B l y ≠ 1 → J y = 0 := fun y l hl hne => by
    have ht : J y = ∫ x in C, B (l + x) y ∂m := by
      refine setIntegral_translate_of_iff m hCm hCm l (fun x => ?_) (fun x => B x y)
      have e : l + x - x₀ = l + (x - x₀) := by abel
      simp only [hCdef, Set.mem_setOf_eq, e]
      exact L.add_mem_cancel_left hl
    have h2 : J y = B l y * J y := by
      conv_lhs => rw [ht]
      simp only [hJ, hB1, integral_const_mul]
    have h3 : (1 - B l y) * J y = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
  set S : Set X := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hSL : S ⊆ (L : Set X) := fun y hy => hy.1
  have hSfin : m S < ⊤ := (measure_mono hSL).trans_lt hLfin
  have hcut : ∫ y in (L : Set X), q y * J y ∂m = ∫ y in S, q y * J y ∂m := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hLm hSL fun y hy => ?_
    have : ¬ ∀ l ∈ L, B l y = 1 := fun h => hy.2 ⟨hy.1, h⟩
    push_neg at this
    obtain ⟨l, hl, hne⟩ := this
    simp [hJ0 y l hl hne]
  have hbound : ‖∫ y in S, q y * J y ∂m‖ ≤ (m (L : Set X)).toReal * (m S).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := S) (f := fun y => q y * J y)
      (C := (m (L : Set X)).toReal) hSfin (fun y _ => by simpa [hq1] using hJle y)
    simpa [Measure.real] using this
  have hsq : ‖I‖ ^ 2 = ‖I * (starRingEnd ℂ) I‖ := by
    rw [norm_mul, RCLike.norm_conj, sq]
  rw [hsq, hstep, hcut]
  exact hbound

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_quadratic_character_bound : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ) (B : X → X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) →
    (∀ x y, q (x + y) = q x * q y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    ∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤
      (m (L : Set X)).toReal * (m {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1}).toReal := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependent
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma cont_coord (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (b : Fin n) (i : Fin M) (w : W) :
    Continuous fun X : Fin n → Fin M → K => κ (X b i) w :=
  (continuous_apply w).comp (hκ.continuous.comp ((continuous_apply i).comp (continuous_apply b)))

lemma isOpen_nearK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (w : W) (s : Fin n → ℂ) (ε : ℝ) :
    IsOpen (nearK (M := M) κ w s ε) := by
  have : nearK (M := M) κ w s ε = ⋂ i, {X | ‖∑ b, s b * κ (X b i) w‖ < ε} := by
    ext X; simp [nearK]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt ?_ continuous_const
  refine Continuous.norm ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_const.mul (cont_coord κ hκ b i w)

lemma isCompact_boxK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (r : Fin n → W → ℝ) :
    IsCompact (boxK (M := M) κ r) := by
  let e : K ≃ₜ (W → ℂ) := hκ.homeomorph κ
  let Φ : (Fin n → Fin M → K) ≃ₜ (Fin n → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  have hB : IsCompact (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_univ_pi fun w =>
      isCompact_closedBall _ _
  have : boxK (M := M) κ r = Φ ⁻¹' (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) := by
    ext X
    simp [boxK, Φ, e]
  rw [this]
  exact (Homeomorph.isCompact_preimage Φ).2 hB

lemma linIndep_iff (κ : K ≃+* (W → ℂ)) {n M : ℕ} (X : Fin n → Fin M → K) :
    LinearIndependent K X ↔ ∀ w, LinearIndependent ℂ (fun b i => κ (X b i) w) := by
  classical
  constructor
  · intro hX w
    rw [Fintype.linearIndependent_iff] at hX ⊢
    intro t ht b
    have key := hX (fun b => κ.symm (Pi.single w (t b))) (by
      funext i
      apply κ.injective
      funext w'
      have := congrFun ht i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, Finset.sum_apply, Pi.mul_apply]
      by_cases h : w' = w
      · subst h; simpa using this
      · simp [Pi.single_apply, h])
    have := congrFun (congrArg κ (key b)) w
    simpa using this
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro c hc b
    apply κ.injective
    funext w
    have hw := h w
    rw [Fintype.linearIndependent_iff] at hw
    have := hw (fun b => κ (c b) w) (by
      funext i
      have := congrArg (fun y => κ y w) (congrFun hc i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Finset.sum_apply, map_sum, map_mul] using this) b
    simpa using this

lemma isOpen_linIndep (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) (n M : ℕ) :
    IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} := by
  have : {X : Fin n → Fin M → K | LinearIndependent K X} =
      ⋂ w, (fun X : Fin n → Fin M → K => fun b i => κ (X b i) w) ⁻¹'
        {Y : Fin n → Fin M → ℂ | LinearIndependent ℂ Y} := by
    ext X; simp [linIndep_iff κ X]
  rw [this]
  refine isOpen_iInter_of_finite fun w => ?_
  refine isOpen_setOfPred_linearIndependent.preimage ?_
  exact continuous_pi fun b => continuous_pi fun i => cont_coord κ hκ b i w

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma goodK_subset (κ : K ≃+* (W → ℂ)) {n M : ℕ} (R ε : ℝ) (hε : 0 < ε) :
    goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro X hX
  rcases hX with ⟨-, hX⟩
  show LinearIndependent K X
  rw [Fintype.linearIndependent_iff]
  intro c hc b0
  by_contra h0
  have hk : κ (c b0) ≠ 0 := by
    intro h; exact h0 (κ.injective (by simpa using h))
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hk
  haveI : Nonempty (Fin n) := ⟨b0⟩
  obtain ⟨a, ha⟩ := Finite.exists_max fun b => ‖κ (c b) w‖
  have hca : κ (c a) w ≠ 0 := by
    intro h
    have := ha b0
    rw [h, norm_zero] at this
    exact hw (norm_le_zero_iff.1 this)
  have hsum : ∀ i, ∑ b, κ (c b) w * κ (X b i) w = 0 := by
    intro i
    have := congrArg (fun y => κ y w) (congrFun hc i)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Finset.sum_apply, map_sum, map_mul] using this
  apply hX
  simp only [Set.mem_iUnion]
  refine ⟨w, a, fun b => κ (c b) w / κ (c a) w, ⟨div_self hca, fun b => ?_⟩, ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ (ha b) (norm_nonneg _)
  · intro i
    have : ∑ b, κ (c b) w / κ (c a) w * κ (X b i) w = (κ (c a) w)⁻¹ * ∑ b, κ (c b) w * κ (X b i) w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hsum i, mul_zero, norm_zero]
    exact hε

theorem boxK_goodK_topology : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro K W _ _ _ κ hκ n M
  refine ⟨fun r => isCompact_boxK κ hκ r, isOpen_linIndep κ hκ n M, fun R ε hε => ⟨?_, goodK_subset κ R ε hε⟩⟩
  refine (isCompact_boxK κ hκ _).diff ?_
  exact isOpen_iUnion fun w => isOpen_iUnion fun a => isOpen_iUnion fun s => isOpen_iUnion fun _ =>
    isOpen_nearK κ hκ w s ε

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependentStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_set_compact_linearly_independent : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowth
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem exists_mem_boxK_two_pow {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ}
    {R : ℝ} (hR : 0 < R) (X : Fin n → Fin M → K) :
    ∃ j : ℕ, X ∈ boxK κ (fun _ _ => (2 : ℝ) ^ j * R) := by
  set B : ℝ := ∑ a, ∑ i, ∑ w, ‖κ (X a i) w‖ with hB
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / R) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨j, fun a i w => ?_⟩
  have h1 : ‖κ (X a i) w‖ ≤ ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun w => ‖κ (X a i) w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have h2 : ∑ w, ‖κ (X a i) w‖ ≤ ∑ i, ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun i => ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ∑ i, ∑ w, ‖κ (X a i) w‖ ≤ B :=
    Finset.single_le_sum (f := fun a => ∑ i, ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h4 : B < (2 : ℝ) ^ j * R := (div_lt_iff₀ hR).1 hj
  linarith

theorem exists_large_ofReal_div_mul_le {A : ℝ} (hA : 0 ≤ A) {D ε : ℝ≥0∞} (hD : D ≠ ⊤) (hε : ε ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ENNReal.ofReal (A / R) * D ≤ ε := by
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hε)
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ A * D.toReal / δ := by positivity
  refine ⟨1 + A * D.toReal / δ, by linarith, ?_⟩
  have hRpos : 0 < 1 + A * D.toReal / δ := by linarith
  have hkey : A / (1 + A * D.toReal / δ) * D.toReal ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    have : (δ : ℝ) * (1 + A * D.toReal / δ) = δ + A * D.toReal := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ δ := hδ0'.le
    linarith
  calc ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * D
      = ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * ENNReal.ofReal D.toReal := by
        rw [ENNReal.ofReal_toReal hD]
    _ = ENNReal.ofReal (A / (1 + A * D.toReal / δ) * D.toReal) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal hkey
    _ = δ := ENNReal.ofReal_coe_nnreal
    _ ≤ ε := hδ.le

theorem tsum_geometric_half_mul (c d : ℝ≥0∞) :
    ∑' j : ℕ, c * (2⁻¹ : ℝ≥0∞) ^ j * d = c * 2 * d := by
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]

theorem shell_real_identity {c R : ℝ} (hR : 0 < R) (e j : ℕ) :
    c / ((2 : ℝ) ^ j * R) ^ (e + 1) * ((2 : ℝ) ^ (j + 1) * R) ^ e
      = c * 2 ^ e / R * (1 / 2) ^ j := by
  have h2 : (2 : ℝ) ^ (j + 1) * R = 2 * ((2 : ℝ) ^ j * R) := by ring
  have key : ∀ P : ℝ, P ≠ 0 → c / P ^ (e + 1) * (2 * P) ^ e = c * 2 ^ e / P := by
    intro P hP
    rw [mul_pow, pow_succ]
    field_simp
  rw [h2, key _ (by positivity), one_div, inv_pow]
  field_simp

theorem tail_small_of_density :
    ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  intro K W _ _ κ n M H _ _ μ ν q C₀ hC₀ hden hq hbox φ hφ ε hε
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 * (M - n) * Fintype.card W * n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := hφ (e + 1)
  have hA : 0 ≤ |C| * (2 : ℝ) ^ e := by positivity
  obtain ⟨R, hR1, hRε⟩ := exists_large_ofReal_div_mul_le hA
    (ENNReal.mul_ne_top (by simp) hC₀ : (2 : ℝ≥0∞) * C₀ ≠ ⊤) hε
  refine ⟨R, hR1, fun Y hY => ?_⟩
  have hR0 : 0 < R := by linarith
  let S : ℕ → Set (Fin n → Fin M → K) := fun j =>
    (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) \ boxK κ (fun _ _ => (2 : ℝ) ^ j * R)) ∩ q ⁻¹' Y
  have hcover : (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y ⊆ ⋃ j, S j := by
    rintro X ⟨hX, hXY⟩
    classical
    have hex := exists_mem_boxK_two_pow κ hR0 X
    have hne : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp only [pow_zero, one_mul] at this
      exact hX this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine Set.mem_iUnion.2 ⟨j, ⟨?_, ?_⟩, hXY⟩
    · have := Nat.find_spec hex
      rw [hj] at this
      exact this
    · exact Nat.find_min hex (by omega)
  have hshell : ∀ j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
      ≤ ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
    intro j
    have hRj : 1 ≤ (2 : ℝ) ^ j * R := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
      nlinarith
    have hRj0 : 0 < (2 : ℝ) ^ j * R := by linarith
    have hSm : MeasurableSet (S j) := ((hbox _).diff (hbox _)).inter (hq hY)
    have hpt : ∀ X ∈ S j, ‖φ X‖ₑ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) := by
      rintro X ⟨⟨-, hX⟩, -⟩
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((hC _ hRj X hX).trans ?_)
      exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    have hmu : μ (S j) ≤ C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y := by
      have h1 := hden (fun _ _ => (2 : ℝ) ^ (j + 1) * R) (fun _ _ => by positivity) Y hY
      have h2 : μ (S j) ≤ μ (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) ∩ q ⁻¹' Y) :=
        measure_mono fun X hX => ⟨hX.1.1, hX.2⟩
      have h3 : (∏ a : Fin n, ∏ w : W, ENNReal.ofReal ((2 : ℝ) ^ (j + 1) * R) ^ (2 * (M - n)))
          = ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) := by
        rw [ENNReal.ofReal_pow (by positivity), he]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [h3] at h1
      exact h2.trans h1
    calc ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in S j, ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) ∂μ :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) * μ (S j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            (C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y) := by gcongr
      _ = (ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e)) * (C₀ * ν Y) := by ring
      _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
          rw [← ENNReal.ofReal_mul (by positivity), shell_real_identity hR0,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          congr 3
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  calc ∫⁻ X in (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ⋃ j, S j, ‖φ X‖ₑ ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) :=
        ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * 2 * (C₀ * ν Y) := tsum_geometric_half_mul _ _
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2 * C₀) * ν Y := by ring
    _ ≤ ε * ν Y := by gcongr

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowthStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_box_radius_tail_lintegral_le_eps_mul : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasure
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

section Gen

variable {H : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_scale (ν : Measure H) [ν.IsAddHaarMeasure] (e : H ≃ₜ+ H) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ν.map e = c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  exact ⟨Measure.addHaarScalarFactor (ν.map e) ν,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem map_eq_of_sq_conj (ν : Measure H) [ν.IsAddHaarMeasure] (A B D : H ≃ₜ+ H)
    (h1 : ∀ x, B x = A (A x)) (h2 : ∀ x, B (D x) = D (A x)) : ν.map A = ν := by
  obtain ⟨c, hc0, hc⟩ := exists_scale ν A
  obtain ⟨d, hd0, hd⟩ := exists_scale ν D
  obtain ⟨b, -, hb⟩ := exists_scale ν B
  have mA : Measurable A := A.continuous.measurable
  have mB : Measurable B := B.continuous.measurable
  have mD : Measurable D := D.continuous.measurable
  have e1 : b • ν = (c * c) • ν := by
    rw [← hb]
    have : (B : H → H) = A ∘ A := funext h1
    rw [this, ← Measure.map_map mA mA, hc, Measure.map_smul c mA.aemeasurable, hc, smul_smul]
  have e2 : (d * b) • ν = (c * d) • ν := by
    have h3 : (B : H → H) ∘ D = D ∘ A := funext h2
    have l : (ν.map D).map B = (d * b) • ν := by
      rw [hd, Measure.map_smul d mB.aemeasurable, hb, smul_smul]
    have r : (ν.map A).map D = (c * d) • ν := by
      rw [hc, Measure.map_smul c mD.aemeasurable, hd, smul_smul]
    rw [← l, ← r, Measure.map_map mB mD, Measure.map_map mD mA, h3]
  obtain ⟨Kc, hK, hKn⟩ := exists_compact_mem_nhds (0 : H)
  have hpos : ν Kc ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have htop : ν Kc ≠ ⊤ := hK.measure_lt_top.ne
  have cancel : ∀ u v : ℝ≥0, u • ν = v • ν → u = v := by
    intro u v h
    have := congrArg (fun m : Measure H => m Kc) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 this
  have hb' := cancel _ _ e1
  have hcd := cancel _ _ e2
  have hc1 : c = 1 := by
    rw [hb'] at hcd
    have : (c * d) * c = (c * d) * 1 := by
      calc (c * d) * c = d * (c * c) := by ring
        _ = c * d := hcd
        _ = (c * d) * 1 := (mul_one _).symm
    exact mul_left_cancel₀ (mul_ne_zero hc0 hd0) this
  rw [hc, hc1, one_smul]

end Gen

section Mat

open HeckeCharacterZeroLocus.SiegelWeilU (cT)

variable {K : Type} [CommRing K] (s : K →+* K) {n : ℕ}

theorem cT_one : cT s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem conj_conj (g h S : Matrix (Fin n) (Fin n) K) :
    cT s h * (cT s g * S * g) * h = cT s (g * h) * S * (g * h) := by
  rw [HeckeCharacterZeroLocus.SiegelWeilU.cT_mul]
  simp only [Matrix.mul_assoc]

theorem shearM_zero (a : Fin n) : shearM a (0 : Fin n → K) = 1 := by
  ext i j
  simp [shearM]

theorem shearM_mul (a : Fin n) (x y : Fin n → K) (hy : y a = 0) :
    shearM a x * shearM a y = shearM a (x + y) := by
  have hN : (Matrix.of (fun b c => if c = a then x b else 0) *
      Matrix.of (fun b c => if c = a then y b else 0) : Matrix (Fin n) (Fin n) K) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = a
    · subst hk
      by_cases hj : j = k <;> simp [hj, hy]
    · simp [hk]
  rw [shearM, shearM, shearM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hN, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, add_zero]
  ext i j
  by_cases hj : j = a
  · simp [hj]
    ring
  · simp [hj]

def diagAt (a : Fin n) (t : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun i => if i = a then t else 1

theorem diagAt_mul (a : Fin n) (t u : K) (h : t * u = 1) : diagAt a t * diagAt a u = 1 := by
  rw [diagAt, diagAt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = a <;> simp [hi, h]

theorem diagAt_shearM (a : Fin n) (x : Fin n → K) (hx : x a = 0) :
    diagAt a 2 * shearM a (x + x) = shearM a x * diagAt a 2 := by
  ext i j
  rw [diagAt, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [shearM, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  by_cases hj : j = a
  · subst hj
    by_cases hi : i = j
    · subst hi
      simp [hx]
    · simp [Matrix.one_apply, hi] <;> ring
  · by_cases hij : i = j
    · subst hij
      simp [hj]
    · rw [Matrix.one_apply_ne hij]
      simp [hj]

variable [TopologicalSpace K] [IsTopologicalRing K]

def conjEq (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cT s g * S * g ∈ H)
    (g g' : Matrix (Fin n) (Fin n) K) (h1 : g * g' = 1) (h2 : g' * g = 1) : H ≃ₜ+ H where
  toFun S := ⟨cT s g * S * g, hH _ S.2 g⟩
  invFun S := ⟨cT s g' * S * g', hH _ S.2 g'⟩
  left_inv S := Subtype.ext (by
    change cT s g' * (cT s g * (S : Matrix (Fin n) (Fin n) K) * g) * g' = S
    rw [conj_conj, h1, cT_one, Matrix.one_mul, Matrix.mul_one])
  right_inv S := Subtype.ext (by
    change cT s g * (cT s g' * (S : Matrix (Fin n) (Fin n) K) * g') * g = S
    rw [conj_conj, h2, cT_one, Matrix.one_mul, Matrix.mul_one])
  map_add' S T := Subtype.ext (by
    change cT s g * ((S : Matrix (Fin n) (Fin n) K) + T) * g = cT s g * S * g + cT s g * T * g
    rw [Matrix.mul_add, Matrix.add_mul])
  continuous_toFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

theorem conjEq_val (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cT s g * S * g ∈ H)
    (g g' : Matrix (Fin n) (Fin n) K) (h1 : g * g' = 1) (h2 : g' * g = 1) (S : H) :
    (conjEq s H hH g g' h1 h2 S : Matrix (Fin n) (Fin n) K) = cT s g * S * g := rfl

theorem map_shear (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cT s g * S * g ∈ H)
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsAddHaarMeasure] (h2 : IsUnit (2 : K)) (a : Fin n) (x : Fin n → K) (hx : x a = 0)
    (τ : H → H) (hτ : ∀ S, (τ S : Matrix (Fin n) (Fin n) K) = cT s (shearM a x) * S * shearM a x) :
    ν.map τ = ν := by
  have inv : ∀ y : Fin n → K, y a = 0 → shearM a y * shearM a (-y) = 1 ∧ shearM a (-y) * shearM a y = 1 := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [shearM_mul a _ _ (by simp [hy]), add_neg_cancel, shearM_zero]
    · rw [shearM_mul a _ _ hy, neg_add_cancel, shearM_zero]
  have hxx : (x + x) a = 0 := by simp [hx]
  obtain ⟨i1, i2⟩ := inv x hx
  obtain ⟨j1, j2⟩ := inv (x + x) hxx
  have d1 : diagAt a (2 : K) * diagAt a ((h2.unit⁻¹ : Kˣ) : K) = 1 :=
    diagAt_mul a _ _ (h2.mul_val_inv)
  have d2 : diagAt a ((h2.unit⁻¹ : Kˣ) : K) * diagAt a (2 : K) = 1 :=
    diagAt_mul a _ _ (h2.val_inv_mul)
  have hτe : τ = conjEq s H hH _ _ i1 i2 := funext fun S => Subtype.ext (hτ S)
  rw [hτe]
  refine map_eq_of_sq_conj ν _ (conjEq s H hH _ _ j1 j2) (conjEq s H hH _ _ d1 d2) ?_ ?_
  · intro S
    apply Subtype.ext
    rw [conjEq_val, conjEq_val, conjEq_val, conj_conj, shearM_mul a _ _ hx]
  · intro S
    apply Subtype.ext
    rw [conjEq_val, conjEq_val, conjEq_val, conjEq_val, conj_conj, conj_conj, diagAt_shearM a x hx]

end Mat

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

theorem coordHerm_map_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) * S * GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam a s hs τ _ hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hH n
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  have hinv : ∀ x : Ainf F ⊗[F] E, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ x) = x :=
    GlobalTheory.CompanionTheory.SW.GramAlg.sigR_invol (Ainf F) (GlobalTheory.CompanionTheory.SW.GramAlg.sigma_invol hσ)
  have hmem : ∀ S ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, ∀ g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n := by
    intro S hS g
    have hS' : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) S = S := by
      ext i j
      exact hS i j
    have key : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ)
        (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g)
        = HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g := by
      rw [HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, GlobalTheory.CompanionTheory.SW.GramAlg.cT_cT _ hinv, hS', Matrix.mul_assoc]
    intro i j
    exact congrFun (congrFun key i) j
  have h2 : IsUnit (2 : Ainf F ⊗[F] E) := by
    have : IsUnit (algebraMap F (Ainf F ⊗[F] E) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
    rwa [map_ofNat] at this
  exact map_shear (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) hmem
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n) h2 a s hs τ hτ

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasureStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_pushforward_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) * S * GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosetsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosets
open MeasureTheory

namespace GlobalTheory.TwistedCosetSum

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem coset_integral [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X)
    [μ.IsAddLeftInvariant] (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (g : X → ℂ)
    (hg : ∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) (c : X) :
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = 0 ∨
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = g c * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  set S : Set X := (fun x => -c + x) ⁻¹' (U : Set X) with hS
  have hmem : ∀ y, y ∈ S ↔ -c + y ∈ U := fun y => Iff.rfl
  have hmeas : MeasurableSet S := (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : μ S = μ U := measure_preimage_add μ _ _
  by_cases h : ∀ u ∈ U, g (c + u) = g c
  · right
    have : S.indicator g = S.indicator (fun _ => g c) := by
      refine Set.indicator_congr fun y hy => ?_
      have := h _ ((hmem y).1 hy)
      rwa [add_neg_cancel_left] at this
    rw [this, integral_indicator_const _ hmeas]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · left
    push_neg at h
    obtain ⟨u, hu, hne⟩ := h
    have hc0 : g c ≠ 0 := by
      intro h0
      have := hg c u hu u hu
      rw [h0, mul_zero] at this
      exact hne (by rw [h0]; exact mul_self_eq_zero.1 this.symm)
    have hshift : ∀ y, S.indicator g (u + y) * g c = g (c + u) * S.indicator g y := by
      intro y
      have hiff : u + y ∈ S ↔ y ∈ S := by
        rw [hmem, hmem, add_left_comm]
        exact U.add_mem_cancel_left hu
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.2 hy)]
        have := hg c u hu _ ((hmem y).1 hy)
        rw [add_neg_cancel_left, show c + u + (-c + y) = u + y by abel] at this
        exact this
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hiff.1 h)), zero_mul, mul_zero]
    have h1 : (∫ y, S.indicator g y ∂μ) * g c = g (c + u) * ∫ y, S.indicator g y ∂μ := by
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (S.indicator g) u]
      rw [← integral_mul_const, ← integral_const_mul]
      simp only [hshift]
    have h2 : (g (c + u) - g c) * ∫ y, S.indicator g y ∂μ = 0 := by
      rw [sub_mul, ← h1]; ring
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

theorem integral_eq_sum_twisted : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  intro X _ _ _ _ _ _ μ _ U hU _ g hc hg
  classical
  by_cases hint : Integrable g μ
  swap
  · exact ⟨∅, by rw [integral_undef hint]; simp⟩
  haveI := GlobalTheory.LCIntegralField.discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        g y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y).2 h)]
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hsum : ∫ y, g y ∂μ = ∑ c ∈ T, ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ := by
    rw [← integral_finsetSum _ fun c _ => hint.indicator (hmeas c)]
    exact congrArg _ hdec
  refine ⟨(T.filter fun c => ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ ≠ 0).image
    Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h), hsum, ← Finset.sum_filter_ne_zero,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact (coset_integral μ U hU g hg (Quotient.out c)).resolve_left (Finset.mem_filter.1 hc).2

end GlobalTheory.TwistedCosetSum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_volume_sum_characterTwistedCosets : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted | exact GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted | (intros; apply GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stairElt_diag (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (e : ℕ) (J : G.Level) (X : ℕ × ℕ) :
    ∃ n : Fin (G.rank X) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X =
        diagGL fun a => ϖ ^ n a := by
  have h1 : ∀ Y : ℕ × ℕ, ∃ n : Fin (G.rank Y) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (1 : GL (Fin (G.rank Y)) k) = diagGL fun a => ϖ ^ n a := fun Y =>
    ⟨fun _ => 0, fun _ => Nat.zero_le _, Units.ext (by simp)⟩
  have h2 : ∀ j : ℕ, ∃ n : Fin (G.rank (G.m, j)) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      stair G ϖ e j = diagGL fun a => ϖ ^ n a := fun j =>
    ⟨fun a => e * (a.val + 1 - topRank G j), fun a => Nat.mul_le_mul_left _ (by
      have := topRank_add hs j; have := a.2; omega), rfl⟩
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]; exact h2 j
    · rw [Reps.elt, onColumn_apply]
      cases j with
      | zero => exact h2 0
      | succ j =>
        have : ¬ j < G.m - 2 := by omega
        simp only [dif_neg this]
        exact h1 _
  · rw [Reps.elt, onColumn, dif_neg hi]
    exact h1 _

theorem valuation_fill_sub_le (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (n : ℕ) (x : ColArgs G) (y : RowArgs G)
    (v l : Vars G) (hl : l ∈ varLat G ϖ n) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    valuation k ((fill hs x y (v + l) - fill hs x y v) b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ <;> simp only [Pi.sub_apply, Matrix.sub_apply, fill] <;> split_ifs
  · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, downMap]
    split_ifs with h
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, stepPt, Matrix.add_apply, Matrix.of_apply,
        add_sub_add_left_eq_sub]
      split_ifs
      · simp only [Pi.add_apply, add_sub_cancel_left]
        exact hl ⟨j, h⟩ _
      · simp
    · simp
    · simp
  all_goals simp

end

theorem moved_stair_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  intro k _ _ _ _ G hs ϖ hϖ e T hT J keep x y v l hl
  rcases Nat.eq_zero_or_pos G.m with hm | hm
  · have : l = 0 := funext fun j => absurd j.2 (by omega)
    rw [this, add_zero]
  have hd := stairElt_diag G hs ϖ e J
  generalize (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = g at hd ⊢
  have hf := valuation_fill_sub_le G hs ϖ _ x y v l hl
  have hsum : G.moveArgs .one g (fill hs x y (v + l)) =
      G.moveArgs .one g (fill hs x y v) + G.moveArgs .one g (fill hs x y (v + l) - fill hs x y v) := by
    funext b
    simp only [Grid.moveArgs, Pi.add_apply, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
  simp only [moved, Grid.pathAct]
  rw [hsum, hT.2.2]
  intro b r
  generalize fill hs x y (v + l) - fill hs x y v = d at hf
  obtain ⟨n, -, hn⟩ := hd b.tgt
  obtain ⟨n', hn1, hn'⟩ := hd b.src
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  rw [SplitFlip.stdLat, smul_diagLat, mem_diagLat]
  intro s
  have hv : (G.moveArgs .one g d b).row r s = (ϖ : k) ^ n r * d b r s * ((ϖ : k) ^ n' s)⁻¹ := by
    have hinv : ((diagGL fun a => ϖ ^ n' a : GL (Fin (G.rank b.src)) k)⁻¹).val =
        Matrix.diagonal fun a => ((ϖ : k) ^ n' a)⁻¹ := by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_right_inv ?_
      simp [Matrix.diagonal_mul_diagonal]
    simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, hn, hn', hinv, diagGL_val,
      Matrix.diagonal_transpose, Matrix.row, Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_pow_eq_pow_val]
  have h2 := hf b r s
  rw [hv]
  simp only [map_mul, map_inv₀, map_pow, Units.val_pow_eq_pow_val, Pi.one_apply, mul_one] at h2 ⊢
  rw [mul_inv_le_iff₀ (pow_pos h0 _), ← pow_add]
  refine (mul_le_of_le_one_left' (pow_le_one' h1 _)).trans (h2.trans (pow_le_pow_right_of_le_one' h1 ?_))
  have := hn1 s
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le' hm
  rw [hm'] at this ⊢
  simp only [Nat.succ_eq_add_one, zero_add, Nat.add_sub_cancel] at this ⊢
  nlinarith

end GlobalTheory.UnfoldLoss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedStaircaseTensor_periodic_uniformizerPow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  first | exact @GlobalTheory.UnfoldLoss.moved_stair_periodic | exact GlobalTheory.UnfoldLoss.moved_stair_periodic | (intros; apply GlobalTheory.UnfoldLoss.moved_stair_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegUnfoldingPhaseMulUniformizerPowLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegUnfoldingPhaseMulUniformizerPowLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss.PhaseQuad

open GlobalTheory.RootEx

section General
variable {V k : Type*} [AddCommGroup V] [CommRing k] (O : Subring k) (S : Set V)

def Aff (f : V → k) : Prop := ∃ a : V → k, (∀ v l, f (v + l) = f v + a l) ∧ ∀ l ∈ S, a l ∈ O

def Quad (f : V → k) : Prop := ∀ v, ∀ l ∈ S, ∀ l' ∈ S, f (v + l + l') + f v - (f (v + l) + f (v + l')) ∈ O

variable {O S}

theorem Aff.const (c : k) : Aff O S fun _ => c := ⟨fun _ => 0, by simp, fun _ _ => zero_mem _⟩

theorem Aff.sum {ι : Type*} (s : Finset ι) {f : ι → V → k} (h : ∀ i, Aff O S (f i)) :
    Aff O S fun v => ∑ i ∈ s, f i v := by
  choose a ha hO using h
  exact ⟨fun l => ∑ i ∈ s, a i l, fun v l => by simp only [ha, Finset.sum_add_distrib],
    fun l hl => sum_mem fun i _ => hO i l hl⟩

theorem Aff.ite (p : Prop) [Decidable p] {f : V → k} (h : Aff O S f) : Aff O S fun v => if p then f v else 0 := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using Aff.const 0

theorem Aff.quad {f : V → k} (h : Aff O S f) : Quad O S f := by
  obtain ⟨a, ha, -⟩ := h
  intro v l _ l' _
  have : f (v + l + l') + f v - (f (v + l) + f (v + l')) = 0 := by
    rw [ha (v + l), ha v l']; ring
  rw [this]; exact zero_mem _

theorem Aff.mul {f g : V → k} (hf : Aff O S f) (hg : Aff O S g) : Quad O S fun v => f v * g v := by
  obtain ⟨a, ha, haO⟩ := hf
  obtain ⟨b, hb, hbO⟩ := hg
  intro v l hl l' hl'
  have : f (v + l + l') * g (v + l + l') + f v * g v - (f (v + l) * g (v + l) + f (v + l') * g (v + l')) =
      a l * b l' + a l' * b l := by
    rw [ha (v + l), ha v l', ha v l, hb (v + l), hb v l', hb v l]; ring
  show f (v + l + l') * g (v + l + l') + f v * g v - (f (v + l) * g (v + l) + f (v + l') * g (v + l')) ∈ O
  rw [this]
  exact add_mem (mul_mem (haO l hl) (hbO l' hl')) (mul_mem (haO l' hl') (hbO l hl))

theorem Quad.add {f g : V → k} (hf : Quad O S f) (hg : Quad O S g) : Quad O S fun v => f v + g v := by
  intro v l hl l' hl'
  convert add_mem (hf v l hl l' hl') (hg v l hl l' hl') using 1
  ring

theorem Quad.sum {ι : Type*} (s : Finset ι) {f : ι → V → k} (h : ∀ i, Quad O S (f i)) :
    Quad O S fun v => ∑ i ∈ s, f i v := by
  intro v l hl l' hl'
  convert sum_mem (t := s) fun i _ => h i v l hl l' hl' using 1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem Quad.ite (p : Prop) [Decidable p] {f : V → k} (h : Quad O S f) : Quad O S fun v => if p then f v else 0 := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using (Aff.const 0).quad

end General

section Phase
variable {k : Type*} [Field k] {G : Grid k} (O : Subring k)

def intVars (G : Grid k) : Set (Vars G) := {e | ∀ j r, e j r ∈ O}

theorem aff_stepPt (j : Fin (G.m - 1)) (x₀ : Matrix (Fin (topRank G (j + 1))) (Fin (topRank G j)) k) (r s) :
    Aff O (intVars O G) fun e : Vars G => stepPt x₀ (e j) r s := by
  by_cases h : Free ((G.m - 2 - j) / 2 + 1) (r, s) ∨ Kept (r, s)
  · refine ⟨fun l => l j ⟨(r, s), h⟩, fun v l => ?_, fun l hl => hl j _⟩
    simp only [stepPt, Matrix.add_apply, Matrix.of_apply, dif_pos h, Pi.add_apply, add_assoc]
  · refine ⟨fun _ => 0, fun v l => ?_, fun _ _ => zero_mem _⟩
    simp only [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]

theorem aff_rowVar (x : ColArgs G) (j : ℕ) (s) : Aff O (intVars O G) fun e : Vars G => rowVar x e j s := by
  by_cases h : j < G.m - 1
  · simp only [rowVar, dif_pos h]
    exact Aff.sum _ fun l => Aff.ite _ (aff_stepPt O ⟨j, h⟩ (x j) _ _)
  · simp only [rowVar, dif_neg h]
    exact Aff.const _

theorem quad_phase (x : ColArgs G) : Quad O (intVars O G) fun e : Vars G => phase x e := by
  unfold phase
  refine Quad.sum _ fun j => Quad.add ?_ (Quad.ite _ (Quad.sum _ fun r => ?_))
  · exact (Aff.sum _ fun i => aff_stepPt O j (x j) _ _).quad
  · exact (aff_rowVar O x _ r).mul (aff_stepPt O j (x j) _ _)

end Phase

theorem psi_phase_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k)
    (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (n : ℕ) (x : ColArgs G) (v l l' : Vars G),
    l ∈ varLat G ϖ n → l' ∈ varLat G ϖ n →
    (ψ (-phase x (v + l + l')) : ℂ) * (ψ (-phase x v) : ℂ) = (ψ (-phase x (v + l)) : ℂ) * (ψ (-phase x (v + l')) : ℂ) := by
  intro k _ _ _ _ G ψ hψ ϖ hϖ n x v l l' hl hl'
  have hint : ∀ e ∈ varLat G ϖ n, e ∈ intVars 𝒪[k] G := fun e he j r => by
    have h1 : valuation k ((ϖ ^ n : kˣ) : k) ≤ 1 := by
      rw [Units.val_pow_eq_pow_val]
      exact pow_mem hϖ.mem n
    exact (he j r).trans h1
  have hq := quad_phase 𝒪[k] x v l (hint l hl) l' (hint l' hl')
  have h1 : ψ (-(phase x (v + l + l') + phase x v - (phase x (v + l) + phase x (v + l')))) = 1 :=
    (hψ 1).2 le_rfl _ (by rw [Valuation.map_neg, map_one]; exact hq)
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  rw [← one_mul (ψ (-phase x (v + l) + -phase x (v + l'))), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  ring

end GlobalTheory.UnfoldLoss.PhaseQuad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegUnfoldingPhaseMulUniformizerPowLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_neg_unfoldingPhase_mul_uniformizerPowLattice : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k)
    (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (n : ℕ) (x : ColArgs G) (v l l' : Vars G),
    l ∈ varLat G ϖ n → l' ∈ varLat G ϖ n →
    (ψ (-phase x (v + l + l')) : ℂ) * (ψ (-phase x v) : ℂ) = (ψ (-phase x (v + l)) : ℂ) * (ψ (-phase x (v + l')) : ℂ) := by
  first | exact @GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul | exact GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul | (intros; apply GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigZetaIntegralEqSmulSmallZetaIntegralOfIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigZetaIntegralEqSmulSmallZetaIntegralOfIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section
namespace GlobalTheory.TopFlip.ZMatQ
open GlobalTheory.FlipMatch.ZMat

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem smallF_rows {A C C₁ : Type} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁] (eC : C ≃ C₁)
    (μ : Measure (GL A k)) [μ.IsHaarMeasure] (ν : kˣ →* ℂˣ)
    {g₀ : GL A k} (hg : g₀ ∈ KO k A) (c : Matrix C C k) (Ψ : Matrix A C₁ k → ℂ) (Y : Matrix A C k) :
      (ν (gdet g₀) : ℂ) * smallF μ ν (fun Y => Ψ (reindex (Equiv.refl _) eC (g₀.val * Y * c))) Y =
        smallF μ ν Ψ (reindex (Equiv.refl _) eC (Y * c)) := by
  unfold smallF
  rw [← Fintype.card_congr eC,
    ← integral_mul_left_eq_self (fun g : GL A k => Ψ (g.val * reindex (Equiv.refl _) eC (Y * c)) *
      (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2)) g₀, ← integral_const_mul]
  congr 1
  funext g
  have h2 : (g₀ * g).val * reindex (Equiv.refl _) eC (Y * c) =
      reindex (Equiv.refl _) eC (g₀.val * (g.val * Y) * c) := by
    have h5 : ∀ (M : Matrix A A k) (N : Matrix A C k),
        M * reindex (Equiv.refl _) eC N = reindex (Equiv.refl _) eC (M * N) := fun M N => by
      ext i j
      simp [Matrix.mul_apply]
    rw [h5]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [h2, gdet_mul, map_mul, Units.val_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg)]
  ring


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
theorem exists_reindex_unit_val {C C₁ : Type} [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁]
    (τ eC : C ≃ C₁) :
    ∃ s : kˣ, ValuativeRel.valuation k (s : k) = 1 ∧ ∀ u : GL C k, ∃ u₁ : GL C₁ k, u₁.val = reindex τ eC u.val ∧
      (invT u₁).val = reindex τ eC (invT u).val ∧ gdet u₁ = s * gdet u := by
  refine ⟨Units.map (Int.castRingHom k).toMonoidHom (Equiv.Perm.sign (eC.trans τ.symm)), ?_, fun u => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (eC.trans τ.symm)) with h | h <;> rw [h] <;> simp
  refine ⟨⟨reindex τ eC u.val, reindex eC τ (u⁻¹).val, ?_, ?_⟩, rfl, rfl, Units.ext ?_⟩
  · simp [submatrix_mul_equiv]
  · simp [submatrix_mul_equiv]
  · exact det_reindex τ eC u.val

end

theorem bigZeta_eq_smul_smallZeta_change : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C]
      (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eC : C ≃ C₁) (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a ⊕ A' ≃ C₁)
      (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) → gB ∈ KO k A' → c ∈ KO k C →
      ∃ x : kˣ, ValuativeRel.valuation k (x : k) = 1 ∧ ∀ (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Ξ : Matrix (Fin a) C₁ k → ℂ) (Ψ : Matrix A' C₁ k → ℂ),
        bigP (haarVol (KO k (Fin a))) ϖ σ₁ ν β Ξ = smallP (haarVol (KO k A')) σ₁ ν (ν * β) Ψ →
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (Equiv.refl _) eC (gA.val * X * (invT c).val))) =
          (ν x : ℂ) • smallP (haarVol (KO k A')) σ ν (ν * β) fun Y => Ψ (reindex (Equiv.refl _) eC (gB.val * Y * c.val)) := by
  intro k _ _ _ _ _ _ a A' _ _ C _ _ C₁ _ _ eC σ σ₁ gA gB c hA hB hC
  let τ : C ≃ C₁ := σ.symm.trans σ₁
  obtain ⟨s, hs1, hs⟩ := exists_reindex_unit_val (k := k) τ eC
  have vA := valuation_gdet_of_mem_KO hA
  have vB := valuation_gdet_of_mem_KO hB
  have vC := valuation_gdet_of_mem_KO hC
  have vs : ValuativeRel.valuation k ((s * gdet c : kˣ) : k) = 1 := by
    rw [Units.val_mul, map_mul, hs1, vC, mul_one]
  refine ⟨(gdet gA)⁻¹ * (s * gdet c) * gdet gB, ?_, fun ϖ ν β Ξ Ψ H => ?_⟩
  · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, vs, vB, Units.val_inv_eq_inv_val, map_inv₀, vA]
    simp
  have n1 : (ν (gdet gA) : ℂ) ≠ 0 := Units.ne_zero _
  have n2 : (ν (s * gdet c) : ℂ) ≠ 0 := Units.ne_zero _
  have n3 : (β (s * gdet c) : ℂ) ≠ 0 := Units.ne_zero _
  funext h
  obtain ⟨u, hu1, hu2, hu3⟩ := hs (h * c)
  have hd : gdet u = (s * gdet c) * gdet h := by rw [hu3, gdet_mul, mul_comm (gdet h), mul_assoc]
  have hX : reindex (Equiv.refl _) eC (X0 k σ * (invT (h * c)).val) = X0 k σ₁ * (invT u).val := by
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply, hu2]
    simp [frameMatrixFirstColumnBlock_mul_apply, τ]
  have hY : reindex (Equiv.refl _) eC (Y0 k σ * h.val * c.val) = Y0 k σ₁ * u.val := by
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply, hu1, Matrix.mul_assoc, ← Units.val_mul]
    simp only [reindex_apply, submatrix_apply, frameMatrixSecondColumnBlock_mul_apply]
    simp [τ]
  have H1 := congrFun H u
  have hF : (ν (gdet gA) : ℂ) * bigF (haarVol (KO k (Fin a))) ϖ ν
      (fun X => Ξ (reindex (Equiv.refl _) eC (gA.val * X * (invT c).val))) (X0 k σ * (invT h).val) =
      bigF (haarVol (KO k (Fin a))) ϖ ν Ξ (X0 k σ₁ * (invT u).val) := by
    unfold bigF
    rw [← shellSum_mul_left _ ϖ ν _ (fun g => Ξ (g * (X0 k σ₁ * (invT u).val))) hA, Fintype.card_congr eC, ← hX]
    congr 2
    funext g
    refine congrArg Ξ ?_
    have h5 : ∀ (M : Matrix (Fin a) (Fin a) k) (N : Matrix (Fin a) C k),
        M * reindex (Equiv.refl _) eC N = reindex (Equiv.refl _) eC (M * N) := fun M N => by
      ext i j
      simp [Matrix.mul_apply]
    simp only [h5, ← Matrix.mul_assoc gA.val g, map_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  have hG := smallF_rows eC (haarVol (KO k A')) ν hB c.val Ψ (Y0 k σ * h.val)
  rw [bigZetaIntegral_eq, smallP, ← hF, ← hY, hd, ← hG] at H1
  rw [Pi.smul_apply, smul_eq_mul, bigZetaIntegral_eq, smallP]
  simp only [map_mul _ (s * gdet c), apow_mul (s * gdet c), Units.val_mul, MonoidHom.mul_apply,
    apow_of_valuation_eq_one vs, map_mul ν _ (gdet gB), map_mul ν (gdet gA)⁻¹, map_inv,
    Units.val_inv_eq_inv_val] at H1 ⊢
  generalize (ν (s * gdet c) : ℂ) = x2 at *
  generalize (β (s * gdet c) : ℂ) = x3 at *
  refine mul_left_cancel₀ (mul_ne_zero n1 n3) ?_
  refine Eq.trans (by ring) (H1.trans ?_)
  field_simp

end GlobalTheory.TopFlip.ZMatQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigZetaIntegralEqSmulSmallZetaIntegralOfIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigZetaIntegral_eq_smul_smallZetaIntegral_of_integralChange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C]
      (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eC : C ≃ C₁) (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a ⊕ A' ≃ C₁)
      (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) → gB ∈ KO k A' → c ∈ KO k C →
      ∃ x : kˣ, ValuativeRel.valuation k (x : k) = 1 ∧ ∀ (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Ξ : Matrix (Fin a) C₁ k → ℂ) (Ψ : Matrix A' C₁ k → ℂ),
        bigP (haarVol (KO k (Fin a))) ϖ σ₁ ν β Ξ = smallP (haarVol (KO k A')) σ₁ ν (ν * β) Ψ →
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (Equiv.refl _) eC (gA.val * X * (invT c).val))) =
          (ν x : ℂ) • smallP (haarVol (KO k A')) σ ν (ν * β) fun Y => Ψ (reindex (Equiv.refl _) eC (gB.val * Y * c.val)) := by
  first | exact @GlobalTheory.TopFlip.ZMatQ.bigZeta_eq_smul_smallZeta_change | exact GlobalTheory.TopFlip.ZMatQ.bigZeta_eq_smul_smallZeta_change | (intros; apply GlobalTheory.TopFlip.ZMatQ.bigZeta_eq_smul_smallZeta_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqSmulIntegralMatrixIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqSmulIntegralMatrixIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.MixVacSmall

open GlobalTheory.SmallDat GlobalTheory.SmallPlaces
open GlobalTheory.BigDat (atW)

theorem mem_latO_iff_at {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {w : Pl D.host.E} (he : IsIdemSum (atPl w 1) {w})
    (hw : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (x : WO S T) (hx : IsHalf (atPl w 1) x) :
    x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      ∀ a b, (((loc w βT)⁻¹).val * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW w) * (loc w βS).val :
        Matrix (Fin T.rank) (Fin S.rank) (Kw w)) a b ∈ (ValuativeRel.valuation (Kw w)).integer := by
  classical
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} _ he (by simpa using hw) _ hx]
  have hmap : ∀ Q, (frMapO S T βS βT x).map (cpt (D := D) Q) =
      ((loc Q βT)⁻¹).val * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW Q) * (loc Q βS).val := by
    intro Q
    rw [← map_inv]
    unfold frMapO
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold IsIntM
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := (mem_OA_iff _).1 (h a b) w
    rw [← hmap, Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]
    exact this
  · refine (mem_OA_iff _).2 fun Q => ?_
    by_cases hQ : Q = w
    · subst hQ
      have := h a b
      rw [← hmap, Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one] at this
      exact this
    · have h0 : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW Q) = 0 := by
        refine Matrix.ext fun a b => ?_
        calc atW Q (x a b) = atW Q (atPl w 1 * x a b) := congrArg _ (hx a b).symm
          _ = 0 := by rw [map_mul, GlobalTheory.BigDat.atW_atPl_ne hQ, zero_mul]
      have h1 := congrFun (congrFun (hmap Q) a) b
      rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_apply, Matrix.zero_apply] at h1
      rw [h1]
      exact zero_mem _

theorem forall_cast_transpose {K : Type} {m m' n n' : ℕ} (hm : m' = m) (hn : n' = n) (A : Matrix (Fin m) (Fin n) K)
    (p : K → Prop) : (∀ r s, p ((A.submatrix (Fin.cast hm) (Fin.cast hn))ᵀ r s)) ↔ ∀ a b, p (A a b) := by
  subst hm hn
  exact forall_comm

theorem mem_latPtS_iff {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (B : Frames G) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (e : Num G i j) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    {x : PtS G i j} (hx : x ∈ mixHalfS e (atPl w 1)) (hat : At (evFin D.host.F (w.under (𝓞 D.host.F))) x) :
    x ∈ latPtS t e (w.under (𝓞 D.host.F)) ↔ ∀ r s, mixCoS B t e w x r s ∈ (ValuativeRel.valuation (Kw w)).integer := by
  classical
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  have h1 : Formalism.L2.NTheta.IsIdemAt (atPl w 1) w := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w hw) ▸ hes w hw
  have he : IsIdemSum (atPl w 1) {w} :=
    ⟨⟨fun _ => atPl w 1, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact h1, by simp⟩, h1.1.2.1⟩
  have hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hst.2 w hw (by
    have := Ideal.mul_mem_left _ ((D.host.d : ℕ) : 𝓞 D.host.E) h
    convert this using 1
    push_cast
    ring)
  have sW : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) :=
    (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have sV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sV₁ : IsSelfDualC (negSp (spV₁ G i j)) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have kA := mem_latO_iff_at sW sV (B.isFrame_β hL i.2.le j.2.le) (B.isFrame_β hL i.2.le j.2) he hb (mapA t e x) hx.1
  have kB := mem_latO_iff_at sV₁ sW (B.isFrame_β hL i.2 j.2.le) (B.isFrame_β hL i.2.le j.2.le) he hb (mapB e x) hx.2
  have cA := forall_cast_transpose (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩)
    (rank_vertex G t w (X := (i, j)) ⟨i.2.le, j.2.le⟩)
    (((loc w (B.β i (j + 1)))⁻¹).val * (mapA t e x).map (atW w) * (loc w (B.β i j)).val)
    (· ∈ (ValuativeRel.valuation (Kw w)).integer)
  have cB := forall_cast_transpose (rank_vertex G t w (X := (i, j)) ⟨i.2.le, j.2.le⟩)
    (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩)
    (((loc w (B.β i j))⁻¹).val * (mapB e x).map (atW w) * (loc w (B.β (i + 1) j)).val)
    (· ∈ (ValuativeRel.valuation (Kw w)).integer)
  rw [mixCoS_eq]
  refine ⟨fun h r s => ?_, fun h => ⟨hat, kA.2 (cA.1 fun r s => h r (.inl s)), kB.2 (cB.1 fun r s => h s (.inr r))⟩⟩
  rcases s with s | s
  · exact cA.2 (kA.1 h.2.1) r s
  · exact cB.2 (kB.1 h.2.2) s r

theorem mixVac_eq_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToB G t i j w, IsMixModelB W B t e Γ w ι →
      ι (Γ.M'.vac _) = ι (Γ.M'.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti w hw I hI
  classical
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  obtain ⟨hid, -⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := halves_split hL W t i j e Γ h.JW₁ h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := mixCoS_spec B t i j e w
  have hv := lagr_vac hI (hG.vac _).1 (hG.vac _).2.1 (latPtS t e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (latPtS_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) hco.2.1 hh.2.2.2.1
  funext Z
  obtain ⟨x, hx, rfl⟩ := hco.2.1 Z
  have k := mem_latPtS_iff hL B t i j hst e hw hx (hh.1 x hx)
  refine (hv.2 x hx).trans ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hl : x ∈ latPtS t e (w.under (𝓞 D.host.F))
  · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (s := {Z : MatB G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer})
      (a := mixCoS B t e w x) (k.1 hl), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (s := {Z : MatB G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer})
      (a := mixCoS B t e w x) (fun h' => hl (k.2 h')), mul_zero]

end GlobalTheory.TopFlip.MixVacSmall

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqSmulIntegralMatrixIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_vacuum_eq_smul_integralMatrix_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToB G t i j w, IsMixModelB W B t e Γ w ι →
      ι (Γ.M'.vac _) = ι (Γ.M'.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  first | exact @GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator | exact GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator | (intros; apply GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedChartThroughWCoordinate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedChartThroughWCoordinate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChartA

open GlobalTheory.FlipMatch.RowChart GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

theorem tr_full {k : Type} [Field k] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {b β g : GL (Fin n) k}
    {Gm : Matrix (Fin n) (Fin n) k} (hg : g.val = -(β.valᵀ * Gmᵀ * b.val))
    {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k} (hC : c.val * cc.val = blk e βV.val (-β₁.val))
    (U : Matrix (Fin n) (Fin d) k) :
    g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (blk e (βV⁻¹).val (-(β₁⁻¹).val) * (Uᵀ * -Gm) * β.val)ᵀ := by
  have h : g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (-(β.valᵀ * Gmᵀ) * U) * blk e (βV⁻¹).valᵀ (-(β₁⁻¹).valᵀ) := by
    rw [← inv_of_blk e hC, invT_val, hg]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val, Units.mul_inv, Matrix.one_mul]
  rw [h]
  simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose]

theorem map_frame {A R k : Type} [CommRing A] [CommRing R] [Field k] (f : A →+* R) (c : R →+* k) {n p q d : ℕ}
    (e : Fin p ⊕ Fin q ≃ Fin d) (β : GL (Fin n) R) (βV : GL (Fin p) R) (β₁ : GL (Fin q) R)
    (J : Matrix (Fin n) (Fin n) A) (u : Matrix (Fin n) (Fin d) A) :
    (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val *
        (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id * J).map f * β.val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val) *
        ((u.map (c.comp f))ᵀ * J.map (c.comp f)) * (GeneralLinearGroup.map c β).val).submatrix
        (e.symm.trans finSumFinEquiv).symm id := by
  have h1 : (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val)).submatrix
        (e.symm.trans finSumFinEquiv).symm (e.symm.trans finSumFinEquiv).symm := by
    have h0 : ((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val =
        GlobalTheory.Doubling.blkMat finSumFinEquiv (βV⁻¹).val (-(β₁⁻¹).val) := rfl
    rw [h0, GlobalTheory.Doubling.blkMat_map _ _ (map_zero c), Matrix.map_neg _ (map_neg c)]
    ext a b
    simp only [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, submatrix_apply, reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
    rfl
  rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.map_mul, Matrix.map_mul]
  have h2 : ((uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id).map f).map c * (J.map f).map c =
      ((u.map (c.comp f))ᵀ * J.map (c.comp f)).submatrix (e.symm.trans finSumFinEquiv).symm id := rfl
  rw [h2, submatrix_mul_equiv]
  rfl

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
  (i j : Fin D.R.m) (e : Num G i j)

theorem linA_ptA (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linA B t i j w (ptA e u) = reindex (finCongr (rankW G t i j w)) (colsEq t e w)
      (blk e ((loc w (B.β i (j + 1)))⁻¹).val (-((loc w (B.β (i + 1) j))⁻¹).val) *
        HMul.hMul (u.map (cw w))ᵀ (-(spW G i j).gram.map (algebraMap D.host.E (Kw w))) *
        (loc w (B.β (i + 1) (j + 1))).val)ᵀ := by
  have eJ : (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram).map (cw w) =
      -(spW G i j).gram.map (algebraMap D.host.E (Kw w)) :=
    Matrix.ext fun a b => (Good.cpt_incA _ _).trans (map_neg (algebraMap D.host.E (Kw w)) _)
  have k2 := map_frame (toEAf D) (cpt (D := D) w) (n := (spW G i j).rank) e (B.β (i + 1) (j + 1)) (B.β i (j + 1))
    (B.β (i + 1) j) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) u
  rw [← eJ]
  refine Matrix.ext fun r s => ?_
  refine (congrFun (congrFun k2 ((colX G t i j w).symm s)) ((finCongr (rankW G t i j w)).symm r)).trans ?_
  have hs : (e.symm.trans finSumFinEquiv).symm ((colX G t i j w).symm s) = (colsEq t e w).symm s :=
    congrArg e (finSumFinEquiv.symm_apply_apply _)
  rw [submatrix_apply, hs]
  rfl

theorem chart_eq_linA (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) {v : Pl D.host.F}
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (ψ : Fv D.host.F v ≃+* Kw w) (hjj : IsPlaceIso τ w ψ)
    (cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w))
    (hcc : (Γ.W.bas v).val.map ψ * cc.val = basCols B e w) (g : GL (Fin (spW G i j).rank) (Kw w))
    (hg : g.val = -((loc w (B.β (i + 1) (j + 1))).valᵀ *
      ((spW G i j).gram.map (algebraMap D.host.E (Kw w)))ᵀ * (Γ.V.bas v).val.map ψ))
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    chart ψ (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX τ (Γ.V.bas v) (Γ.W.bas v) u) =
      linA B t i j w (ptA e u) := by
  have eU : (u.map (piW τ)).map ψ = u.map (cw w) := Matrix.ext fun a b => hjj _
  have k1 := tr_full e (b := GeneralLinearGroup.map ψ.toRingHom (Γ.V.bas v))
    (c := GeneralLinearGroup.map ψ.toRingHom (Γ.W.bas v)) (β := loc w (B.β (i + 1) (j + 1)))
    (βV := loc w (B.β i (j + 1))) (β₁ := loc w (B.β (i + 1) j)) hg hcc (u.map (cw w))
  rw [linA_ptA, chart, chart_coX, eU]
  exact congrArg _ k1

end Grid

theorem exists_mixChart_lin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ ∧
      ∀ u, chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u) =
        linA B t i j w (ptA e u) := by
  classical
  intro D T L sc G μ₀ hL W B t i j M _ e Bs Γ X om om' h hT hTi v w hw jj hjj _ cc hcc
  subst hw
  obtain rfl := eq_complEquiv _ hjj
  have hV := hT.geo.hV
  have hJT : IsHermND D.sp.cm.sig Γ.V.Jᵀ := ⟨fun i j => by simpa using hV.herm j i, by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm _ Bs hV⟩
  have hsd := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose _ _ _ Bs _ Γ.V _ _ hT.base hV v
  have hb := hV.bas v
  rw [hTi.1] at hsd hb
  obtain ⟨g, hgK, hg⟩ := exists_rows (Bs.τ v) hJT hsd hb
    (isFrameAt_loc (B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2) (splitPrime (Bs.τ v)))
  have hJW : Γ.V.J = (spW G i j).gram := h.JW.trans (one_smul _ _)
  rw [hJW] at hg
  refine ⟨g, hgK, isMixChart_of B t i j e Γ (Bs.τ v) _ hjj (complMap_apply_emb _ _) hJW h.JWW cc hcc g hg, fun u => ?_⟩
  exact chart_eq_linA B t i j e Γ (Bs.τ v) _ _ hjj cc hcc g hg u

end GlobalTheory.TopFlip.ChartA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedChartThroughWCoordinateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixed_chart_through_W_coordinate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ ∧
      ∀ u, chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u) =
        linA B t i j w (ptA e u) := by
  first | exact @GlobalTheory.TopFlip.ChartA.exists_mixChart_lin | exact GlobalTheory.TopFlip.ChartA.exists_mixChart_lin | (intros; apply GlobalTheory.TopFlip.ChartA.exists_mixChart_lin <;> assumption)
end
end

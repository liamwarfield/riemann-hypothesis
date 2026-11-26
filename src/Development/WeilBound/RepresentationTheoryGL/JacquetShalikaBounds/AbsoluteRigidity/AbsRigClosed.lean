module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.LandauIteratedDerivatives.LandauL
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.EulerLogarithms.EulerProductLogBound
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantCharacterSplit.NormExponentEquality
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteCharacterNorms.UnitExponentHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantOneCharacters.DeterminantOneConditionHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.PrimeNonSummability.PrimeSumConvergesAndDiverges
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.ConjugateAnalyticity.RankinSelbergUnitaryOfPole
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.RigidityCriterion.JacquetShalikaRigidityOfBound

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteRigidityLemma.AbsoluteRigidityOfCommon
noncomputable section

namespace PositivityTheory.RgJS

namespace AbsoluteRigidity

variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}

theorem rel_symm {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) : Rel q A y x := fun w k => (h w k).symm

def sh (τ : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 - τ)

theorem rel_shift (hq : ∀ w, 2 ≤ q w) {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) (τ : ℝ) : Rel q A (sh τ ∘ x) (sh τ ∘ y) := by
  intro w k
  have hq0 : (q w : ℂ) ≠ 0 := by
    have := hq w
    exact_mod_cast (by omega : q w ≠ 0)
  have e : ∀ (a : ℂ) (t : ℝ), (a * (q w : ℂ) ^ (-((t - τ : ℝ) : ℂ))) ^ k =
      ((q w : ℂ) ^ (τ : ℂ)) ^ k * (a * (q w : ℂ) ^ (-(t : ℂ))) ^ k := by
    intro a t
    rw [← mul_pow]
    congr 1
    rw [show (q w : ℂ) ^ (τ : ℂ) * (a * (q w : ℂ) ^ (-(t : ℂ))) = a * ((q w : ℂ) ^ (τ : ℂ) * (q w : ℂ) ^ (-(t : ℂ))) by ring,
      ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
  have h1 := congrArg (fun z => ((q w : ℂ) ^ (τ : ℂ)) ^ k * z) (h w k)
  simp only [Finset.mul_sum] at h1
  simp only [Function.comp_apply, sh, e]
  exact h1

theorem rel_remove {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {x : ι → X × ℝ}
    {y : κ → X × ℝ} (h : Rel q A x y) (i : ι) (j : κ) (hij : x i = y j) :
    Rel q A (fun i' : {i' // i' ≠ i} => x i') (fun j' : {j' // j' ≠ j} => y j') := by
  intro w k
  have h1 := h w k
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ j, hij] at h1
  exact add_left_cancel h1

theorem exists_common (hC : Common0) (hS : Sys q X d A) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ) (h : Rel q A x y) (hne : Nonempty ι ∨ Nonempty κ) :
    ∃ i j, x i = y j := by
  classical
  set T : Finset ℝ := (Finset.univ.image fun i => (x i).2) ∪ (Finset.univ.image fun j => (y j).2) with hT
  have hTne : T.Nonempty := by
    rcases hne with ⟨⟨i⟩⟩ | ⟨⟨j⟩⟩
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    · exact ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
  set τ := T.min' hTne with hτ
  have hx : ∀ i, τ ≤ (x i).2 := fun i =>
    T.min'_le _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hy : ∀ j, τ ≤ (y j).2 := fun j =>
    T.min'_le _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hmem : τ ∈ T := T.min'_mem hTne
  have hsh := rel_shift hS.primes.two h τ
  have hinj : ∀ p p' : X × ℝ, sh τ p = sh τ p' → p = p' := fun p p' e => by
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [sh] at e1 e2
    exact Prod.ext e1 (by linarith)
  rcases Finset.mem_union.1 hmem with hm | hm
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm
    obtain ⟨i', j, e⟩ := hC W q X d A hS ι κ (sh τ ∘ x) (sh τ ∘ y) hsh
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      ⟨i, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i', j, hinj _ _ e⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hm
    obtain ⟨j', i, e⟩ := hC W q X d A hS κ ι (sh τ ∘ y) (sh τ ∘ x) (rel_symm hsh)
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      ⟨j, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i, j', (hinj _ _ e).symm⟩

theorem main (hC : Common0) (hS : Sys q X d A) : ∀ (N : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ), Fintype.card ι + Fintype.card κ ≤ N → Rel q A x y →
      ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
  intro N
  induction N with
  | zero =>
    intro ι κ _ _ x y hN _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by omega)
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 (by omega)
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
  | succ N ih =>
    intro ι κ _ _ x y hN h
    classical
    have step : Nonempty ι ∨ Nonempty κ → ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
      intro hne
      obtain ⟨i, j, hij⟩ := exists_common hC hS x y h hne
      have hr := rel_remove h i j hij
      have c1 : Fintype.card {i' // i' ≠ i} < Fintype.card ι := Fintype.card_subtype_lt (p := fun i' => i' ≠ i) (x := i) (by simp)
      have c2 : Fintype.card {j' // j' ≠ j} < Fintype.card κ := Fintype.card_subtype_lt (p := fun j' => j' ≠ j) (x := j) (by simp)
      obtain ⟨s', hs'⟩ := ih {i' // i' ≠ i} {j' // j' ≠ j} (fun i' => x i') (fun j' => y j') (by omega) hr
      refine ⟨(Equiv.optionSubtypeNe i).symm.trans ((Equiv.optionCongr s').trans (Equiv.optionSubtypeNe j)), fun i' => ?_⟩
      by_cases hi : i' = i
      · subst hi
        simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self, Equiv.optionCongr_apply, Option.map_none,
          Equiv.optionSubtypeNe_none]
        exact hij
      · simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi, Equiv.optionCongr_apply, Option.map_some,
          Equiv.optionSubtypeNe_some]
        exact hs' ⟨i', hi⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · rcases isEmpty_or_nonempty κ with hκ | hκ
      · exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
      · exact step (Or.inr hκ)
    · exact step (Or.inl hι)

end AbsoluteRigidity

theorem absolute_rigidity_of_common : Common0 → AbsRig := by
  intro hC W q X d A hS ι κ _ _ x y h
  exact AbsoluteRigidity.main hC hS _ ι κ x y le_rfl h

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SubtypeIteSums.CommonOfLandauEuler
noncomputable section

open scoped ComplexConjugate
open Finset

namespace PositivityTheory.RgJS.Common0Aux

variable {W X : Type} {d : X → ℕ}

def Pw (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (w : W) (k : ℕ) : ℂ :=
  ∑ i, ∑ a, (A (u i).1 w a * (q w : ℂ) ^ (-((u i).2 : ℂ))) ^ (k + 1)

theorem cpow_real (q : ℕ) (t : ℝ) : (q : ℂ) ^ (-(t : ℂ)) = (((q : ℝ) ^ (-t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, Complex.ofReal_neg]

theorem lterm_pair (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) {α β : Type} [Fintype α] [Fintype β] (a : W → α → ℂ)
    (b : W → β → ℂ) (σ t t' : ℝ) (p : W × ℕ) :
    lterm q a b (((σ + t + t' : ℝ)) : ℂ) p =
      (∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1)) *
        conj (∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1)) *
        ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by
  have hq0 : (q p.1 : ℂ) ≠ 0 := by
    have := hq p.1
    exact_mod_cast (by omega : q p.1 ≠ 0)
  unfold lterm
  have e : (q p.1 : ℂ) ^ (-(((σ + t + t' : ℝ)) : ℂ)) =
      (q p.1 : ℂ) ^ (-(σ : ℂ)) * (q p.1 : ℂ) ^ (-(t : ℂ)) * (q p.1 : ℂ) ^ (-(t' : ℂ)) := by
    rw [← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  have hr' : conj ((q p.1 : ℂ) ^ (-(t' : ℂ))) = (q p.1 : ℂ) ^ (-(t' : ℂ)) := by
    rw [cpow_real, Complex.conj_ofReal]
  have h1 : ∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1) =
      (∑ x, a p.1 x ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1) := by
    rw [Finset.sum_mul]
    simp only [mul_pow]
  have h2 : ∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1) =
      (∑ y, b p.1 y ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1) := by
    rw [Finset.sum_mul]
    simp only [mul_pow]
  rw [h1, h2, map_mul, map_pow, hr', e]
  ring

theorem sum_lterm (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : ι → X × ℝ) (v : κ → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (u i).1) (A (v j).1) (((σ + (u i).2 + (v j).2 : ℝ)) : ℂ) p =
      Pw q A u p.1 p.2 * conj (Pw q A v p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by
  simp only [lterm_pair q hq]
  unfold Pw
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.sum_div]

def cc (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (p : W × ℕ) : ℝ :=
  ‖Pw q A u p.1 p.2‖ ^ 2 / ((p.2 : ℝ) + 1)

def ll (q : W → ℕ) (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)

theorem cc_nonneg (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (p : W × ℕ) :
    0 ≤ cc q A u p := by
  unfold cc; positivity

theorem ll_nonneg (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (p : W × ℕ) : 0 ≤ ll q p := by
  unfold ll
  have h : (1 : ℝ) ≤ q p.1 := by exact_mod_cast (le_trans (by norm_num) (hq p.1))
  have := Real.log_nonneg h
  positivity

theorem term_real (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι]
    (u : ι → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    Pw q A u p.1 p.2 * conj (Pw q A u p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) =
      ((cc q A u p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have hqpos : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, cpow_real]
  have e : ((q p.1 : ℝ) ^ (-σ)) ^ (p.2 + 1) = Real.exp (-(ll q p * σ)) := by
    rw [← Real.rpow_mul_natCast hqpos.le, Real.rpow_def_of_pos hqpos]
    unfold ll
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_pow, e]
  unfold cc
  push_cast
  ring

theorem exists_pos_le {ι : Type} [Fintype ι] (f : ι → ℝ) (P : ι → Prop) (h : ∀ i, P i → 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i, P i → δ ≤ f i := by
  classical
  by_cases hs : (univ.filter P).Nonempty
  · refine ⟨min 1 ((univ.filter P).inf' hs f), lt_min one_pos ((Finset.lt_inf'_iff hs).2 fun j hj => h j ?_),
      min_le_left _ _, fun i hi => (min_le_right _ _).trans (Finset.inf'_le _ ?_)⟩
    · simpa using hj
    · simpa using hi
  · exact ⟨1, one_pos, le_rfl, fun i hi => absurd ⟨i, by simpa using hi⟩ hs⟩

theorem sum_subtype_ite {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ℂ) :
    ∑ i : {i // P i}, f i = ∑ i, if P i then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter P) (by simp) f).symm

theorem dsum_subtype {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ι → ℂ) :
    ∑ i : {i // P i}, ∑ j : {i // P i}, f i j = ∑ i, ∑ j, if P i ∧ P j then f i j else 0 := by
  rw [sum_subtype_ite P (fun i => ∑ j : {i // P i}, f i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : P i
  · simp [hi, sum_subtype_ite P (fun j => f i j)]
  · simp [hi]


open Classical in
def gf {ι κ : Type} (F : ι × κ → ℂ → ℂ) (x : ι → X × ℝ) (y : κ → X × ℝ) (p : ι × κ) (s : ℂ) : ℂ := by
  classical
  exact if (x p.1).1 = (y p.2).1 then F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) / (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1)
    else F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ))

end PositivityTheory.RgJS.Common0Aux

open PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux in
open PositivityTheory.RgJS.Common0Aux in
theorem PositivityTheory.RgJS.common_of_landau_euler : LandauL → EulerLog → Conv1 → Unb → Common0 := by
  classical
  intro hL hE hC hU W q X d A hS ι κ _ _ x y hR ht ht' h0
  by_contra hne
  push Not at hne
  have hq := hS.primes.two
  have hP : ∀ w k, Pw q A y w k = Pw q A x w k := fun w k => (hR w (k + 1)).symm
  have hxy : ∀ (σ : ℝ) (p : W × ℕ), ∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p =
      ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := fun σ p => by
    rw [sum_lterm q hq A x y σ p, hP, term_real q hq A x σ p]
  have hxx : ∀ (σ : ℝ) (p : W × ℕ), ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := fun σ p => by
    rw [sum_lterm q hq A x x σ p, term_real q hq A x σ p]
  have hsum : ∀ (u v : X) (s : ℝ), 1 < s → Summable fun p => ‖lterm q (A u) (A v) (s : ℂ) p‖ :=
    fun u v s hs => (hC W q X d A hS u v).1 s hs
  have hcn : ∀ (σ : ℝ) (p : W × ℕ), 0 ≤ cc q A x p * Real.exp (-(ll q p * σ)) := fun σ p =>
    mul_nonneg (cc_nonneg q A x p) (Real.exp_pos _).le

  have hD1 : ∀ σ : ℝ, 1 < σ → Summable fun p => cc q A x p * Real.exp (-(ll q p * σ)) := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (hcn σ) (fun p => ?_)
      (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ =>
        hsum (x i).1 (y j).1 (σ + (x i).2 + (y j).2) (by linarith [ht i, ht' j]))
    calc cc q A x p * Real.exp (-(ll q p * σ)) = ‖((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (hcn σ p)]
      _ = ‖∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p‖ := by rw [hxy]
      _ ≤ ∑ i, ∑ j, ‖lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)

  obtain ⟨δ, hδ, hδ1, hδle⟩ := exists_pos_le (fun p : ι × κ => (x p.1).2 + (y p.2).2)
    (fun p => (x p.1).1 = (y p.2).1) (by
      rintro ⟨i, j⟩ hij
      have h1 := ht i
      have h2 := ht' j
      rcases (add_nonneg h1 h2).lt_or_eq with h | h
      · exact h
      · exfalso
        have a1 : (x i).2 = 0 := by linarith
        have a2 : (y j).2 = 0 := by linarith
        exact hne i j (Prod.ext hij (by rw [a1, a2])))
  choose F σ0 hFa hFe using fun p : ι × κ => hS.rs (x p.1).1 (y p.2).1
  have hGa' : ∀ σ : ℝ, 1 - δ < σ → ∀ p : ι × κ, AnalyticAt ℂ (gf F x y p) σ := by
    intro σ hσ p
    have hpos : 0 < σ + ((x p.1).2 + (y p.2).2) := by linarith [ht p.1, ht' p.2]
    have hF' : AnalyticAt ℂ (fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ))) (σ : ℂ) := by
      have := hFa p (σ + ((x p.1).2 + (y p.2).2)) hpos
      have hlin : AnalyticAt ℂ (fun s : ℂ => s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) (σ : ℂ) :=
        analyticAt_id.add analyticAt_const
      exact AnalyticAt.comp_of_eq this hlin (by push_cast; ring)
    by_cases hc : (x p.1).1 = (y p.2).1
    · have hne1 : (σ : ℂ) + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1 ≠ 0 := by
        have h3 : 1 < σ + ((x p.1).2 + (y p.2).2) := by have := hδle p hc; linarith
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have : AnalyticAt ℂ (fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) /
          (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1)) (σ : ℂ) :=
        hF'.div ((analyticAt_id.add analyticAt_const).sub analyticAt_const) hne1
      have hgf : gf F x y p = fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) /
          (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1) := by
        funext s
        unfold gf
        rw [if_pos hc]
      rw [hgf]
      exact this
    · have hgf : gf F x y p = fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) := by
        funext s
        unfold gf
        rw [if_neg hc]
      rw [hgf]
      exact hF'
  have hGa : ∀ σ : ℝ, 1 - δ < σ → AnalyticAt ℂ (fun s => ∏ p, gf F x y p s) σ := by
    intro σ hσ
    have := Finset.analyticAt_prod (f := fun p => gf F x y p) Finset.univ (fun p _ => hGa' σ hσ p)
    rw [Finset.prod_fn] at this
    exact this
  set σ₁ : ℝ := 2 + ∑ p, |σ0 p| with hσ₁
  have hσ0le : ∀ p, σ0 p ≤ σ₁ - 2 := fun p => by
    have := Finset.single_le_sum (f := fun p => |σ0 p|) (fun p _ => abs_nonneg _) (Finset.mem_univ p)
    have := le_abs_self (σ0 p)
    simp only [hσ₁]
    linarith
  have hσ₁2 : 2 ≤ σ₁ := by
    have : 0 ≤ ∑ p, |σ0 p| := Finset.sum_nonneg fun p _ => abs_nonneg _
    simp only [hσ₁]
    linarith
  have hGe : ∀ σ : ℝ, σ₁ < σ → (fun s => ∏ p, gf F x y p s) σ =
      ((Real.exp (∑' p, cc q A x p * Real.exp (-(ll q p * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have hs' : ∀ p : ι × κ, Summable fun r => lterm q (A (x p.1).1) (A (y p.2).1) (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) r :=
      fun p => (hsum _ _ _ (by linarith [ht p.1, ht' p.2])).of_norm
    have hg : ∀ p : ι × κ, gf F x y p σ =
        Complex.exp (∑' r, lterm q (A (x p.1).1) (A (y p.2).1) (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) r) := by
      intro p
      have hs : σ0 p < σ + (x p.1).2 + (y p.2).2 := by linarith [hσ0le p, ht p.1, ht' p.2]
      have hs2 : 2 < ((((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ)).re := by
        rw [Complex.ofReal_re]
        linarith [ht p.1, ht' p.2]
      have hEL := (hE W q (Fin (d (x p.1).1)) (Fin (d (y p.2).1)) (A (x p.1).1) (A (y p.2).1) _ hS.primes
        (hS.bd _) (hS.bd _) hs2).2.1
      have hFE := hFe p _ hs
      have ecast : (σ : ℂ) + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) = (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) := by
        push_cast
        ring
      unfold gf
      rw [ecast]
      split_ifs with hc
      · have hne1 : ((((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ)) - 1 ≠ 0 := by
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith [ht p.1, ht' p.2]
        rw [hFE, if_pos hc, mul_div_cancel_left₀ _ hne1, hEL]
      · rw [hFE, if_neg hc, one_mul, hEL]
    show ∏ p, gf F x y p σ = _
    simp only [hg]
    rw [← Complex.exp_sum, ← Summable.tsum_finsetSum (fun p _ => hs' p)]
    simp only [Fintype.sum_prod_type]
    rw [show (fun r => ∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) r) =
      fun r => ((cc q A x r * Real.exp (-(ll q r * σ)) : ℝ) : ℂ) from funext (hxy σ)]
    rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp]
  have hL1 := hL (W × ℕ) (cc q A x) (ll q) (1 - δ) σ₁ (fun s => ∏ p, gf F x y p s) (cc_nonneg q A x) (ll_nonneg q hq)
    hGa (fun σ hσ => hD1 σ (by linarith)) hGe 1 (by linarith)

  obtain ⟨τ, hτ, -, hτle⟩ := exists_pos_le (fun i => (x i).2) (fun i => (x i).2 ≠ 0)
    (fun i hi => lt_of_le_of_ne (ht i) (Ne.symm hi))
  choose M hM using fun i i' : ι => (hC W q X d A hS (x i).1 (x i').1).2 (1 + τ) (by linarith)
  obtain ⟨i₀, hi₀⟩ := h0
  have : Nonempty {i // (x i).2 = 0} := ⟨⟨i₀, hi₀⟩⟩
  refine hU W q X d A hS {i // (x i).2 = 0} (fun i => (x i.1).1)
    ⟨(∑' p, cc q A x p * Real.exp (-(ll q p * 1))) + ∑ i, ∑ i', |M i i'|, fun σ hσ1 hσ2 => ?_⟩
  have hs : ∀ i j, Summable fun p => lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
    fun i j => (hsum _ _ _ (by linarith [ht i, ht j])).of_norm
  have hform : ∑ i : {i // (x i).2 = 0}, ∑ j : {i // (x i).2 = 0}, ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (σ : ℂ) p =
      ∑ i : {i // (x i).2 = 0}, ∑ j : {i // (x i).2 = 0},
        ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (((σ + (x i.1).2 + (x j.1).2 : ℝ)) : ℂ) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [i.2, j.2, add_zero, add_zero]
  have htot : ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
    calc ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p
        = ∑ i, ∑' p, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
      _ = ∑' p, ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          (Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j).symm
      _ = ∑' p, ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := tsum_congr fun p => hxx σ p
      _ = _ := (Complex.ofReal_tsum _).symm
  rw [hform, dsum_subtype (fun i => (x i).2 = 0)
    (fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p)]
  set f : ι → ι → ℂ := fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p with hf
  have hsplit : ∑ i, ∑ j, f i j = (∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then f i j else 0) +
      ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hrest : ‖∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then (0 : ℂ) else f i j‖ ≤ ∑ i, ∑ i', |M i i'| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    split_ifs with hij
    · simp
    · have hge : 1 + τ ≤ σ + (x i).2 + (x j).2 := by
        rcases not_and_or.1 hij with h | h
        · linarith [hτle i h, ht j]
        · linarith [hτle j h, ht i]
      exact (hM i j _ hge).trans (le_abs_self _)
  have hDle : (∑' p, cc q A x p * Real.exp (-(ll q p * σ))) ≤ ∑' p, cc q A x p * Real.exp (-(ll q p * 1)) := by
    refine Summable.tsum_le_tsum (fun p => ?_) (hD1 σ hσ1) hL1
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (cc_nonneg q A x p)
    have := ll_nonneg q hq p
    nlinarith
  have hD0 : 0 ≤ ∑' p, cc q A x p * Real.exp (-(ll q p * σ)) := tsum_nonneg (hcn σ)
  have heq : (∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then f i j else 0) =
      ((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) -
        ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j := by
    rw [← htot, hsplit]
    ring
  rw [heq]
  calc ‖((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) -
        ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j‖
      ≤ ‖((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)‖ +
        ‖∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then (0 : ℂ) else f i j‖ := norm_sub_le _ _
    _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hD0]
        linarith
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLowerBounds.NewtonIdentitiesLowDegree
noncomputable section

open MvPolynomial Finset

namespace PositivityTheory.RgJS.NewtonIdentitiesAlt

variable {A : Type} [Fintype A]

def ev (a : A → ℂ) (j : ℕ) : ℂ := ∑ t ∈ powersetCard j (univ : Finset A), ∏ i ∈ t, a i

theorem aeval_esymm (a : A → ℂ) (j : ℕ) : aeval a (esymm A ℂ j) = ev a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [esymm, ev, map_sum, map_prod]

theorem ev_zero (a : A → ℂ) : ev a 0 = 1 := by simp [ev]

theorem ev_card (a : A → ℂ) : ev a (Fintype.card A) = ∏ i, a i := by
  rw [ev, ← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]

theorem newton [DecidableEq A] (a : A → ℂ) (j : ℕ) :
    (j : ℂ) * ev a j = (-1) ^ (j + 1) *
      ∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2 := by
  have h := congrArg (aeval a) (MvPolynomial.mul_esymm_eq_sum A ℂ j)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_mul, map_sum, aeval_esymm, MvPolynomial.psum] using h

omit [Fintype A] in
theorem card_filter_lt (j : ℕ) : #{x ∈ antidiagonal j | x.1 < j} ≤ j := by
  calc #{x ∈ antidiagonal j | x.1 < j} ≤ #(range j) :=
        Finset.card_le_card_of_injOn Prod.fst
          (fun x hx => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
            simp only [Finset.coe_range, Set.mem_Iio]
            exact hx.2)
          (fun x hx y hy hxy => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
            have e1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
            have e2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hy.1
            exact Prod.ext hxy (by omega))
    _ = j := Finset.card_range j

theorem bound [DecidableEq A] (a : A → ℂ) (N : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ δ) : ∀ j, 1 ≤ j → j ≤ N → ‖ev a j‖ ≤ δ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj1 hjN
  have hev : ∀ m, m < j → ‖ev a m‖ ≤ 1 := fun m hm => by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [ev_zero]
      simp
    · exact (ih m hm h (by omega)).trans hδ
  have hsum : ‖∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ ≤ j * δ := by
    calc _ ≤ ∑ x ∈ antidiagonal j with x.1 < j, ‖(-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ antidiagonal j with x.1 < j, δ := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter] at hx
        have e1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        calc ‖ev a x.1‖ * ‖∑ i, a i ^ x.2‖ ≤ 1 * δ :=
              mul_le_mul (hev _ hx.2) (hp _ (by omega) (by omega)) (norm_nonneg _) zero_le_one
          _ = δ := one_mul δ
      _ = (#{x ∈ antidiagonal j | x.1 < j} : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ j * δ := by
        gcongr
        exact_mod_cast card_filter_lt j
  have h2 : (j : ℝ) * ‖ev a j‖ ≤ j * δ := by
    have h3 := congrArg norm (newton a j)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at h3
    rw [h3]
    exact hsum
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  exact le_of_mul_le_mul_left h2 hjpos

end PositivityTheory.RgJS.NewtonIdentitiesAlt

namespace PositivityTheory.RgJS

open NewtonIdentitiesAlt in
theorem newton_identities_low_degree : NewtonLow := by
  intro N hN
  refine ⟨1 / 4, by norm_num, fun A _ a hA hprod => ?_⟩
  classical
  by_contra hlt
  push_neg at hlt
  have hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ 1 / 2 := by
    intro k hk1 hkN
    by_contra hk
    push_neg at hk
    have hle : ‖∑ i, a i ^ k‖ ^ 2 ≤ ∑ m ∈ range N, ‖∑ i, a i ^ (m + 1)‖ ^ 2 := by
      have hmem : k - 1 ∈ range N := by
        rw [Finset.mem_range]
        omega
      have h4 := Finset.single_le_sum (f := fun m => ‖∑ i, a i ^ (m + 1)‖ ^ 2) (fun m _ => by positivity) hmem
      simpa [Nat.sub_add_cancel hk1] using h4
    nlinarith
  have h5 := bound a N (1 / 2) (by norm_num) (by norm_num) hp N hN le_rfl
  rw [← hA, ev_card, hprod] at h5
  norm_num at h5

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NonnegativeCoefficients.DirichletSeriesUnbounded
noncomputable section

open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace DirichletSeriesUnbounded₂

variable {W X : Type} (q : W → ℕ) {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (x : ι → X)

def PP (p : W × ℕ) : ℂ := ∑ i, ∑ a, A (x i) p.1 a ^ (p.2 + 1)

def cc (p : W × ℕ) : ℝ := ‖PP A x p‖ ^ 2 / ((p.2 : ℝ) + 1)

def ll (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)

theorem cc_nonneg (p : W × ℕ) : 0 ≤ cc A x p := by
  unfold cc; positivity

theorem cpow_pow (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) = ((Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have h1 : (q p.1 : ℂ) = ((q p.1 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (hq p.1).le, ← Complex.ofReal_pow, Real.rpow_def_of_pos (hq p.1),
    ← Real.exp_nat_mul]
  congr 2
  simp only [ll]
  push_cast
  ring

theorem sum_lterm (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((cc A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  set s : ι → ℂ := fun i => ∑ a, A (x i) p.1 a ^ (p.2 + 1) with hs
  set z : ℂ := ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / ((p.2 : ℂ) + 1) with hz
  have e1 : ∀ i j, lterm q (A (x i)) (A (x j)) σ p = s i * conj (s j) * z := by
    intro i j
    simp only [lterm, hs, hz]
    ring
  simp only [e1]
  have e2 : ∑ i, ∑ j, s i * conj (s j) * z = (∑ i, s i) * conj (∑ j, s j) * z := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, cpow_pow q hq σ p]
  simp only [cc, PP, hs]
  push_cast
  ring

end DirichletSeriesUnbounded₂

open DirichletSeriesUnbounded₂ in
theorem dirichlet_series_unbounded : LandauL → NewtonLow → EulerLog → Remov → Conv1 → Unb := by
  intro hL hN hE hR hC W q X d A hS ι _ _ x hMex
  obtain ⟨M, hM⟩ := hMex
  classical
  set c : W × ℕ → ℝ := cc A x with hc
  set l : W × ℕ → ℝ := ll q with hl
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 0 < q w)
  have hq1 : ∀ w, (1 : ℝ) ≤ q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 1 ≤ q w)
  have hc0 : ∀ p, 0 ≤ c p := fun p => cc_nonneg A x p
  have hl0 : ∀ p, 0 ≤ l p := fun p => mul_nonneg (by positivity) (Real.log_nonneg (hq1 p.1))
  have hpt : ∀ (σ : ℝ) p, ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) :=
    fun σ p => sum_lterm q A x hq σ p
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun p => c p * Real.exp (-(l p * σ)) := by
    intro σ hσ
    have h1 : ∀ i j, Summable fun p => ‖lterm q (A (x i)) (A (x j)) σ p‖ := fun i j =>
      (hC W q X d A hS (x i) (x j)).1 σ hσ
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hc0 p) (Real.exp_pos _).le) (fun p => ?_)
      (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ => h1 i j)
    calc c p * Real.exp (-(l p * σ)) = ‖((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hc0 p) (Real.exp_pos _).le)]
      _ = ‖∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p‖ := by rw [hpt σ p]
      _ ≤ ∑ i, ∑ j, ‖lterm q (A (x i)) (A (x j)) σ p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have htsum : ∀ σ : ℝ, 1 < σ → ∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p =
      ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) := by
    intro σ hσ
    have hs : ∀ i j, Summable fun p => lterm q (A (x i)) (A (x j)) σ p := fun i j =>
      ((hC W q X d A hS (x i) (x j)).1 σ hσ).of_norm
    rw [Complex.ofReal_tsum]
    simp_rw [← hpt σ]
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  have hT : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∑' p, c p * Real.exp (-(l p * σ)) ≤ M := by
    intro σ h1 h2
    have := hM σ h1 h2
    rw [htsum σ h1, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  choose F σ0 hFa hFe using fun ij : ι × ι => hS.rs (x ij.1) (x ij.2)
  set G : ℂ → ℂ := fun s => ∏ ij : ι × ι, F ij s with hG
  have hGa : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ := fun σ hσ => by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) (c := (σ : ℂ)) Finset.univ (fun ij _ => hFa ij σ hσ)
    have e : G = ∏ ij ∈ Finset.univ, F ij := by
      funext s
      simp [hG, Finset.prod_apply]
    rw [e]
    exact this
  set B : ℝ := 2 + ∑ ij, |σ0 ij| with hBd
  have hB : ∀ ij, σ0 ij ≤ B := fun ij => by
    have := Finset.single_le_sum (f := fun ij => |σ0 ij|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)
    have := le_abs_self (σ0 ij)
    linarith
  have hB2 : (2 : ℝ) ≤ B := by
    have := Finset.sum_nonneg (s := Finset.univ) (f := fun ij : ι × ι => |σ0 ij|) (fun _ _ => abs_nonneg _)
    linarith
  set r : ℕ := (Finset.univ.filter fun ij : ι × ι => x ij.1 = x ij.2).card with hr
  set SC : ℂ → ℂ := fun s => ∑' p, (c p : ℂ) * Complex.exp (-((l p : ℂ) * s)) with hSCd
  have hSC : ∀ σ : ℝ, SC σ = ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) := by
    intro σ
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun p => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hSCa : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ SC σ := by
    intro σ hσ
    set σ' : ℝ := (1 + σ) / 2 with hσ'
    have hU : IsOpen {s : ℂ | σ' < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ SC {s : ℂ | σ' < s.re} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hsum σ' (by linarith)) (fun p => ?_) hU (fun p s hs => ?_)
      · exact (Differentiable.differentiableOn (by fun_prop))
      · rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (hc0 p)]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc0 p)
        have hs' : σ' < s.re := hs
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith [hl0 p]
    exact hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith))
  have hEq : ∀ σ : ℝ, B < σ → G σ = ((σ : ℂ) - 1) ^ r * Complex.exp (SC σ) := by
    intro σ hσ
    have h2 : (2 : ℝ) < σ := by linarith
    have e0 : G σ = ∏ ij : ι × ι, ((if x ij.1 = x ij.2 then (σ : ℂ) - 1 else 1) *
        eul q (A (x ij.1)) (A (x ij.2)) σ) :=
      Finset.prod_congr rfl fun ij _ => hFe ij σ (lt_of_le_of_lt (hB ij) hσ)
    rw [e0, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    · rw [hSC σ, ← htsum σ (by linarith), ← Fintype.sum_prod_type', Complex.exp_sum]
      refine Finset.prod_congr rfl fun ij _ => ?_
      exact (hE W q (Fin (d (x ij.1))) (Fin (d (x ij.2))) (A (x ij.1)) (A (x ij.2)) σ hS.primes (hS.bd _) (hS.bd _)
        (by simpa using h2)).2.1
  have ha1 : AnalyticOnNhd ℝ (fun t : ℝ => G t) (Set.Ioi 1) := fun t ht => by
    have h1 : AnalyticAt ℝ G (t : ℂ) := (hGa t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have ha2 : AnalyticOnNhd ℝ (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1) := fun t ht => by
    have h : AnalyticAt ℂ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ) :=
      ((analyticAt_id.sub analyticAt_const).pow r).mul (hSCa t (Set.mem_Ioi.1 ht)).cexp
    have h1 : AnalyticAt ℝ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ) := h.restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have hid : Set.EqOn (fun t : ℝ => G t) (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1) :=
    ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_Ioi (z₀ := B + 1)
      (Set.mem_Ioi.2 (by linarith)) (by
        filter_upwards [Ioi_mem_nhds (show B < B + 1 by linarith)] with t ht
        exact hEq t ht)
  have hGb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖G σ‖ ≤ Real.exp M * (σ - 1) ^ r := by
    intro σ h1 h2
    have e := hid (Set.mem_Ioi.2 h1)
    simp only at e
    have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [e, norm_mul, norm_pow, hn, hSC, Complex.norm_exp_ofReal, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hT σ h1 h2)) (pow_nonneg (by linarith) _)
  obtain ⟨G', hG'a, hG'e⟩ := hR G r (Real.exp M) hGa hGb
  have hG'v : ∀ σ : ℝ, 1 < σ → G' σ = ((Real.exp (∑' p, c p * Real.exp (-(l p * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have e1 := hid (Set.mem_Ioi.2 hσ)
    simp only at e1
    have e2 := hG'e σ hσ
    have hne : ((σ : ℂ) - 1) ^ r ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (by exact_mod_cast hσ.ne'))
    rw [e1] at e2
    have e3 := mul_left_cancel₀ hne e2
    rw [← e3, hSC, Complex.ofReal_exp]
  have hLand := hL (W × ℕ) c l 0 1 G' hc0 hl0 (fun σ hσ => hG'a σ hσ) hsum (fun σ hσ => hG'v σ hσ)
  set N : ℕ := ∑ i, d (x i) with hNd
  have hN1 : 1 ≤ N := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact le_trans (hS.pos (x i)) (Finset.single_le_sum (f := fun i => d (x i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs0 := hLand (1 / N) (by positivity)
  obtain ⟨c0, hc0pos, hc0le⟩ := hN N hN1
  have hlow : ∀ w, c0 / N * (q w : ℝ)⁻¹ ≤ ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N))) := by
    intro w
    have hnew := hc0le (Σ i : ι, Fin (d (x i))) (fun ib => A (x ib.1) w ib.2)
      (by rw [Fintype.card_sigma]; simp [hNd]) (by
        rw [Fintype.prod_sigma, norm_prod]
        exact Finset.prod_eq_one fun i _ => hS.det (x i) w)
    have hPk : ∀ k, (∑ ib : Σ i : ι, Fin (d (x i)), A (x ib.1) w ib.2 ^ (k + 1)) = PP A x (w, k) := fun k => by
      rw [Fintype.sum_sigma]; rfl
    simp only [hPk] at hnew
    have hterm : ∀ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ ≤ c (w, k) * Real.exp (-(l (w, k) * (1 / N))) := by
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hk
      have hlog : 0 ≤ Real.log (q w) := Real.log_nonneg (hq1 w)
      have he : (q w : ℝ)⁻¹ ≤ Real.exp (-(l (w, k) * (1 / N))) := by
        rw [← Real.exp_log (hq w), ← Real.exp_neg]
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        simp only [hl, ll]
        calc ((k : ℝ) + 1) * Real.log (q w) * (1 / N) = ((k + 1) / N) * Real.log (q w) := by ring
          _ ≤ 1 * Real.log (q w) := mul_le_mul_of_nonneg_right ((div_le_one hNpos).2 hk') hlog
          _ = Real.log (q w) := one_mul _
      have hc' : ‖PP A x (w, k)‖ ^ 2 / N ≤ c (w, k) := by
        simp only [hc, cc]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk'
      exact mul_le_mul hc' he (by positivity) (hc0 _)
    calc c0 / N * (q w : ℝ)⁻¹ ≤ (∑ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2) / N * (q w : ℝ)⁻¹ := by
          gcongr
      _ = ∑ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ := by
          rw [Finset.sum_div, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hsw : Summable fun w => ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N))) :=
    summable_sum (s := Finset.range N) fun k _ => hs0.comp_injective (fun a b h => (Prod.mk.inj h).1)
  have h2 : Summable fun w => c0 / N * (q w : ℝ)⁻¹ :=
    Summable.of_nonneg_of_le (fun w => by have := hq w; positivity) hlow hsw
  have h3 : Summable fun w => (q w : ℝ)⁻¹ := by
    have := h2.mul_left (N / c0)
    refine this.congr fun w => ?_
    field_simp
  exact hS.primes.div h3

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.RemovableSingularities.RemovableSingularityHolds
noncomputable section

open Filter Topology

namespace PositivityTheory.RgJS

namespace RemovableSingularityAlt

def D (G : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => G
  | j + 1 => dslope (D G j) 1

theorem analyticAt_dslope {f : ℂ → ℂ} {z : ℂ} (h1 : AnalyticAt ℂ f 1) (hz : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f 1) z := by
  rcases eq_or_ne z 1 with rfl | hne
  · have hev := h1.eventually_analyticAt
    have hd : DifferentiableOn ℂ f {w | AnalyticAt ℂ f w} := fun w hw => hw.differentiableAt.differentiableWithinAt
    have hs : {w | AnalyticAt ℂ f w} ∈ 𝓝 (1 : ℂ) := hev
    exact ((Complex.differentiableOn_dslope hs).2 hd).analyticAt hs
  · have hsl : AnalyticAt ℂ (fun w => (w - 1)⁻¹ • (f w - f 1)) z :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hne)).smul (hz.sub analyticAt_const)
    refine hsl.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hne] with w hw
    rw [dslope_of_ne _ hw, slope_def_module]

theorem analytic_D {G : ℂ → ℂ} (hG : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) :
    ∀ j, ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ (D G j) σ := by
  intro j
  induction j with
  | zero => exact hG
  | succ j ih =>
      intro σ hσ
      have h1 : AnalyticAt ℂ (D G j) (1 : ℂ) := ih 1 one_pos
      rw [D]
      exact analyticAt_dslope h1 (ih σ hσ)

theorem factor (G : ℂ → ℂ) : ∀ j, (∀ i < j, D G i 1 = 0) → ∀ z, G z = (z - 1) ^ j * D G j z := by
  intro j
  induction j with
  | zero => intro _ z; simp [D]
  | succ j ih =>
      intro h z
      have e : (z - 1) * D G (j + 1) z = D G j z := by
        rw [D, ← smul_eq_mul]
        exact sub_smul_dslope_of_zero (h j (Nat.lt_succ_self j)) z
      rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)) z, pow_succ, mul_assoc, e]

end RemovableSingularityAlt

open RemovableSingularityAlt in
theorem removable_singularity_holds : Remov := by
  intro G r M hG hM
  have han := analytic_D hG
  have key : ∀ j ≤ r, ∀ i < j, D G i 1 = 0 := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      have hprev := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hprev i hi
      ·
        have hfac : ∀ z : ℂ, G z = (z - 1) ^ i * D G i z := factor G i hprev
        have hc : ContinuousAt (D G i) 1 := by
          have := (han i 1 one_pos).continuousAt
          simpa using this

        have hb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D G i σ‖ ≤ |M| * (σ - 1) := by
          intro σ h1 h2
          have h0 : (0 : ℝ) < σ - 1 := by linarith
          have hle := hM σ h1 h2
          rw [hfac, norm_mul, norm_pow, show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg h0.le] at hle
          have hpow : (σ - 1) ^ r = (σ - 1) ^ i * (σ - 1) ^ (r - i) := by
            rw [← pow_add]; congr 1; omega
          rw [hpow] at hle
          have hpi : 0 < (σ - 1) ^ i := pow_pos h0 i
          have h3 : ‖D G i σ‖ ≤ M * (σ - 1) ^ (r - i) := by
            have := le_of_mul_le_mul_left (by linarith [hle] : (σ - 1) ^ i * ‖D G i σ‖ ≤ (σ - 1) ^ i * (M * (σ - 1) ^ (r - i))) hpi
            exact this
          have h4 : (σ - 1) ^ (r - i) ≤ σ - 1 := by
            have hr : 1 ≤ r - i := by omega
            calc (σ - 1) ^ (r - i) ≤ (σ - 1) ^ 1 := pow_le_pow_of_le_one h0.le (by linarith) hr
              _ = σ - 1 := pow_one _
          calc ‖D G i σ‖ ≤ M * (σ - 1) ^ (r - i) := h3
            _ ≤ |M| * (σ - 1) ^ (r - i) := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
            _ ≤ |M| * (σ - 1) := mul_le_mul_of_nonneg_left h4 (abs_nonneg M)

        have hlim : Tendsto (fun σ : ℝ => D G i σ) (𝓝[>] 1) (𝓝 (D G i 1)) := by
          have hcr : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
            have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
              (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
            simpa using this
          exact hc.tendsto.comp hcr
        have hlim0 : Tendsto (fun σ : ℝ => D G i σ) (𝓝[>] 1) (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine squeeze_zero' (g := fun σ : ℝ => |M| * (σ - 1)) (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
          · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hσ
            exact hb σ hσ.1 hσ.2.le
          · have : Tendsto (fun σ : ℝ => |M| * (σ - 1)) (𝓝 1) (𝓝 (|M| * (1 - 1))) :=
              (continuous_const.mul (continuous_id.sub continuous_const)).tendsto 1
            rw [sub_self, mul_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
        exact tendsto_nhds_unique hlim hlim0
  refine ⟨D G r, han r, fun σ _ => factor G r (key r le_rfl) σ⟩

end PositivityTheory.RgJS
end
end

namespace PositivityTheory.RgJS

theorem absRig_closed : AbsRig :=
  absolute_rigidity_of_common (common_of_landau_euler landauL euler_product_log_bound (convergence_of_landau_euler landauL euler_product_log_bound)
    (dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds (convergence_of_landau_euler landauL euler_product_log_bound)))

theorem rigid (h : RSPole) (hB : GlobalTheory.Published.JacquetShalikaBound) : GlobalTheory.Published.JacquetShalikaRigidity :=
  jacquet_shalika_rigidity_of_bound absRig_closed unit_exponent_holds satake_twist_holds determinant_one_condition_holds prime_sum_converges_and_diverges (rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds h) hB

end PositivityTheory.RgJS

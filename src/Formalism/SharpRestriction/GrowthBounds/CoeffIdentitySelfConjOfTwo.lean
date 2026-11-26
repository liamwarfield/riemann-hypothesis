module

public import Formalism.SharpRestriction.GrowthBounds.R1sExpLowHolds

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfFourOpen
section -- merged from Formalism.SharpRestriction.GrowthBounds.ConstantCoeffUnshiftLogarithm
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace SelfConjDifferentials

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_unshift_logarithm (Y : FBChart C V O dd) (i : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0 := by
  rw [constantCoeff_uncurry, Y.lg_const]

theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem exp_sum_range {σ : Type} (f : ℕ → MvPowerSeries σ C) (hf : ∀ k, MvPowerSeries.constantCoeff (f k) = 0)
    (n : ℕ) : mvExp (∑ k ∈ Finset.range n, f k) = ((List.range n).map fun k => mvExp (f k)).prod := by
  induction n with
  | zero => simp [rtj_mvExp_zero]
  | succ n ih =>
    have h0 : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, f k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => hf k
    rw [Finset.sum_range_succ, VP.exp_add h0 (hf n), ih, List.range_succ, List.map_append, List.prod_append]
    simp

theorem lg_zero (Y : FBChart C V O dd) {τ : Type} (i : Fin dd) :
    MvPowerSeries.subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) (un1 (Y.lg i)) = 0 := by
  show MvPowerSeries.subst (0 : Fin dd → MvPowerSeries τ C) (un1 (Y.lg i)) = 0
  rw [MvPowerSeries.subst_zero_eq_C_constantCoeff, constantCoeff_unshift_logarithm]
  simp

theorem subst_add_logarithm_additive (Y : FBChart C V O dd) {τ : Type} (a b : Fin dd → MvPowerSeries τ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (VP.addAt Y a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by
  have h := lg_addOf Y ![a, b] (fun k j => by fin_cases k; exacts [ha j, hb j]) i
  have e : (fun q : Fin 2 × Fin dd => (![a, b] : Fin 2 → Fin dd → MvPowerSeries τ C) q.1 q.2) = VP.P2 a b := by
    funext q
    obtain ⟨k, j⟩ := q
    fin_cases k <;> simp [VP.P2]
  rw [e] at h
  exact h

theorem lg_sumL (Y : FBChart C V O dd) {τ : Type} (i : Fin dd) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, VP.GoodPt V a) →
      MvPowerSeries.subst (VP.sumL Y l) (un1 (Y.lg i)) = (l.map fun a => MvPowerSeries.subst a (un1 (Y.lg i))).sum
  | [], _ => by
    show MvPowerSeries.subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) (un1 (Y.lg i)) = _
    rw [lg_zero, List.map_nil, List.sum_nil]
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    have hl : ∀ b ∈ l, VP.GoodPt V b := fun b hb => h b (List.mem_cons_of_mem _ hb)
    show MvPowerSeries.subst (VP.addAt Y a (VP.sumL Y l)) (un1 (Y.lg i)) = _
    rw [subst_add_logarithm_additive Y a _ ha.1 (VP.good_sumL Y l hl).1, lg_sumL Y i l hl, List.map_cons, List.sum_cons]

theorem pt_eq_of_lg (Y : FBChart C V O dd) {τ : Type} {A B : Fin dd → MvPowerSeries τ C}
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (hB : ∀ j, MvPowerSeries.constantCoeff (B j) = 0)
    (h : ∀ i, MvPowerSeries.subst A (un1 (Y.lg i)) = MvPowerSeries.subst B (un1 (Y.lg i))) : A = B := by
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => constantCoeff_unshift_logarithm Y j
  have key : ∀ A : Fin dd → MvPowerSeries τ C, (∀ j, MvPowerSeries.constantCoeff (A j) = 0) → ∀ i,
      MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
    intro A hA i
    have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
    have hx : un1 (comp1 Y.ex Y.lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
      rw [Y.ex_lg]; exact uncurry_X i
    rw [← MvPowerSeries.subst_comp_subst_apply hL hA', uncurry_comp Y.lg_const, hx, MvPowerSeries.subst_X hA']
  funext i
  rw [← key A hA i, ← key B hB i]
  simp only [h]

theorem hAt_self (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) {τ : Type}
    (a b : Fin 2 × Fin dd → MvPowerSeries τ C) (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0)
    (hb : ∀ x, MvPowerSeries.constantCoeff (b x) = 0) :
    SelfConjCharts.hAt (Y.rawSelf p) a b = ∑ col : Fin 2, VP.hAt Y (fun x => a (col, x)) (fun x => b (col, x)) := by
  have hP : MvPowerSeries.HasSubst (SelfConjCharts.pairSubst a b) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      unfold SelfConjCharts.pairSubst
      split_ifs
      exacts [ha _, hb _]
  have hc : ∀ col : Fin 2, MvPowerSeries.subst (SelfConjCharts.pairSubst a b) (hCol col Y.h) =
      VP.hAt Y (fun x => a (col, x)) (fun x => b (col, x)) := by
    intro col
    have hI : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
        (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
    unfold hCol
    rw [MvPowerSeries.subst_comp_subst_apply hI hP]
    show _ = MvPowerSeries.subst (VP.P2 _ _) Y.h
    congr 1
    funext q
    rw [MvPowerSeries.subst_X hP]
    rfl
  show MvPowerSeries.subst (SelfConjCharts.pairSubst a b) (∑ col, hCol col Y.h) = _
  rw [Fin.sum_univ_two, Fin.sum_univ_two, MvPowerSeries.subst_add hP, hc 0, hc 1]

theorem col_left (Y : FBChart C V O dd) {τ : Type} (n : ℕ) (a : ℕ → Fin dd → MvPowerSeries τ C)
    {s c : Fin dd → MvPowerSeries τ C} (ha : ∀ k, VP.GoodPt V (a k)) (hs : VP.GoodPt V s) (hc : VP.GoodPt V c)
    (hsum : s = VP.sumL Y ((List.range n).map a)) :
    IntS V (mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c)) ∧
      MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c) = 0 := by
  open VP in
  have biadd :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y (sumL Y l) c) * U = (l.map fun a => mvExp (hAt Y a c)).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, IsIU.one, by
      show mvExp (hAt Y (fun _ => 0) c) * 1 = 1
      rw [hAt_zero_left Y hc.1, rtj_mvExp_zero, one_mul]⟩
    | cons a l ih =>
      intro h
      have ha := h a List.mem_cons_self
      have hl := good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U, hU, e⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hp := first_partial_law_at_points Y ha.1 hl.1 hc.1
      have hpi : IntS V (MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1) :=
        IntS.subst (constantCoeff_triple_substitution ha.1 hl.1 hc.1) (integral_triple_substitution ha.2 hl.2 hc.2) Y.intPh1
      refine ⟨MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1 * U, (isIU_of_exp hpi hp).mul hU, ?_⟩
      have c1 := cc_hAt Y ha.1 hc.1
      have c2 := cc_hAt Y hl.1 hc.1
      have c3 := cc_hAt Y (cc_addAt Y ha.1 hl.1) hc.1
      have e2 : mvExp (hAt Y (addAt Y a (sumL Y l)) c) * MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1 =
          mvExp (hAt Y a c) * mvExp (hAt Y (sumL Y l) c) := by
        rw [hp, ← exp_add c3 (by rw [map_sub, map_add (f := _), c1, c2, c3]; simp), ← exp_add c1 c2]
        congr 1
        ring
      show mvExp (hAt Y (addAt Y a (sumL Y l)) c) * _ = _
      rw [List.map_cons, List.prod_cons, ← e, ← mul_assoc, e2, mul_assoc]

  obtain ⟨U, hU, e⟩ := biadd ((List.range n).map a) (by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact ha k)
  rw [← hsum, List.map_map] at e
  have c1 : ∀ k, MvPowerSeries.constantCoeff (VP.hAt Y (a k) c) = 0 := fun k => VP.cc_hAt Y (ha k).1 hc.1
  have c2 : MvPowerSeries.constantCoeff (VP.hAt Y s c) = 0 := VP.cc_hAt Y hs.1 hc.1
  have cS : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y (a k) c) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => c1 k
  have c2' : MvPowerSeries.constantCoeff (-VP.hAt Y s c) = 0 := by rw [map_neg, c2, neg_zero]
  have hU' : mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c) = mvExp (VP.hAt Y s c) * U := by
    rw [exp_sum_range (fun k => VP.hAt Y (a k) c) c1 n, e]
    rfl
  have inv : mvExp (VP.hAt Y s c) * mvExp (-VP.hAt Y s c) = 1 := by
    rw [← VP.exp_add c2 c2', add_neg_cancel, rtj_mvExp_zero]
  have key : mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c) = U := by
    rw [sub_eq_add_neg, VP.exp_add cS c2', hU', mul_comm (mvExp (VP.hAt Y s c)) U, mul_assoc, inv, mul_one]
  refine ⟨?_, by rw [map_sub, cS, c2, sub_zero]⟩
  rw [key]
  exact hU.1

theorem col_right (Y : FBChart C V O dd) {τ : Type} (n : ℕ) (a : ℕ → Fin dd → MvPowerSeries τ C)
    {s c : Fin dd → MvPowerSeries τ C} (ha : ∀ k, VP.GoodPt V (a k)) (hs : VP.GoodPt V s) (hc : VP.GoodPt V c)
    (hsum : s = VP.sumL Y ((List.range n).map a)) :
    IntS V (mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s)) ∧
      MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s) = 0 := by
  open VP in
  have biadd :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y c (sumL Y l)) * U = (l.map fun a => mvExp (hAt Y c a)).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, IsIU.one, by
      show mvExp (hAt Y c (fun _ => 0)) * 1 = 1
      rw [hAt_zero_right Y hc.1, rtj_mvExp_zero, one_mul]⟩
    | cons a l ih =>
      intro h
      have ha := h a List.mem_cons_self
      have hl := good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U, hU, e⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hp := second_partial_law_at_points Y hc.1 ha.1 hl.1
      have hpi : IntS V (MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2) :=
        IntS.subst (constantCoeff_triple_substitution hc.1 ha.1 hl.1) (integral_triple_substitution hc.2 ha.2 hl.2) Y.intPh2
      refine ⟨MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2 * U, (isIU_of_exp hpi hp).mul hU, ?_⟩
      have c1 := cc_hAt Y hc.1 ha.1
      have c2 := cc_hAt Y hc.1 hl.1
      have c3 := cc_hAt Y hc.1 (cc_addAt Y ha.1 hl.1)
      have e2 : mvExp (hAt Y c (addAt Y a (sumL Y l))) * MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2 =
          mvExp (hAt Y c a) * mvExp (hAt Y c (sumL Y l)) := by
        rw [hp, ← exp_add c3 (by rw [map_sub, map_add (f := _), c1, c2, c3]; simp), ← exp_add c1 c2]
        congr 1
        ring
      show mvExp (hAt Y c (addAt Y a (sumL Y l))) * _ = _
      rw [List.map_cons, List.prod_cons, ← e, ← mul_assoc, e2, mul_assoc]

  obtain ⟨U, hU, e⟩ := biadd ((List.range n).map a) (by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact ha k)
  rw [← hsum, List.map_map] at e
  have c1 : ∀ k, MvPowerSeries.constantCoeff (VP.hAt Y c (a k)) = 0 := fun k => VP.cc_hAt Y hc.1 (ha k).1
  have c2 : MvPowerSeries.constantCoeff (VP.hAt Y c s) = 0 := VP.cc_hAt Y hc.1 hs.1
  have cS : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y c (a k)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => c1 k
  have c2' : MvPowerSeries.constantCoeff (-VP.hAt Y c s) = 0 := by rw [map_neg, c2, neg_zero]
  have hU' : mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k)) = mvExp (VP.hAt Y c s) * U := by
    rw [exp_sum_range (fun k => VP.hAt Y c (a k)) c1 n, e]
    rfl
  have inv : mvExp (VP.hAt Y c s) * mvExp (-VP.hAt Y c s) = 1 := by
    rw [← VP.exp_add c2 c2', add_neg_cancel, rtj_mvExp_zero]
  have key : mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s) = U := by
    rw [sub_eq_add_neg, VP.exp_add cS c2', hU', mul_comm (mvExp (VP.hAt Y c s)) U, mul_assoc, inv, mul_one]
  refine ⟨?_, by rw [map_sub, cS, c2, sub_zero]⟩
  rw [key]
  exact hU.1

theorem biInt_self (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    SelfConjCharts.BiInt (Y.rawSelf p) V := by
  intro τ _ n a s c ha hs hc hlg
  have gp : ∀ {b : Fin 2 × Fin dd → MvPowerSeries τ C}, SelfConjCharts.IsPt V b → ∀ col : Fin 2,
      VP.GoodPt V (fun x => b (col, x)) :=
    fun hb col => ⟨fun x => (hb (col, x)).1, fun x => (hb (col, x)).2⟩
  have cc0 : ∀ {b : Fin 2 × Fin dd → MvPowerSeries τ C}, SelfConjCharts.IsPt V b → ∀ q,
      MvPowerSeries.constantCoeff (b q) = 0 :=
    fun hb q => (hb q).1
  have hsum : ∀ col : Fin 2,
      (fun x => s (col, x)) = VP.sumL Y ((List.range n).map fun k x => a k (col, x)) := by
    intro col
    have hl : ∀ b ∈ (List.range n).map (fun k x => a k (col, x)), VP.GoodPt V b := by
      intro b hb
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
      exact gp (ha k) col
    apply pt_eq_of_lg Y (gp hs col).1 (VP.good_sumL Y _ hl).1
    intro i
    rw [lg_sumL Y i _ hl, List.map_map]
    have h := hlg (col, i)
    change MvPowerSeries.subst s (inCol col (un1 (Y.lg i))) =
      ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (inCol col (un1 (Y.lg i))) at h
    have h2 : ∀ k, MvPowerSeries.subst (a k) (inCol col (un1 (Y.lg i))) =
        MvPowerSeries.subst (fun x => a k (col, x)) (un1 (Y.lg i)) :=
      fun k => subst_inCol (cc0 (ha k)) col _
    rw [subst_inCol (cc0 hs)] at h
    simp only [h2] at h
    rw [h, sum_range_list]
    rfl
  constructor
  · have e : ∑ k ∈ Finset.range n, SelfConjCharts.hAt (Y.rawSelf p) (a k) c - SelfConjCharts.hAt (Y.rawSelf p) s c =
        ∑ col : Fin 2, (∑ k ∈ Finset.range n, VP.hAt Y (fun x => a k (col, x)) (fun x => c (col, x)) -
          VP.hAt Y (fun x => s (col, x)) (fun x => c (col, x))) := by
      rw [Finset.sum_congr rfl fun k _ => hAt_self Y p (a k) c (cc0 (ha k)) (cc0 hc),
        hAt_self Y p s c (cc0 hs) (cc0 hc), Finset.sum_comm, ← Finset.sum_sub_distrib]
    have h0 := col_left Y n (fun k x => a k (0, x)) (fun k => gp (ha k) 0) (gp hs 0) (gp hc 0) (hsum 0)
    have h1 := col_left Y n (fun k x => a k (1, x)) (fun k => gp (ha k) 1) (gp hs 1) (gp hc 1) (hsum 1)
    rw [e, Fin.sum_univ_two, VP.exp_add h0.2 h1.2]
    exact h0.1.mul h1.1
  · have e : ∑ k ∈ Finset.range n, SelfConjCharts.hAt (Y.rawSelf p) c (a k) - SelfConjCharts.hAt (Y.rawSelf p) c s =
        ∑ col : Fin 2, (∑ k ∈ Finset.range n, VP.hAt Y (fun x => c (col, x)) (fun x => a k (col, x)) -
          VP.hAt Y (fun x => c (col, x)) (fun x => s (col, x))) := by
      rw [Finset.sum_congr rfl fun k _ => hAt_self Y p c (a k) (cc0 hc) (cc0 (ha k)),
        hAt_self Y p c s (cc0 hc) (cc0 hs), Finset.sum_comm, ← Finset.sum_sub_distrib]
    have h0 := col_right Y n (fun k x => a k (0, x)) (fun k => gp (ha k) 0) (gp hs 0) (gp hc 0) (hsum 0)
    have h1 := col_right Y n (fun k x => a k (1, x)) (fun k => gp (ha k) 1) (gp hs 1) (gp hc 1) (hsum 1)
    rw [e, Fin.sum_univ_two, VP.exp_add h0.2 h1.2]
    exact h0.1.mul h1.1

end SelfConjDifferentials

theorem biadditive_on_columns : BiadditiveOnColumns := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  exact SelfConjDifferentials.biInt_self Y p

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SumRescaleTySTwo
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoeffOneAlongCvLg
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_tyS_Fs {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) := by
  rw [← tyS_Vpow hl]
  apply tyS_eq hl
  · intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
    rw [← Finset.sum_mul]
    cases s with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ s =>
      have h1 : ∀ k, (ζ ^ k) ^ (l ^ (s + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  · intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]

theorem rescale_sum_smul {ι : Type} [Fintype ι] (a : C) (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.rescale a (∑ c, u c • f c) = ∑ c, u c • PowerSeries.rescale a (f c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem subst_pow_sum_smul {n : ℕ} (hn : 0 < n) {ι : Type} [Fintype ι] (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (∑ c, u c • f c) =
      ∑ c, u c • PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (f c) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hn.ne'])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← PowerSeries.coe_substAlgHom hS, map_sum]
  simp only [map_smul]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem coeff_one_alongCv_lg (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    PowerSeries.coeff 1 (alongCv γ (X.lg i)) = PowerSeries.coeff 1 (γ i) := by
  rw [coeff_alongCv_low le_rfl (fun j m hm => by
      have : m = 0 := by omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ j]) (hB.lg0 i)]
  rw [Finset.sum_eq_single i]
  · rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_neg, zero_mul]
    intro h
    exact hj (Finsupp.single_left_injective one_ne_zero h)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeff_one_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.coeff 1 (tyS l a) = a 0 := by
  have h := coeff_tyS_pow hl a 0
  rwa [pow_zero] at h

theorem coeff_one_of_mem (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {g : Fin 2} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {x : ℕ → I g ⊕ JJ I g → C}
    (h1 : ∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) (i : κ) :
    PowerSeries.coeff 1 (γ i) = ∑ c : I g, X.u g c i * x 0 (Sum.inl c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coeff_one_alongCv_lg X hB hγ i, h1 i, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_smul, coeff_one_tyS V.l_prime.two_le, smul_eq_mul]

end SelfConjCharts

open SelfConjCharts in
theorem r1sRestB_holds : OtherGroupCurvesClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g q
  have hl2 := V.l_prime.two_le
  set g' : Fin 2 := 1 - g with hg'
  obtain ⟨x, hx, hx0, -⟩ := (H g').t4 (X.ty g' q) (fun c => if c = q then 1 else 0)
    (fun c => by split_ifs <;> simp [VF.Ge.zero, VF.Ge.one])
    (fun c hc => by
      rw [if_neg]
      rintro rfl
      exact hc rfl)
  have hF := (H g').Fm x hx
  obtain ⟨z, -, hz, -, hz1, -⟩ := id hx
  obtain ⟨ε, -, hε, -, hε1, -⟩ := hF
  refine ⟨z, ε, fun q' => Fs V.l x 0 (Sum.inl q'), hz, hε, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hε1 i, hz1 i, subst_pow_sum_smul (by omega)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    exact subst_tyS_Fs hl2 hζ (fun s => x s (Sum.inl c))
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hz i).1) hz1 i, hx0]
    simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hε i).1) hε1 i]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro q'
    exact (H g').t2 _ ((H g').Fm x hx) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_X_pow_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) f := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  rw [PowerSeries.subst_comp_subst_apply hS hS]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]

theorem sum_rescale_tyS_two {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) (ha : a 1 = 0) :
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (tyS l fun s => (l : C) * a (s + 2)) := by
  have e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2) := by
    funext s
    cases s with
    | zero => simp [ha]
    | succ s => simp
  rw [← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]
  congr 1
  rw [← tyS_Vpow hl, e]

theorem sum_root_pow {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range l, (ζ ^ k) ^ (l ^ j) = (l : C) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  simp [h1]

theorem coeff_sum_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) (f : PowerSeries C) :
    PowerSeries.coeff (l ^ j) (∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) f) =
      (l : C) * PowerSeries.coeff (l ^ j) f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_root_pow hζ j hj]

section MM

variable {V : VF C}

theorem mmA_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mmA_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mmA_sum {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h

theorem mmA_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' hb ha

end MM

end SelfConjCharts

open SelfConjCharts in
theorem good_curve_closed : GoodCurveClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hxT : x ∈ X.TySet V g := hG.1.1
  have hx1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2

  have hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g := by
    have hF := (H g).Fm x hxT
    have h3 := (H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)
    have hsub := (H g).add _ _ hF ((H g).neg _ h3)
    convert hsub using 1
    funext i n
    cases i with
    | zero =>
      cases n with
      | inl c => simp [Vpow, Fs, const0, hx1 c]
      | inr q => simp [Vpow, Fs, const0, Cart.c0']
    | succ i => simp [Vpow, Fs, const0]
  have hyT' := X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT
  obtain ⟨γ, lam, hγ, hlam, hγ1, hγ2⟩ := id hxT
  obtain ⟨δ, -, hδ, -, hδ1, -⟩ := hyT'
  refine ⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]
  · intro i
    rw [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]
    exact mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)
  · intro q
    have hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) =
        PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) +
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inl c)) else 0) := by
      intro n
      have e := congrArg (PowerSeries.coeff n) (hγ2 q)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero,
        smul_eq_mul] at e
      linear_combination e
    have hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1 := fun b => by
      simpa using coeff_tyS_pow hl2 b 1
    have hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2 := fun b => coeff_tyS_pow hl2 b 2
    have hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
        (V.l : C) * PowerSeries.coeff V.l f := fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f
    have hN2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
          (V.l : C) * PowerSeries.coeff (V.l ^ 2) f := fun f => coeff_sum_rescale hζ 2 (by norm_num) f
    have hl2pos : 0 < V.l ^ 2 := by positivity
    have hS1 : ∀ f : PowerSeries C,
        PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0 := fun f =>
      coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by
        have := Nat.le_of_dvd hl0 h
        nlinarith)
    have hS2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) =
          PowerSeries.coeff 1 f := fun f => by simpa using coeff_subst_X_pow hl2pos f 1
    refine ⟨hG.c0'_int q, ?_, ?_⟩
    · have e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q =
          -((V.l : C) * PowerSeries.coeff V.l (lam q)) := by
        unfold phi
        rw [map_sub, hS1, hN1, hA]
        simp only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']
        ring
      rw [e]
      exact MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))
    · have hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) =
          ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q) := by
        rw [coeff_alongCv_low le_rfl (fun j m hm => by
            obtain rfl : m = 0 := by omega
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]
        simp only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1,
          RawChart.sg1, Finset.mul_sum, zero_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) -
          (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) =
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> ring
      have e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) =
          (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) +
            -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q)) := by
        unfold phi
        rw [map_sub, hS2, hN2, hA, hB1]
        simp only [hT2]
        linear_combination key
      rw [e]
      refine mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))
      split_ifs with hm
      · exact mmA_zero
      · exact mmA_mul_int (hV2 c) (hB.hmis g c q hm)

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sFrob_holds : PowerSeriesFrobeniusCongruence := frobPow_smul

theorem r1sRoots_holds : RootsOfUnityProductCongruence := fun C _ V ζ hζ j f hf μ => rootsProd C V ζ hζ j f hf μ

theorem coeffIdentity_selfConj_of_four_open (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry) (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds
    (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.PsOfIntS
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjGauge

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def IsPt (V : VF C) {τ : Type} (a : κ → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (a i) = 0 ∧ IntS V (a i)

def BiInt (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ (τ : Type) [Finite τ] (n : ℕ) (a : ℕ → κ → MvPowerSeries τ C) (s c : κ → MvPowerSeries τ C),
    (∀ k, IsPt V (a k)) → IsPt V s → IsPt V c →
    (∀ i, MvPowerSeries.subst s (X.lg i) = ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (X.lg i)) →
    IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range n, hAt X (a k) c - hAt X s c)) ∧
      IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range n, hAt X c (a k) - hAt X c s))

def NormRel (X : RawChart C d I κ) (l n : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) =
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i))

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

section Lem

variable {V : VF C}

theorem intS_of_ps {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) : IntS V f := fun μ => by
  have hμ : μ = Finsupp.single () (μ ()) := Finsupp.ext fun u => by cases u; simp
  rw [hμ]; exact hf (μ ())

theorem ps_of_intS {f : PowerSeries C} (hf : IntS V f) : ∀ n, V.Ge 0 (PowerSeries.coeff n f) :=
  fun n => hf (Finsupp.single () n)

theorem subst_ps {τ : Type} {a : MvPowerSeries τ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hai : IntS V a) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 ∧ IntS V (PowerSeries.subst a f) := by
  refine ⟨constantCoeff_subst_zero (σ := Unit) (fun _ => ha) hf0, ?_⟩
  exact PartialDerivEval.intS_subst (fun _ => ha) (fun _ => hai) (intS_of_ps hf)

theorem inV_pt (j : Fin 2) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    MvPowerSeries.constantCoeff (inV j f) = 0 ∧ IntS V (inV j f) :=
  subst_ps (MvPowerSeries.constantCoeff_X j) (PartialDerivEval.intS_X j) hf0 hf

theorem rc_cv {c : C} (hc : V.Ge 0 c) {γ : κ → PowerSeries C} (hγ : IsCv V γ) : IsCv V (rc c γ) := by
  intro i
  refine ⟨?_, fun n => ?_⟩
  · show PowerSeries.constantCoeff (PowerSeries.rescale c (γ i)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (hγ i).1]
  · show V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale c (γ i)))
    rw [PowerSeries.coeff_rescale]
    exact (hc.pow n).mul_int ((hγ i).2 n)

theorem pw_cv {n : ℕ} (hn : 0 < n) {δ : κ → PowerSeries C} (hδ : IsCv V δ) : IsCv V (pw n δ) := by
  intro i
  have hX : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ n) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  have hXi : IntS V ((PowerSeries.X : PowerSeries C) ^ n) :=
    PartialDerivEval.intS_pow (intS_of_ps fun m => by
      rw [PowerSeries.coeff_X]; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0]) n
  obtain ⟨h0, hI⟩ := subst_ps (τ := Unit) hX hXi (hδ i).1 (hδ i).2
  exact ⟨h0, ps_of_intS hI⟩

theorem subst_inV (j : Fin 2) {x : κ → PowerSeries C} (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun i => inV j (x i)) F = inV j (alongCv x F) := by
  unfold inV alongCv
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ : Unit => MvPowerSeries.constantCoeff_X j))]

theorem inV_sum (j : Fin 2) {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) :
    inV j (∑ k ∈ s, f k) = ∑ k ∈ s, inV j (f k) := by
  unfold inV
  have hS : PowerSeries.HasSubst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← PowerSeries.coe_substAlgHom hS, map_sum]

theorem log_rel (X : RawChart C d I κ) (j : Fin 2) {l n : ℕ} (hn : 0 < n) {ζ : C} {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0)
    (hN : NormRel X l n ζ γ δ) (i : κ) :
    MvPowerSeries.subst (fun i => inV j (pw n δ i)) (X.lg i) =
      ∑ k ∈ Finset.range l, MvPowerSeries.subst (fun i => inV j (rc (ζ ^ k) γ i)) (X.lg i) := by
  have hX : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ n) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  have hpw0 : ∀ i, PowerSeries.constantCoeff (pw n δ i) = 0 := fun i =>
    constantCoeff_subst_zero (σ := Unit) (fun _ => hX) (hδ i)
  have hrc0 : ∀ (c : C) i, PowerSeries.constantCoeff (rc c γ i) = 0 := fun c i => by
    show PowerSeries.constantCoeff (PowerSeries.rescale c (γ i)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i]
  rw [subst_inV j hpw0]
  simp only [subst_inV j (hrc0 _)]
  rw [← inV_sum]
  congr 1
  rw [show alongCv (pw n δ) (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) from
    alongCv_repar hδ hX (X.lg i), hN i]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : PowerSeries.constantCoeff ((ζ ^ k) • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  show PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i)) = alongCv (fun i => PowerSeries.rescale (ζ ^ k) (γ i)) (X.lg i)
  rw [PowerSeries.rescale_eq_subst]
  simp only [PowerSeries.rescale_eq_subst]
  rw [alongCv_repar hγ hc]

end Lem

theorem hInt_core [CharZero C] (V : VF C) (X : RawChart C d I κ) (hBi : BiInt X V) (ζ : C) (hζ : ζ ^ V.l = 1)
    (n : ℕ) (hn : 0 < n) (γ δ c : κ → PowerSeries C) (hγ : IsCv V γ) (hδ : IsCv V δ) (hc : IsCv V c)
    (hN : NormRel X V.l n ζ γ δ) :
    IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ))) := by
  have hζint : V.Ge 0 ζ := V.ge_of_pow_eq_one V.l_prime.ne_zero hζ
  have hrc : ∀ k, IsCv V (rc (ζ ^ k) γ) := fun k => rc_cv (hζint.pow k) hγ
  have hpw : IsCv V (pw n δ) := pw_cv hn hδ
  have pt : ∀ (j : Fin 2) (x : κ → PowerSeries C), IsCv V x → IsPt V (fun i => inV j (x i)) :=
    fun j x hx i => inV_pt j (hx i).1 (hx i).2
  refine ⟨?_, ?_⟩
  · exact (hBi (Fin 2) V.l (fun k i => inV 0 (rc (ζ ^ k) γ i)) (fun i => inV 0 (pw n δ i))
      (fun i => inV 1 (c i)) (fun k => pt 0 _ (hrc k)) (pt 0 _ hpw) (pt 1 _ hc)
      (log_rel X 0 hn (fun i => (hγ i).1) (fun i => (hδ i).1) hN)).1
  · exact (hBi (Fin 2) V.l (fun k i => inV 1 (rc (ζ ^ k) γ i)) (fun i => inV 1 (pw n δ i))
      (fun i => inV 0 (c i)) (fun k => pt 1 _ (hrc k)) (pt 1 _ hpw) (pt 0 _ hc)
      (log_rel X 1 hn (fun i => (hγ i).1) (fun i => (hδ i).1) hN)).2

end SelfConjGauge

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RescaleInV
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjPoints

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

theorem hsX (j : Fin 2) : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem inV_cc (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf

theorem rescale_inV (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by
      show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0
      rw [MvPowerSeries.smul_eq_C_mul, map_mul,
        show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]
  unfold inV
  rw [MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]
  congr 1
  funext u
  rw [MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]
  have h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) =
      MvPowerSeries.X j := MvPowerSeries.subst_X (hsX j) ()
  rw [h1]
  rfl

theorem rescale_HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by
  have hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i))) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_
    unfold pairSubst
    split_ifs
    · exact inV_cc 0 (hx q.2)
    · exact inV_cc 1 (hz q.2)
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold HH hAt
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]
  congr 1
  funext q
  rw [← MvPowerSeries.rescale_eq_subst]
  unfold pairSubst rc
  split_ifs
  · exact rescale_inV w 0 (x q.2)
  · exact rescale_inV w 1 (z q.2)

end SelfConjPoints


open SelfConjPoints in
theorem r1sHResc (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (c : C) :
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z) := by
  have e1 : ∀ y : κ → PowerSeries C, rc 1 y = y := fun y => by
    funext i; unfold rc; rw [PowerSeries.rescale_one]; rfl
  refine ⟨?_, ?_⟩
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sHInt_holds : IntegralUnitFamilies :=
  fun C _ _ V d I _ κ _ X _ hBi ζ hζ n hn γ δ c hγ hδ hc hN => SelfConjGauge.hInt_core V X hBi ζ hζ n hn γ δ c hγ hδ hc hN

theorem r1sHResc_holds : GaugeRescalingSymmetry := r1sHResc

theorem coeffIdentity_selfConj_of_two (hHL : GaugeLeadingTermLinear) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four_open hHL r1sHResc_holds r1sHInt_holds hGe

end Formalism.L2.FormalSeriesBounds

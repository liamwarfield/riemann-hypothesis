module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeAdjointEndPairElementaryBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeAdjointEndPairElementaryBlock
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.EndBlock

open MvPowerSeries

variable {C : Type} [Field C]

theorem eq_zero_of_van {τ : Type} {f : MvPowerSeries τ C} (h : Van (∅ : Set τ) f) : f = 0 := by
  ext ν
  rw [h ν (fun _ _ => Set.notMem_empty _)]
  simp

theorem subst_zero' {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 :=
  eq_zero_of_van (Van.subst Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ hf))

section General

variable {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem cc_lin (hlg : ∀ i, constantCoeff (X.lg i) = 0) (M : Matrix κ κ C) {τ : Type}
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, cc_subst ha, hlg, smul_zero]

theorem cc_endP (hlg : ∀ i, constantCoeff (X.lg i) = 0) (hex : ∀ i, constantCoeff (X.ex i) = 0)
    (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    constantCoeff (endP X M a i) = 0 := by
  unfold endP
  rw [cc_subst (cc_lin X hlg M ha), hex]

theorem subst_endP (hlg : ∀ i, constantCoeff (X.lg i) = 0) (M : Matrix κ κ C) {τ υ : Type} [Finite τ]
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) (i : κ) :
    subst b (endP X M a i) = endP X M (fun k => subst b (a k)) i := by
  have hA := hasSubst_of_constantCoeff_zero ha
  have hB := hasSubst_of_constantCoeff_zero hb
  unfold endP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_lin X hlg M ha)) hB]
  congr 1
  funext x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hB, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, coe_substAlgHom hB, subst_comp_subst_apply hA hB]

theorem cc_pair {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  exacts [ha _, hb _]

theorem subst_hAt {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (ha' : ∀ i, constantCoeff (a' i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) :
    subst b (hAt X a a') = hAt X (fun k => subst b (a k)) (fun k => subst b (a' k)) := by
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_pair ha ha'))
    (hasSubst_of_constantCoeff_zero hb)]
  congr 1
  funext p
  split_ifs <;> rfl

theorem hAt_zero_left (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {b : κ → MvPowerSeries τ C} (hb : ∀ i, constantCoeff (b i) = 0) : hAt X (fun _ => 0) b = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 0} (cc_pair (fun _ => map_zero _) hb) ?_ hh)
  intro s hs ν _
  have h0 : s.1 = 0 := hs
  rw [if_pos h0, map_zero]

theorem hAt_zero_right (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → coeff e X.h = 0) {τ : Type}
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) : hAt X a (fun _ => 0) = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 1} (cc_pair ha (fun _ => map_zero _)) ?_ hh)
  intro s hs ν _
  have h1 : s.1 = 1 := hs
  rw [if_neg (by rw [h1]; decide), map_zero]

theorem cc_hAt (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (cc_pair ha hb), ← coeff_zero_eq_constantCoeff_apply]
  exact hh 0 (by simp)

end General

section Square

variable {dd : ℕ}

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun k => a (col, k)) f := by
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext k
  rw [subst_X hA]

variable {d d' : ℕ} {I I' : Fin 2 → Type} (X : RawChart C d I (Fin dd)) (Z : RawChart C d' I' (Fin 2 × Fin dd))

theorem matrixEnd_block (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2)) (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2))
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0) (r s : Fin 2)
    (M : Matrix (Fin dd) (Fin dd) C) {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (col : Fin 2) (i : Fin dd) :
    endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0) a (col, i) =
      if col = r then endP X M (fun k => a (s, k)) i else 0 := by
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  unfold endP
  rw [hex, subst_inCol (cc_lin Z hZ _ ha)]
  split_ifs with hc
  · congr 1
    funext k
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hlg, subst_inCol ha]
      simp [hc]
    · intro t _ ht
      simp [ht]
    · simp
  · simp only [Matrix.of_apply, hc, false_and, if_false, zero_smul, Finset.sum_const_zero]
    exact subst_zero' (hex0 i)

theorem hAt_square (hh : Z.h = ∑ col, hCol col X.h) {τ : Type} {a b : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    hAt Z a b = ∑ col, hAt X (fun k => a (col, k)) (fun k => b (col, k)) := by
  have hA := hasSubst_of_constantCoeff_zero (cc_pair ha hb)
  unfold hAt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hh, ← coe_substAlgHom hA, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [coe_substAlgHom hA, hCol,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext q
  rw [subst_X hA]

theorem isEnd_block_raw [CharZero C] (V : VF C) (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2))
    (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2)) (hh : Z.h = ∑ col, hCol col X.h)
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0)
    (hax : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0)
    (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C) (H : IsEnd X V M M') :
    IsEnd Z V (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  have hint : ∀ (r s : Fin 2) (M : Matrix (Fin dd) (Fin dd) C),
      (∀ i, IntS V (endP X M (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) i)) →
      ∀ x, IntS V (endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
        (MvPowerSeries.X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) x) := by
    rintro r s M hM ⟨col, i⟩
    rw [matrixEnd_block X Z hlg hex hlg0 hex0 r s M (fun _ => constantCoeff_X _)]
    split_ifs
    · have hb : ∀ k : Fin dd, constantCoeff (MvPowerSeries.X (s, k) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 :=
        fun _ => constantCoeff_X _
      have h1 := intS_subst hb (fun _ => intS_X _) (hM i)
      rw [subst_endP X hlg0 M (fun _ => constantCoeff_X _) hb] at h1
      simpa only [subst_X (hasSubst_of_constantCoeff_zero hb)] using h1
    · exact intS_zero
  refine ⟨hint r s M H.1, hint s r M' H.2.1, ?_⟩
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  have hZ' : ∀ x, constantCoeff (Z.ex x) = 0 := fun x => by
    rw [hex, inCol, cc_subst (fun _ => constantCoeff_X _), hex0]
  have hg : ∀ (κ : Type) (j : Fin 2) (x : κ), constantCoeff (gp C κ j x) = 0 := fun _ _ _ => constantCoeff_X _
  have hb : ∀ q : Fin 2 × Fin dd, constantCoeff (MvPowerSeries.X (q.1, (if q.1 = 0 then s else r, q.2)) :
      MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C) = 0 := fun _ => constantCoeff_X _
  have hB := hasSubst_of_constantCoeff_zero hb
  have h1 := intS_subst hb (fun _ => intS_X _) H.2.2
  rw [RowVal.subst_mvExp hb (by
      rw [map_sub, cc_hAt X (hax 0) (cc_endP X hlg0 hex0 M (hg _ 0)) (hg _ 1),
        cc_hAt X (hax 0) (hg _ 0) (cc_endP X hlg0 hex0 M' (hg _ 1)), sub_zero]),
    subst_sub hB, subst_hAt X (cc_endP X hlg0 hex0 M (hg _ 0)) (hg _ 1) hb,
    subst_hAt X (hg _ 0) (cc_endP X hlg0 hex0 M' (hg _ 1)) hb] at h1
  simp only [subst_endP X hlg0 _ (hg _ _) hb] at h1
  simp only [gp, subst_X hB, if_true, one_ne_zero, if_false] at h1
  rw [hAt_square X Z hh (cc_endP Z hZ hZ' _ (hg _ 0)) (hg _ 1),
    hAt_square X Z hh (hg _ 0) (cc_endP Z hZ hZ' _ (hg _ 1)),
    Finset.sum_eq_single r, Finset.sum_eq_single s]
  · simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_true]
    exact h1
  · intro t _ ht
    simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_neg ht]
    exact hAt_zero_right X (hax 1) (fun _ => hg _ _ _)
  · simp
  · intro t _ ht
    simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_neg ht]
    exact hAt_zero_left X (hax 0) (fun _ => hg _ _ _)
  · simp

end Square

theorem isEnd_block : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] (p : SelfData Y d I0) (d' : ℕ) (I : Fin 2 → Type)
    (X : RawChart C d' I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h →
    ∀ (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C), IsEnd X V M M' →
    IsEnd (Y.rawSelf p) V
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  intro C _ _ V O _ _ dd Y d I0 _ p d' I X hlg hex hh r s M M' H
  refine isEnd_block_raw X (Y.rawSelf p) V (fun x => by rw [hlg]; rfl) (fun x => by rw [hex]; rfl)
    (by rw [hh]; rfl) (fun i => ?_) (fun i => ?_) (fun g => ?_) r s M M' H
  · rw [hlg]
    show constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp),
      coeff_zero_eq_constantCoeff_apply, constantCoeff_X]
  · rw [hex]
    show constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  · rw [hh]
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl

end GlobalTheory.RowLaw.EndBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeAdjointEndPairElementaryBlockStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeAdjointEndPair_elementaryBlock : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] (p : SelfData Y d I0) (d' : ℕ) (I : Fin 2 → Type) (X : RawChart C d' I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C), IsEnd X V M M' → IsEnd (Y.rawSelf p) V (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0) (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  first | exact @GlobalTheory.RowLaw.EndBlock.isEnd_block | exact GlobalTheory.RowLaw.EndBlock.isEnd_block | (intros; apply GlobalTheory.RowLaw.EndBlock.isEnd_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAdd
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowVal MvPowerSeries

namespace GlobalTheory.RowLaw.EndSum

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ]
  {X : RawChart C d I κ} {V : VF C}

theorem pair_cc {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  · exact ha _
  · exact hb _

theorem gp_cc {n : ℕ} (j : Fin n) (x : κ) : constantCoeff (gp C κ j x) = 0 := constantCoeff_X _

theorem lg_cc (h : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, h.lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply,
    constantCoeff_X]

theorem h_cc (h : RLaw X V) : constantCoeff X.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h.axes 0 0 (by simp)

theorem sum_cc (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (subst a (X.lg x) + subst b (X.lg x)) = 0 := by
  rw [map_add (f := _), cc_subst ha, cc_subst hb, lg_cc h, add_zero]

theorem lin_cc (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [smul_eq_C_mul, map_mul, cc_subst ha, lg_cc h, mul_zero]

theorem formalAdd_constantCoeff (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (addP X a b x) = 0 := by
  unfold addP
  rw [cc_subst (sum_cc h ha hb), h.exc]

theorem constantCoeff_expMulLog (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) : constantCoeff (endP X M a x) = 0 := by
  unfold endP
  rw [cc_subst (lin_cc h M ha), h.exc]

theorem hAt_cc (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) :
    constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (pair_cc ha hb), h_cc h]

theorem subst_addP (h : RLaw X V) {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (addP X a b x) = addP X (fun y => subst c (a y)) (fun y => subst c (b y)) x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (sum_cc h ha hb)) hS]
  congr 1
  funext y
  rw [subst_add hS, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hS,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hS]

theorem subst_hAt {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (hAt X a b) = hAt X (fun y => subst c (a y)) (fun y => subst c (b y)) := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (pair_cc ha hb)) hS]
  congr 1
  funext p
  split_ifs <;> rfl

theorem subst_endP_X (h : RLaw X V) (M : Matrix κ κ C) {ρ : Type}
    {c : κ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C) x) = endP X M c x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold endP
  rw [subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero (lin_cc h M (fun s => constantCoeff_X s))) hS]
  congr 1
  funext y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [coe_substAlgHom hS, subst_smul hS, subst_self]
  rfl

theorem lg_endP (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (i : κ) :
    subst (endP X M a) (X.lg i) = ∑ y, M i y • subst a (X.lg y) := by
  have hS := hasSubst_of_constantCoeff_zero (lin_cc h M ha)
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h.exc) hS (X.lg i)
  rw [h.lgex, subst_X hS] at this
  exact this.symm

theorem matrixEnd_add (h : RLaw X V) (M N : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : endP X (M + N) a = addP X (endP X M a) (endP X N a) := by
  funext i
  unfold addP
  simp only [lg_endP h _ ha]
  unfold endP
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem formalAdd_integral (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (x : κ) : IntS V (addP X a b x) := by
  have hc := pair_cc ha hb
  have hS := hasSubst_of_constantCoeff_zero hc
  have h1 := intS_subst hc (fun p => by split_ifs; exacts [hai _, hbi _]) (h.addInt x)
  rw [subst_addP h (gp_cc 0) (gp_cc 1) hc] at h1
  simpa [gp, subst_X hS] using h1

theorem defects [CharZero C] (h : RLaw X V) {τ : Type} {a b c : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (hc : ∀ s, constantCoeff (c s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (hci : ∀ s, IntS V (c s)) :
    hAt X a c + hAt X b c - hAt X (addP X a b) c ∈ logInt V τ ∧
      hAt X a b + hAt X a c - hAt X a (addP X b c) ∈ logInt V τ := by
  let e : Fin 3 × κ → MvPowerSeries τ C := fun p => (![a, b, c] : Fin 3 → κ → MvPowerSeries τ C) p.1 p.2
  have he : ∀ p, constantCoeff (e p) = 0 := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [ha x, hb x, hc x]
  have hei : ∀ p, IntS V (e p) := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [hai x, hbi x, hci x]
  have hS := hasSubst_of_constantCoeff_zero he
  have s0 : (fun x => subst e (gp C κ (0 : Fin 3) x)) = a := funext fun x => subst_X hS _
  have s1 : (fun x => subst e (gp C κ (1 : Fin 3) x)) = b := funext fun x => subst_X hS _
  have s2 : (fun x => subst e (gp C κ (2 : Fin 3) x)) = c := funext fun x => subst_X hS _
  have g := fun j : Fin 3 => gp_cc (C := C) (κ := κ) j
  constructor
  · have h1 := logInt_subst he hei (mem_logInt.2 ⟨by
      rw [map_sub, map_add (f := _), hAt_cc h (g 0) (g 2), hAt_cc h (g 1) (g 2), hAt_cc h (formalAdd_constantCoeff h (g 0) (g 1)) (g 2)]
      simp, h.ph1⟩)
    rw [subst_sub hS, subst_add hS, subst_hAt (g 0) (g 2) he, subst_hAt (g 1) (g 2) he,
      subst_hAt (formalAdd_constantCoeff h (g 0) (g 1)) (g 2) he, funext (subst_addP h (g 0) (g 1) he), s0, s1, s2] at h1
    exact h1
  · have h1 := logInt_subst he hei (mem_logInt.2 ⟨by
      rw [map_sub, map_add (f := _), hAt_cc h (g 0) (g 1), hAt_cc h (g 0) (g 2), hAt_cc h (g 0) (formalAdd_constantCoeff h (g 1) (g 2))]
      simp, h.ph2⟩)
    rw [subst_sub hS, subst_add hS, subst_hAt (g 0) (g 1) he, subst_hAt (g 0) (g 2) he,
      subst_hAt (g 0) (formalAdd_constantCoeff h (g 1) (g 2)) he, funext (subst_addP h (g 1) (g 2) he), s0, s1, s2] at h1
    exact h1

theorem isEnd_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C,
      IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  intro C _ V d I κ _ X h M M' N N' hM hN
  haveI := h.charZero
  have hX : ∀ s : κ, constantCoeff (MvPowerSeries.X s : MvPowerSeries κ C) = 0 := fun s => constantCoeff_X s
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_add h _ _ hX]
    exact formalAdd_integral h (constantCoeff_expMulLog h _ hX) (constantCoeff_expMulLog h _ hX) hM.1 hN.1 i
  · rw [matrixEnd_add h _ _ hX]
    exact formalAdd_integral h (constantCoeff_expMulLog h _ hX) (constantCoeff_expMulLog h _ hX) hM.2.1 hN.2.1 i
  have g := fun j : Fin 2 => gp_cc (C := C) (κ := κ) j
  have gi : ∀ (j : Fin 2) s, IntS V (gp C κ j s) := fun j s => intS_X _
  have ei : ∀ (A : Matrix κ κ C), (∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) →
      ∀ (j : Fin 2) s, IntS V (endP X A (gp C κ j) s) := fun A hA j s => by
    rw [← subst_endP_X h A (g j)]
    exact intS_subst (g j) (gi j) (hA s)
  have ad : ∀ A A' : Matrix κ κ C, IsEnd X V A A' →
      hAt X (endP X A (gp C κ (0 : Fin 2))) (gp C κ 1) - hAt X (gp C κ 0) (endP X A' (gp C κ 1)) ∈
        logInt V (Fin 2 × κ) := fun A A' hA =>
    mem_logInt.2 ⟨by
      rw [map_sub, hAt_cc h (constantCoeff_expMulLog h _ (g 0)) (g 1), hAt_cc h (g 0) (constantCoeff_expMulLog h _ (g 1)), sub_zero], hA.2.2⟩
  have d1 := (defects h (constantCoeff_expMulLog h M (g 0)) (constantCoeff_expMulLog h N (g 0)) (g 1) (ei M hM.1 0) (ei N hN.1 0) (gi 1)).1
  have d2 := (defects h (g 0) (constantCoeff_expMulLog h M' (g 1)) (constantCoeff_expMulLog h N' (g 1)) (gi 0) (ei M' hM.2.1 1)
    (ei N' hN.2.1 1)).2
  have key := add_mem (sub_mem (add_mem (ad M M' hM) (ad N N' hN)) d1) d2
  rw [matrixEnd_add h M N (g 0), matrixEnd_add h M' N' (g 1)]
  convert (mem_logInt.1 key).2 using 2
  ring

end GlobalTheory.RowLaw.EndSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAddStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGaugeAdjointIntegralEndPair_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C, IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  first | exact @GlobalTheory.RowLaw.EndSum.isEnd_add | exact GlobalTheory.RowLaw.EndSum.isEnd_add | (intros; apply GlobalTheory.RowLaw.EndSum.isEnd_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlace
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ProjSelf

variable {C : Type} [Field C] {V : VF C}

theorem eq_zero_of_ge {x : C} (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  by_contra hx
  have hne : V.v x ≠ ⊤ := fun e => hx ((AddValuation.top_iff _).1 e)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have := h N
  unfold VF.Ge at this
  rw [← ht] at this
  have h2 : (N : ℝ) ≤ t := by exact_mod_cast this
  linarith

theorem exists_lower {κ : Type} [Fintype κ] (v : κ → C) : ∃ m : ℕ, ∀ i, V.Ge (-(m : ℝ)) (v i) := by
  have h1 : ∀ x : C, ∃ m : ℕ, V.Ge (-(m : ℝ)) x := by
    intro x
    unfold VF.Ge
    induction V.v x using WithTop.recTopCoe with
    | top => exact ⟨0, le_top⟩
    | coe t =>
      obtain ⟨N, hN⟩ := exists_nat_gt (-t)
      refine ⟨N, ?_⟩
      have : -(N : ℝ) ≤ t := by linarith
      exact_mod_cast this
  choose f hf using fun i => h1 (v i)
  refine ⟨∑ i, f i, fun i => (hf i).mono ?_⟩
  have : f i ≤ ∑ i, f i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have : (f i : ℝ) ≤ ((∑ i, f i : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem ge_mulVec {κ : Type} [Fintype κ] {A : Matrix κ κ C} (hA : ∀ i j, V.Ge 0 (A i j)) {m : ℝ} {v : κ → C}
    (hv : ∀ i, V.Ge m (v i)) (i : κ) : V.Ge m (A.mulVec v i) :=
  VF.Ge.sum fun j _ => (hA i j).mul_int (hv j)

theorem ge_l_pow (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one (V := V)
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul (VF.ge_l (V := V))
    push_cast
    exact this

theorem ge_of_unit_mul {u x : C} {m : ℝ} (hu : V.v u = 0) (h : V.Ge m (u * x)) : V.Ge m x := by
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, hu, zero_add] at h

theorem v_eq_zero_of_mm {t : C} (h : V.MM (t - 1)) : V.v t = 0 := by
  have e : t = 1 + (t - 1) := by ring
  rw [e, AddValuation.map_add_eq_of_lt_left _ (by rw [V.v.map_one]; exact h), V.v.map_one]

section Lim

variable {O : Type} [CommRing O] {κ : Type} [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C)

def IsLim (V : VF C) (L : O →+* Matrix κ κ C) (M : Matrix κ κ C) (a : ℕ → O) : Prop :=
  ∀ (N : ℕ) (v : κ → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - (L (a n)).mulVec v i)

theorem IsLim.eig {M : Matrix κ κ C} {a : ℕ → O} (h : IsLim V L M a) (ψ : O →+* C) (c : C)
    (hc : ∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (c - ψ (a n))) {w : κ → C} (hw0 : ∀ i, V.Ge 0 (w i))
    (hw : ∀ x, (L x).mulVec w = ψ x • w) : M.mulVec w = c • w := by
  funext i
  rw [← sub_eq_zero]
  apply eq_zero_of_ge (V := V)
  intro N
  obtain ⟨n0, h0⟩ := h N w i
  obtain ⟨n1, h1⟩ := hc N
  have a1 := h0 (n0 + n1) (by omega)
  have a2 := (hw0 i).mul_int (h1 (n0 + n1) (by omega))
  rw [hw] at a1
  have := a1.sub a2
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem IsLim.absorb (hL : ∀ x i j, V.Ge 0 (L x i j)) {M E : Matrix κ κ C} {a e : ℕ → O} (h : IsLim V L M a)
    (hE : IsLim V L E e) (hae : ∀ n, ∃ y, e n * a n - a n = (V.l : O) ^ n * y) (v : κ → C) :
    M.mulVec v = M.mulVec (E.mulVec v) := by
  funext i
  rw [← sub_eq_zero]
  apply eq_zero_of_ge (V := V)
  intro N
  obtain ⟨m, hm⟩ := exists_lower (V := V) v
  obtain ⟨n0, h0⟩ := h N v i
  obtain ⟨n1, h1⟩ := h N (E.mulVec v) i
  choose n2 h2 using hE N v
  set n := n0 + n1 + (∑ j, n2 j) + N + m with hn
  have a0 := h0 n (by omega)
  have a1 := h1 n (by omega)
  have a2 : ∀ j, V.Ge N ((E.mulVec v - (L (e n)).mulVec v) j) := fun j => h2 j n (by
    have : n2 j ≤ ∑ j, n2 j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega)
  have a3 := ge_mulVec (hL (a n)) a2 i
  obtain ⟨y, hy⟩ := hae n
  have a4 : V.Ge N ((V.l : C) ^ n * (L y).mulVec v i) := by
    refine ((ge_l_pow n).mul (ge_mulVec (hL y) hm i)).mono ?_
    have : N + m ≤ n := by omega
    have : (N : ℝ) + m ≤ n := by exact_mod_cast this
    linarith
  have e1 : (V.l : C) ^ n * (L y).mulVec v i = (L (a n)).mulVec ((L (e n)).mulVec v) i - (L (a n)).mulVec v i := by
    have h3 := congrArg (fun z => (L z).mulVec v i) hy
    simp only [map_sub, map_mul, map_pow, map_natCast, Matrix.sub_mulVec, Pi.sub_apply] at h3
    have h4 : (V.l : Matrix κ κ C) ^ n * L y = ((V.l : C) ^ n) • L y := by
      rw [← Nat.cast_pow, ← Nat.cast_pow, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm (a n), map_mul, h3, h4, Matrix.smul_mulVec, Pi.smul_apply,
      smul_eq_mul]
  rw [e1] at a4
  rw [Matrix.mulVec_sub, Pi.sub_apply] at a3
  have := ((a0.sub a1).sub a3).sub a4
  convert this using 1
  ring

end Lim

section Seq

variable {O : Type} [CommRing O]

theorem idem_pow {l : ℕ} {ε : O} (h : ∃ y, ε * ε - ε = (l : O) * y) (k : ℕ) : (l : O) ∣ ε ^ (k + 1) - ε := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨y, hy⟩ := h
    have e : ε ^ (k + 1 + 1) - ε = ε * (ε ^ (k + 1) - ε) + (ε * ε - ε) := by ring
    rw [e, hy]
    exact (ih.mul_left _).add (dvd_mul_right _ _)

theorem pow_kill {ι : Type} (em : ι → (O →+* C)) (hint : ∀ a x, V.Ge 0 (em a x)) {ε : O}
    (hP : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) (n : ℕ) :
    ∀ x : O, (∀ a, V.Ge n (em a x)) → (V.l : O) ^ n ∣ ε ^ n * x := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    obtain ⟨y, hy⟩ := hP x fun a => lt_of_lt_of_le (by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      exact_mod_cast this) (hx a)
    have hy' : ∀ a, V.Ge n (em a y) := by
      intro a
      have h1 := (hint a ε).mul_int (hx a)
      rw [← map_mul, hy, map_mul, map_natCast] at h1
      refine h1.of_l_mul.mono ?_
      push_cast
      linarith
    obtain ⟨z, hz⟩ := ih y hy'
    refine ⟨z, ?_⟩
    calc ε ^ (n + 1) * x = ε ^ n * (ε * x) := by ring
      _ = (V.l : O) * (ε ^ n * y) := by rw [hy]; ring
      _ = _ := by rw [hz]; ring

end Seq

section Seq2

variable {O : Type} [CommRing O] {ι : Type} (em : ι → (O →+* C))

theorem idem_lift {l : ℕ} {ε : O} (h : ∃ y, ε * ε - ε = (l : O) * y) (n : ℕ) :
    (l : O) ^ n ∣ ε ^ (l ^ n) * ε ^ (l ^ n) - ε ^ (l ^ n) := by
  obtain ⟨y, hy⟩ := h
  have h1 := dvd_sub_pow_of_dvd_sub (p := l) (a := ε * ε) (b := ε) ⟨y, hy⟩ n
  rw [mul_pow] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

theorem idem_cauchy {ε : O} (h : ∃ y, ε * ε - ε = (V.l : O) * y) (n : ℕ) :
    (V.l : O) ^ n ∣ ε ^ (V.l ^ (n + 1)) - ε ^ (V.l ^ n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
  have h0 := idem_pow h k
  rw [← Nat.succ_eq_add_one, ← hk] at h0
  have h1 := dvd_sub_pow_of_dvd_sub h0 n
  rw [← pow_mul, ← pow_succ'] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

theorem em_idem (ψ : O →+* C) (hint : ∀ x, V.Ge 0 (ψ x)) {ε : O} (h : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h1 : V.MM (ψ ε - 1)) (n : ℕ) : V.Ge n (ψ (ε ^ (V.l ^ n)) - 1) := by
  obtain ⟨y, hy⟩ := idem_lift h n
  have h2 := congrArg ψ hy
  have hu : V.v (ψ (ε ^ (V.l ^ n))) = 0 := by
    rw [map_pow, V.v.map_pow, v_eq_zero_of_mm h1, smul_zero]
  apply ge_of_unit_mul hu
  rw [map_sub, map_mul, map_mul, map_pow ψ (V.l : O), map_natCast] at h2
  rw [mul_sub, mul_one, h2]
  simpa using (ge_l_pow n).mul (hint y)

theorem exists_seq (hint : ∀ a x, V.Ge 0 (em a x)) {ε : O} (h : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h1 : ∀ a, V.MM (em a ε - 1)) (hP : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y)
    (φ : ι → C) (hφ : ∀ N : ℕ, ∃ x : O, ∀ a, V.Ge N (φ a - em a x)) :
    ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ n, ε ^ (V.l ^ n) ∣ s n) ∧
      ∀ a (N : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge N (φ a - em a (s n)) := by
  choose x hx using hφ
  refine ⟨fun n => ε ^ (V.l ^ n) * x n, fun n => ?_, fun n => dvd_mul_right _ _, fun a N => ⟨N, fun n hn => ?_⟩⟩
  · have h2 : (V.l : O) ^ n ∣ ε ^ n * (x (n + 1) - x n) := by
      refine pow_kill em hint hP n _ fun a => ?_
      have := (hx n a).sub ((hx (n + 1) a).mono (by push_cast; linarith))
      convert this using 1
      rw [map_sub]
      ring
    have h3 : n ≤ V.l ^ n := (Nat.lt_pow_self V.l_prime.one_lt).le
    have h4 : (V.l : O) ^ n ∣ ε ^ (V.l ^ n) * (x (n + 1) - x n) :=
      h2.trans (mul_dvd_mul_right (pow_dvd_pow _ h3) _)
    have h5 := ((idem_cauchy h n).mul_right (x (n + 1))).add h4
    have e : ε ^ (V.l ^ (n + 1)) * x (n + 1) - ε ^ (V.l ^ n) * x n =
      (ε ^ V.l ^ (n + 1) - ε ^ V.l ^ n) * x (n + 1) + ε ^ V.l ^ n * (x (n + 1) - x n) := by ring
    show (V.l : O) ^ n ∣ ε ^ (V.l ^ (n + 1)) * x (n + 1) - ε ^ (V.l ^ n) * x n
    rw [e]
    exact h5
  · have h2 := (hx n a).sub ((hint a (x n)).mul_int (em_idem (em a) (hint a) h (h1 a) n))
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    refine VF.Ge.mono ?_ hn'
    convert h2 using 1
    rw [map_mul]
    ring

end Seq2

section Blocks

variable {κ : Type} [Fintype κ]

def blk (r s : Fin 2) (M : Matrix κ κ C) : Matrix (Fin 2 × κ) (Fin 2 × κ) C :=
  Matrix.of fun x y : Fin 2 × κ => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0

theorem blk_mulVec (r s : Fin 2) (M : Matrix κ κ C) (v : Fin 2 × κ → C) (x : Fin 2 × κ) :
    (blk r s M).mulVec v x = if x.1 = r then M.mulVec (fun j => v (s, j)) x.2 else 0 := by
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.of_apply, Fintype.sum_prod_type]
  by_cases h : x.1 = r
  · simp only [h, true_and, if_true]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · simp [h]

def blks (M : Fin 2 → Fin 2 → Matrix κ κ C) : Matrix (Fin 2 × κ) (Fin 2 × κ) C :=
  (blk 0 0 (M 0 0) + blk 0 1 (M 0 1)) + (blk 1 0 (M 1 0) + blk 1 1 (M 1 1))

theorem blks_mulVec (M : Fin 2 → Fin 2 → Matrix κ κ C) (v : Fin 2 × κ → C) (x : Fin 2 × κ) :
    (blks M).mulVec v x = ∑ s, (M x.1 s).mulVec (fun j => v (s, j)) x.2 := by
  obtain ⟨r, i⟩ := x
  simp only [blks, Matrix.add_mulVec, Pi.add_apply, blk_mulVec, Fin.sum_univ_two]
  fin_cases r <;> simp

end Blocks

section Main

variable [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

theorem exists_lin : ∃ L : O →+* Matrix (Fin dd) (Fin dd) C,
    (∀ x v, (L x).mulVec v = linAct (Y.B.A.act x) v) ∧ ∀ x i j, V.Ge 0 (L x i j) := by
  have e : ∀ x i j, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dActH C Y.B x i j =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act x i) := by
    intro x i j
    show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (MvPowerSeries.map (algebraMap C C) (Y.B.A.act x i)) = _
    rw [MvPowerSeries.coeff_map]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dActH C Y.B, fun x v => ?_, fun x i j => ?_⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, e, linAct]
  · rw [e]
    exact Y.intAct x i _

variable {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

noncomputable def rawOne : RawChart C 0 (fun _ => Empty) (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := 0
  u := fun _ c => c.elim
  ty := fun _ c => c.elim
  n := 0
  j := 0
  j' := 0
  big := fun _ _ => True

theorem isEnd_blks (M M' : Fin 2 → Fin 2 → Matrix (Fin dd) (Fin dd) C)
    (h : ∀ r s, IsEnd (rawOne Y) V (M r s) (M' s r)) : IsEnd (Y.rawSelf p) V (blks M) (blks M') := by
  have hR := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p
  have hb : ∀ r s, IsEnd (Y.rawSelf p) V (blk r s (M r s)) (blk s r (M' s r)) := fun r s =>
    GlobalTheory.T.gaugeAdjointEndPair_elementaryBlock C V O dd Y d I0 p 0 _ (rawOne Y) rfl rfl rfl r s _ _ (h r s)
  have ha := GlobalTheory.T.isGaugeAdjointIntegralEndPair_add C V d _ _ (Y.rawSelf p) hR
  have := ha _ _ _ _ (ha _ _ _ _ (hb 0 0) (hb 0 1)) (ha _ _ _ _ (hb 1 0) (hb 1 1))
  have e : blks M' = blk 0 0 (M' 0 0) + blk 1 0 (M' 1 0) + (blk 0 1 (M' 0 1) + blk 1 1 (M' 1 1)) := by
    unfold blks
    abel
  rw [e]
  exact this

theorem exists_pair : ∃ b : (Fin dd → C) → I0 → C, ∀ φ : ZMod d → C,
    (∀ N : ℕ, ∃ x : O, ∀ a, V.Ge N (φ a - p.em a x)) →
    ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (rawOne Y) V M M' ∧ IsEnd (rawOne Y) V M' M ∧
      (∀ c, M.mulVec (p.e c) = φ (p.ty0 c) • p.e c) ∧ (∀ c, M'.mulVec (p.e c) = φ (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v, M.mulVec v = M.mulVec (∑ c, b v c • p.e c)) ∧ ∀ v, M'.mulVec v = M'.mulVec (∑ c, b v c • p.e c) := by
  have := Y.algClosed
  obtain ⟨L, hL, hLi⟩ := exists_lin Y
  obtain ⟨ε, h0, h1, hP⟩ := p.em_unr
  obtain ⟨E, -, -, -, hE, -⟩ := GlobalTheory.T.exists_integralEnd_of_ladic_action_limit C V O dd Y 0 _ (rawOne Y) rfl rfl rfl (fun n => ε ^ (V.l ^ n))
    (idem_cauchy h0)
  simp only [← hL] at hE
  have hb : ∀ v, ∃ b : I0 → C, E.mulVec v = ∑ c, b c • p.e c := by
    intro v
    obtain ⟨w, hw, hv⟩ := GlobalTheory.T.limitIdempotent_range_le_sum_eigenspaces C V O (Fin dd) L hLi d p.em p.em_int p.em_frob ε h0 hP E hE v
    choose b _ hb using fun a => p.e_full a (w a) fun x => by rw [← hL, hw]
    refine ⟨fun c => ∑ a, b a c, ?_⟩
    rw [hv]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => hb a
  choose b hb using hb
  refine ⟨b, fun φ hφ => ?_⟩
  obtain ⟨s, hs, hsd, hsl⟩ := exists_seq p.em p.em_int h0 h1 hP φ hφ
  obtain ⟨M, M', e1, e2, hM, hM'⟩ := GlobalTheory.T.exists_integralEnd_of_ladic_action_limit C V O dd Y 0 _ (rawOne Y) rfl rfl rfl s hs
  simp only [← hL] at hM hM'
  have hst : (V.l : O) ∣ ε * star ε - star ε := by
    obtain ⟨y, hy⟩ := hP (1 - star ε) fun a => by
      have := h1 (a + p.hd)
      unfold VF.MM at this ⊢
      rw [map_sub, map_one, p.em_conj, ← V.v.map_neg, neg_sub]
      exact this
    refine ⟨-star y, ?_⟩
    have h2 := congrArg star hy
    simp only [star_mul', star_sub, star_one, star_star, star_natCast] at h2
    linear_combination -h2
  refine ⟨M, M', e1, e2, fun c => ?_, fun c => ?_, fun v => ?_, fun v => ?_⟩
  · exact IsLim.eig L (a := s) hM (p.em (p.ty0 c)) _ (hsl _) (p.e_int c) fun x => by rw [hL, p.e_eig]
  · refine IsLim.eig L (a := fun n => star (s n)) hM' (p.em (p.ty0 c)) _ ?_ (p.e_int c) fun x => by
      rw [hL, p.e_eig]
    simp only [p.em_conj]
    exact hsl _
  · rw [← hb]
    refine IsLim.absorb L hLi (a := s) (e := fun n => ε ^ (V.l ^ n)) hM hE (fun n => ?_) v
    obtain ⟨z, hz⟩ := hsd n
    show (V.l : O) ^ n ∣ ε ^ (V.l ^ n) * s n - s n
    rw [hz, ← mul_assoc, ← sub_mul]
    exact (idem_lift h0 n).mul_right _
  · rw [← hb]
    refine IsLim.absorb L hLi (a := fun n => star (s n)) (e := fun n => ε ^ (V.l ^ n)) hM' hE (fun n => ?_) v
    obtain ⟨z, hz⟩ := hsd n
    show (V.l : O) ^ n ∣ ε ^ (V.l ^ n) * star (s n) - star (s n)
    rw [hz, star_mul', star_pow, ← mul_assoc, ← sub_mul, ← mul_pow]
    exact ((pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub hst n)).mul_right _

end Main

theorem hasProj_of {d : ℕ} {I0 κ : Type} [Fintype I0] [Fintype κ] (X : RawChart C d (fun _ => I0) κ)
    (A B : Matrix κ κ C) (h1 : IsEnd X V A B) (h2 : IsEnd X V B A)
    (a0 : ∀ c, A.mulVec (X.u 0 c) = X.u 0 c) (b1 : ∀ c, B.mulVec (X.u 1 c) = X.u 1 c)
    (a1 : ∀ c, A.mulVec (X.u 1 c) = 0) (b0 : ∀ c, B.mulVec (X.u 0 c) = 0)
    (ra : ∀ v, ∃ b : I0 → C, A.mulVec v = ∑ c, b c • X.u 0 c)
    (rb : ∀ v, ∃ b : I0 → C, B.mulVec v = ∑ c, b c • X.u 1 c) : HasProj X V :=
  ⟨![A, B], h1, h2, Fin.forall_fin_two.2 ⟨a0, b1⟩, Fin.forall_fin_two.2 ⟨a1, b0⟩, Fin.forall_fin_two.2 ⟨ra, rb⟩⟩

theorem hasProj_self : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), HasProj (Y.rawSelf p) V := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  obtain ⟨b, hb⟩ := exists_pair Y p
  have hgi : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨G, hG⟩ := p.gm_lim 0
    have := (hG a r s).add (by simpa using p.em_int a (G r s))
    simpa using this
  have hφ : ∀ r s : Fin 2, ∀ N : ℕ, ∃ x : O, ∀ a, V.Ge N (p.gm a r 0 * p.gm (a + p.hd) s 1 - p.em a x) := by
    intro r s N
    obtain ⟨G, hG⟩ := p.gm_lim N
    refine ⟨G r 0 * star (G s 1), fun a => ?_⟩
    have := ((hgi a r 0).mul_int (hG (a + p.hd) s 1)).add
      ((p.em_int (a + p.hd) (G s 1)).mul_int (hG a r 0))
    convert this using 1
    rw [map_mul, p.em_conj]
    ring
  choose M M' e1 e2 hM hM' hv hv' using fun r s : Fin 2 =>
    hb (fun a => p.gm a r 0 * p.gm (a + p.hd) s 1) (hφ r s)
  have hu : ∀ g c x, (Y.rawSelf p).u g c x = p.gm (p.ty0 c) x.1 g * p.e c x.2 := fun _ _ _ => rfl
  have hcol : ∀ g c s, (fun j => (Y.rawSelf p).u g c (s, j)) = p.gm (p.ty0 c) s g • p.e c := fun _ _ _ => rfl
  have k0 : ∀ g c, (blks M).mulVec ((Y.rawSelf p).u g c) = (if 1 = g then (0 : C) else 1) • (Y.rawSelf p).u 0 c := by
    intro g c
    funext x
    rw [blks_mulVec, ← p.gm_hyp (p.ty0 c) 1 g, Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hcol, Matrix.mulVec_smul, hM]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have k1 : ∀ g c, (blks fun s r => M' r s).mulVec ((Y.rawSelf p).u g c) =
      (if 0 = g then (0 : C) else 1) • (Y.rawSelf p).u 1 c := by
    intro g c
    funext x
    rw [blks_mulVec, ← p.gm_hyp (p.ty0 c) 0 g, Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hcol, Matrix.mulVec_smul, hM', add_assoc, p.hd_two, add_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have i1 : IsEnd (Y.rawSelf p) V (blks M) (blks fun s r => M' r s) :=
    isEnd_blks Y p M (fun s r => M' r s) e1
  have i2 : IsEnd (Y.rawSelf p) V (blks fun s r => M' r s) (blks M) :=
    isEnd_blks Y p (fun s r => M' r s) M fun r s => e2 s r
  refine hasProj_of _ _ _ i1 i2 (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_) ?_ ?_
  · rw [k0, if_neg (by decide), one_smul]
  · rw [k1, if_neg (by decide), one_smul]
  · rw [k0, if_pos rfl, zero_smul]
  · rw [k1, if_pos rfl, zero_smul]
  · intro v
    refine ⟨fun c => ∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 1, ?_⟩
    funext x
    show (blks M).mulVec v x = (∑ c, (∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 1) •
      (Y.rawSelf p).u 0 c) x
    rw [blks_mulVec, Finset.sum_apply]
    simp only [Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hv, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, hM]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro v
    refine ⟨fun c => ∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 0, ?_⟩
    funext x
    show (blks fun s r => M' r s).mulVec v x = (∑ c, (∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 0) •
      (Y.rawSelf p).u 1 c) x
    rw [blks_mulVec, Finset.sum_apply]
    simp only [Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hv', Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, hM', add_assoc, p.hd_two, add_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.ProjSelf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlaceStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), HasProj (Y.rawSelf p) V := by
  first | exact @GlobalTheory.ProjSelf.hasProj_self | exact GlobalTheory.ProjSelf.hasProj_self | (intros; apply GlobalTheory.ProjSelf.hasProj_self <;> assumption)
end

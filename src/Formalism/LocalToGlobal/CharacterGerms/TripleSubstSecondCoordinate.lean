module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieLab

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffTripleSubstitution
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieValU
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def IsIU (V : VF C) {σ : Type} (U : MvPowerSeries σ C) : Prop :=
  IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0

theorem IsIU.one {σ : Type} : IsIU V (1 : MvPowerSeries σ C) := by
  refine ⟨fun μ => ?_, ?_⟩
  · unfold VF.Ge
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · rw [AddValuation.map_one]; exact le_rfl
    · rw [AddValuation.map_zero]; exact le_top
  · rw [map_one, AddValuation.map_one]

theorem IsIU.mul {σ : Type} {U U' : MvPowerSeries σ C} (h : IsIU V U) (h' : IsIU V U') : IsIU V (U * U') :=
  ⟨IntS.mul h.1 h'.1, by rw [map_mul, AddValuation.map_mul, h.2, h'.2, add_zero]⟩

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

end Defs

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

def P2 (a b : Fin dd → MvPowerSeries τ C) : Fin 2 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def P3 (a b c : Fin dd → MvPowerSeries τ C) : Fin 3 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else if q.1 = 1 then b q.2 else c q.2

theorem constantCoeff_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]

theorem constantCoeff_triple_substitution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
    (q : Fin 3 × Fin dd) : MvPowerSeries.constantCoeff (P3 a b c q) = 0 := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]

theorem integral_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (q : Fin 2 × Fin dd) : IntS V (P2 a b q) := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]

theorem integral_triple_substitution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (hc : ∀ i, IntS V (c i)) (q : Fin 3 × Fin dd) : IntS V (P3 a b c q) := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]

theorem subst_sub' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f - g) = MvPowerSeries.subst a f - MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_sub _ f g

theorem subst_add' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f + g) = MvPowerSeries.subst a f + MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_add _ f g

theorem cc_pt {n : ℕ} (g : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd g i) = 0 := MvPowerSeries.constantCoeff_X _

theorem toK_eq {n : ℕ} (f : PS C n dd) : FB.toK C f = f := by
  unfold FB.toK
  simp

variable (Y : FBChart C V O dd)

def hAt (a b : Fin dd → MvPowerSeries τ C) : MvPowerSeries τ C := MvPowerSeries.subst (P2 a b) Y.h

def actAt (x : O) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i)

def addAt (a b : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (P2 a b) (Y.B.G.F i)

theorem cc_hAt {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : MvPowerSeries.constantCoeff (hAt Y a b) = 0 := by
  unfold hAt
  exact VP.cc_subst (constantCoeff_pair_substitution ha hb) (cc_h Y)

theorem cc_actAt (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (i : Fin dd) : MvPowerSeries.constantCoeff (actAt Y x a i) = 0 := by
  unfold actAt
  exact VP.cc_subst (fun q : Fin 1 × Fin dd => ha q.2) (Y.B.A.const x i)

theorem eval_two_points_eq_subst {n m : ℕ} (a b : Pt C n dd) (f : PS C 2 dd) (_hm : m = 2) : ev ![a, b] f = MvPowerSeries.subst (P2 a b) f := by
  unfold ev
  congr 1
  funext q
  rcases q with ⟨i, k⟩
  fin_cases i <;> simp [P2]

theorem actK_eq (x : O) (i : Fin dd) : Y.B.actK C x i = Y.B.A.act x i := by
  unfold FB.actK
  exact toK_eq _

theorem compose_one_action_eq_actAt {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.actK C x) a = actAt Y x a := by
  funext i
  simp only [comp1, ev, actAt, actK_eq, Matrix.cons_val_fin_one]

variable {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)

include ha hb

theorem pair_subst_coordinate (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.subst (P2 a b) (pt C dd g i) = P2 a b (g, i) := by
  rw [show pt C dd g i = (MvPowerSeries.X (g, i) : MvPowerSeries (Fin 2 × Fin dd) C) from rfl]
  exact VP.subst_X (constantCoeff_pair_substitution ha hb) (g, i)

theorem sy_at : MvPowerSeries.subst (P2 a b) Y.B.sy = mvExp (hAt Y b a - hAt Y a b) := by
  obtain ⟨-, -, -, -, hsy, -⟩ := Y.gauge
  rw [toK_eq] at hsy
  have hP10 : ∀ q, MvPowerSeries.constantCoeff (P2 (pt C dd 1) (pt C dd 0) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution (cc_pt 1) (cc_pt 0)
  have hswap : MvPowerSeries.subst (P2 a b) (ev ![pt C dd 1, pt C dd 0] Y.h) = hAt Y b a := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hP10 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (pt C dd 1 k) = b k
      rw [pair_subst_coordinate ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (pt C dd 0 k) = a k
      rw [pair_subst_coordinate ha hb]
      rfl
  have hcc : MvPowerSeries.constantCoeff (ev ![pt C dd 1, pt C dd 0] Y.h - Y.h) = 0 := by
    rw [map_sub, eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.cc_subst hP10 (cc_h Y), cc_h Y, sub_zero]
  rw [hsy, expS_eq _ hcc, subst_exp (constantCoeff_pair_substitution ha hb) hcc, subst_sub' (constantCoeff_pair_substitution ha hb), hswap]
  rfl

theorem actAt_pt (x : O) (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd g) i) = actAt Y x (fun j => P2 a b (g, j)) i := by
  unfold actAt
  rw [VP.subst_subst (fun q : Fin 1 × Fin dd => cc_pt g q.2) (constantCoeff_pair_substitution ha hb)]
  congr 1
  funext q
  exact pair_subst_coordinate ha hb g q.2

theorem ad_at (x : O) :
    MvPowerSeries.subst (P2 a b) (Y.B.ad x) = mvExp (hAt Y (actAt Y x a) b - hAt Y a (actAt Y (star x) b)) := by
  obtain ⟨-, -, -, -, -, had⟩ := Y.gauge
  have hx := had x
  rw [toK_eq, compose_one_action_eq_actAt Y x, compose_one_action_eq_actAt Y (star x)] at hx
  have hA0 : ∀ i, MvPowerSeries.constantCoeff (actAt Y x (pt C dd 0) i : PS C 2 dd) = 0 :=
    cc_actAt Y x (cc_pt (n := 2) 0)
  have hA1 : ∀ i, MvPowerSeries.constantCoeff (actAt Y (star x) (pt C dd 1) i : PS C 2 dd) = 0 :=
    cc_actAt Y (star x) (cc_pt (n := 2) 1)
  have hQ1 : ∀ q, MvPowerSeries.constantCoeff (P2 (actAt Y x (pt C dd 0)) (pt C dd 1) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution hA0 (cc_pt (n := 2) 1)
  have hQ2 : ∀ q, MvPowerSeries.constantCoeff (P2 (pt C dd 0) (actAt Y (star x) (pt C dd 1)) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution (cc_pt (n := 2) 0) hA1
  have e1 : MvPowerSeries.subst (P2 a b) (ev ![actAt Y x (pt C dd 0), pt C dd 1] Y.h) = hAt Y (actAt Y x a) b := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hQ1 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd 0) k) = actAt Y x a k
      rw [actAt_pt Y ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (pt C dd 1 k) = b k
      rw [pair_subst_coordinate ha hb]
      rfl
  have e2 : MvPowerSeries.subst (P2 a b) (ev ![pt C dd 0, actAt Y (star x) (pt C dd 1)] Y.h) =
      hAt Y a (actAt Y (star x) b) := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hQ2 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (pt C dd 0 k) = a k
      rw [pair_subst_coordinate ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (actAt Y (star x) (pt C dd 1) k) = actAt Y (star x) b k
      rw [actAt_pt Y ha hb]
      rfl
  have hcc : MvPowerSeries.constantCoeff (ev ![actAt Y x (pt C dd 0), pt C dd 1] Y.h -
      ev ![pt C dd (0 : Fin 2), actAt Y (star x) (pt C dd (1 : Fin 2))] Y.h) = 0 := by
    rw [map_sub, eval_two_points_eq_subst (m := 2) _ _ _ rfl, eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.cc_subst hQ1 (cc_h Y),
      VP.cc_subst hQ2 (cc_h Y), sub_zero]
  rw [hx, expS_eq _ hcc, subst_exp (constantCoeff_pair_substitution ha hb) hcc, subst_sub' (constantCoeff_pair_substitution ha hb), e1, e2]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

private theorem coeff_mul_eq_zero_of_degree_lt_add_character_germs {σ : Type} {p q : MvPowerSeries σ C} {k l : ℕ}
    (hp : ∀ a : σ →₀ ℕ, a.degree < k → MvPowerSeries.coeff a p = 0)
    (hq : ∀ a : σ →₀ ℕ, a.degree < l → MvPowerSeries.coeff a q = 0) :
    ∀ a : σ →₀ ℕ, a.degree < k + l → MvPowerSeries.coeff a (p * q) = 0 := by
  intro a ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = a.degree := by rw [← hx, map_add (f := _)]
  by_cases h1 : x.1.degree < k
  · rw [hp _ h1, zero_mul]
  · rw [hq _ (by omega), mul_zero]

private theorem coeff_pow_eq_zero_of_degree_lt_character_germs' {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ k : ℕ, ∀ a : σ →₀ ℕ, a.degree < k → MvPowerSeries.coeff a (f ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ k ih =>
    rw [pow_succ]
    refine coeff_mul_eq_zero_of_degree_lt_add_character_germs ih fun a ha => ?_
    have h0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

private theorem coeff_mvExp_eq_sum_range_of_degree_le {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (m : σ →₀ ℕ) (N : ℕ) (hN : m.degree ≤ N) :
    MvPowerSeries.coeff m (mvExp f) =
      ∑ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) := by
  show ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) = _
  rw [← Finset.sum_range_add_sum_Ico _ (show m.degree + 1 ≤ N + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (m.degree + 1) (N + 1)) (fun k hk => by
    rw [Finset.mem_Ico] at hk
    rw [coeff_pow_eq_zero_of_degree_lt_character_germs' hf k m (by omega), zero_div]), add_zero]

theorem exp_add {σ : Type} {f g : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  ext m
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by rw [map_add (f := _), hf, hg, add_zero]
  set N := m.degree with hN
  have hT : ∀ i j : ℕ, N < i + j → MvPowerSeries.coeff m (f ^ i * g ^ j) = 0 :=
    fun i j h => coeff_mul_eq_zero_of_degree_lt_add_character_germs (coeff_pow_eq_zero_of_degree_lt_character_germs' hf i) (coeff_pow_eq_zero_of_degree_lt_character_germs' hg j) m (by omega)

  have hL : MvPowerSeries.coeff m (mvExp (f + g)) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
    rw [coeff_mvExp_eq_sum_range_of_degree_le hfg m N le_rfl]
    have hk : ∀ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m ((f + g) ^ k) / (k.factorial : C) =
        ∑ i ∈ Finset.range (k + 1), MvPowerSeries.coeff m (f ^ i * g ^ (k - i)) /
          ((i.factorial : C) * ((k - i).factorial : C)) := by
      intro k _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [add_pow, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← nsmul_eq_mul', map_nsmul, nsmul_eq_mul, Nat.cast_choose C hik]
      have h1 : (k.factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have h2 : (i.factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have h3 : ((k - i).factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    rw [Finset.sum_congr rfl hk]
    rw [Finset.sum_range_diag_flip (N + 1) fun i j =>
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C))]
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_subset (fun j hj => by
      rw [Finset.mem_range] at hj ⊢
      omega) fun j hj hj' => ?_
    rw [Finset.mem_range] at hj hj'
    rw [hT i j (by omega), zero_div]

  have hR : MvPowerSeries.coeff m (mvExp f * mvExp g) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
    rw [MvPowerSeries.coeff_mul]
    have hx : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, MvPowerSeries.coeff x.1 (mvExp f) * MvPowerSeries.coeff x.2 (mvExp g) =
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          MvPowerSeries.coeff x.1 (f ^ i) * MvPowerSeries.coeff x.2 (g ^ j) /
            ((i.factorial : C) * (j.factorial : C)) := by
      intro x hx
      replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hd : x.1.degree + x.2.degree = N := by rw [hN, ← hx, map_add (f := _)]
      rw [coeff_mvExp_eq_sum_range_of_degree_le hf x.1 N (by omega), coeff_mvExp_eq_sum_range_of_degree_le hg x.2 N (by omega), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_div_comm]
    rw [Finset.sum_congr rfl hx, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_div]
  rw [hL, hR]

private theorem hasSubst_of_Z0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

private theorem constantCoeff_P2_eq_zero {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : ∀ q, MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
  intro q
  simp only [P2]
  split_ifs
  exacts [ha _, hb _]

private theorem constantCoeff_P3_eq_zero {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    ∀ q, MvPowerSeries.constantCoeff (P3 a b c q) = 0 := by
  intro q
  simp only [P3]
  split_ifs
  exacts [ha _, hb _, hc _]

private theorem mvExp_zero_character_germs {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp_eq_sum_range_of_degree_le (map_zero _) m m.degree le_rfl, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem exp_nsmul {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) (k : ℕ) :
    mvExp ((k : C) • f) = mvExp f ^ k := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact mvExp_zero_character_germs
  | succ k ih =>
    have hk : MvPowerSeries.constantCoeff ((k : C) • f) = 0 := by simp [hf]
    rw [Nat.cast_succ, add_smul, one_smul, exp_add hk hf, ih, pow_succ]

variable (Y : FBChart C V O dd)

section Subst

variable [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
  {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
  (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)

include hA hu hv in
theorem subst_pair_substitution_comm (f : PS C 2 dd) :
    MvPowerSeries.subst A (MvPowerSeries.subst (P2 u v) f) =
      MvPowerSeries.subst (P2 (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i))) f := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (constantCoeff_P2_eq_zero hu hv)) (hasSubst_of_Z0 hA)]
  congr 1
  funext q
  simp only [P2]
  split_ifs <;> rfl

include hA hu hv in
theorem hAt_subst : MvPowerSeries.subst A (hAt Y u v) =
    hAt Y (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i)) :=  subst_pair_substitution_comm hA hu hv Y.h

include hA hu hv in
theorem addAt_subst (i : Fin dd) : MvPowerSeries.subst A (addAt Y u v i) =
    addAt Y (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i)) i :=  subst_pair_substitution_comm hA hu hv (Y.B.G.F i)

include hA hu in
theorem actAt_subst (x : O) (i : Fin dd) : MvPowerSeries.subst A (actAt Y x u i) =
    actAt Y x (fun i => MvPowerSeries.subst A (u i)) i := by
  show MvPowerSeries.subst A (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => u q.2) (Y.B.A.act x i)) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst A (u q.2)) (Y.B.A.act x i)
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => u q.2) fun q => hu q.2) (hasSubst_of_Z0 hA)]

end Subst

theorem cc_addAt {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (addAt Y a b i) = 0 :=  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_Z0 (constantCoeff_P2_eq_zero ha hb))
    (constantCoeff_P2_eq_zero ha hb) (Y.B.G.const i)

private theorem ev_pt_pair {n : ℕ} (x y : Pt C n dd) : ev (n := n) ![x, y] Y.h = hAt Y x y := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst (P2 x y) Y.h
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl | simp [P2]

theorem addOf_eq {n : ℕ} (a b : Pt C n dd) : addOf (Y.B.FK C) a b = addAt Y a b := by
  funext i
  show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![a, b] : Fin 2 → Pt C n dd) p.1 p.2)
      (MvPowerSeries.map (algebraMap C C) (Y.B.G.F i)) = MvPowerSeries.subst (P2 a b) (Y.B.G.F i)
  have hm : MvPowerSeries.map (algebraMap C C) (Y.B.G.F i) = Y.B.G.F i := by
    ext n
    simp [MvPowerSeries.coeff_map]
  rw [hm]
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl | simp [P2]

section Three

variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)

include ha hb hc

theorem triple_subst_first_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (0 : Fin 3) i)) = a := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((0 : Fin 3), i)) = a i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]
  simp [P3]

theorem triple_subst_second_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (1 : Fin 3) i)) = b := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((1 : Fin 3), i)) = b i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]
  simp [P3]

theorem triple_subst_third_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (2 : Fin 3) i)) = c := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((2 : Fin 3), i)) = c i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (constantCoeff_P3_eq_zero ha hb hc))]
  simp [P3]

theorem second_partial_law_at_points : MvPowerSeries.subst (P3 a b c) Y.B.ph2 =
    mvExp (hAt Y a b + hAt Y a c - hAt Y a (addAt Y b c)) := by
  have hp : ∀ (j : Fin 3) (i : Fin dd), MvPowerSeries.constantCoeff (pt C dd j i : PS C 3 dd) = 0 :=
    fun j i => MvPowerSeries.constantCoeff_X _
  have hP3 := constantCoeff_P3_eq_zero ha hb hc
  have hg := Y.gauge.ph2
  rw [toK_eq, ev_pt_pair Y, ev_pt_pair Y, ev_pt_pair Y, addOf_eq] at hg
  have hcc : MvPowerSeries.constantCoeff (hAt Y (pt C dd 0) (pt C dd 1) + hAt Y (pt C dd 0) (pt C dd 2) -
      hAt Y (pt C dd (0 : Fin 3)) (addAt Y (pt C dd 1) (pt C dd 2))) = 0 := by
    rw [map_sub, map_add (f := _), cc_hAt Y (hp 0) (hp 1), cc_hAt Y (hp 0) (hp 2),
      cc_hAt Y (hp 0) (cc_addAt Y (hp 1) (hp 2))]
    simp
  rw [hg, expS_eq _ hcc, subst_exp hP3 hcc]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_Z0 hP3), map_sub, map_add (f := _), MvPowerSeries.coe_substAlgHom]
  rw [hAt_subst Y hP3 (hp 0) (hp 1), hAt_subst Y hP3 (hp 0) (hp 2),
    hAt_subst Y hP3 (hp 0) (cc_addAt Y (hp 1) (hp 2))]
  have haddS : (fun i => MvPowerSeries.subst (P3 a b c) (addAt Y (pt C dd (1 : Fin 3)) (pt C dd 2) i)) =
      addAt Y b c := by
    funext i
    rw [addAt_subst Y hP3 (hp 1) (hp 2) i, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]
  rw [haddS, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]

end Three

end VP

end Formalism.L2.FormalSeriesBounds

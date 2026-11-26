module

public import Formalism.PeriodIntegrals.UnimodGenus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.SubstUpdateVarTwoLiftedThirdRoot
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.LiftedThirdRootSubXZeroNeZero
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.PairSubstXZero
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CoeffSubstUpdZero
noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)

variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]

def upd (k : σ) (t : MvPowerSeries σ K) : σ → MvPowerSeries σ K := Function.update MvPowerSeries.X k t

theorem upd_const {k : σ} {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) (i : σ) :
    MvPowerSeries.constantCoeff (upd k t i) = 0 := by
  unfold upd
  rcases eq_or_ne i k with rfl | h
  · rw [Function.update_self]; exact ht
  · rw [Function.update_of_ne h]; exact MvPowerSeries.constantCoeff_X i

theorem hasSubst_upd (k : σ) {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.HasSubst (upd k t) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (upd_const ht)

theorem upd_self (k : σ) (t : MvPowerSeries σ K) : upd k t k = t :=
  Function.update_self _ _ _

theorem upd_ne {k i : σ} (t : MvPowerSeries σ K) (h : i ≠ k) : upd k t i = MvPowerSeries.X i :=
  Function.update_of_ne h _ _

theorem X_mem_SerS' (S : Subring K) (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ∈ SerS S σ := by
  rw [PI.AddIntG.Wk.mem_SerS]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem upd_mem {S : Subring K} (k : σ) {t : MvPowerSeries σ K} (ht : t ∈ SerS S σ) (i : σ) :
    upd k t i ∈ SerS S σ := by
  rcases eq_or_ne i k with rfl | h
  · rw [upd_self]; exact ht
  · rw [upd_ne t h]; exact X_mem_SerS' S i

theorem prod_upd_zero (k : σ) (d : σ →₀ ℕ) :
    (d.prod fun s e => (upd k (0 : MvPowerSeries σ K) s) ^ e) =
      if d k = 0 then MvPowerSeries.monomial d 1 else 0 := by
  by_cases h : d k = 0
  · rw [if_pos h, MvPowerSeries.monomial_one_eq]
    refine Finsupp.prod_congr fun s hs => ?_
    have hsk : s ≠ k := by
      rintro rfl
      exact (Finsupp.mem_support_iff.1 hs) h
    rw [upd_ne _ hsk]
  · rw [if_neg h, Finsupp.prod]
    refine Finset.prod_eq_zero (i := k) (Finsupp.mem_support_iff.2 h) ?_
    try dsimp only
    rw [upd_self, zero_pow h]

theorem coeff_subst_upd_zero (k : σ) (f : MvPowerSeries σ K) (m : σ →₀ ℕ) (hm : m k = 0) :
    MvPowerSeries.coeff m (MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) f) = MvPowerSeries.coeff m f := by
  have ha := hasSubst_upd k (t := (0 : MvPowerSeries σ K)) (map_zero _)
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ m]
  · try dsimp only
    rw [prod_upd_zero, if_pos hm, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    try dsimp only
    rw [prod_upd_zero]
    split_ifs
    · rw [MvPowerSeries.coeff_monomial_ne (Ne.symm hd), smul_zero]
    · rw [map_zero, smul_zero]

theorem coeff_X_mul_shift (k : σ) (H : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e + Finsupp.single k 1) (MvPowerSeries.X k * H) = MvPowerSeries.coeff e H := by
  rw [add_comm, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul]

private theorem subst_upd_subst_upd_eq_subst_upd_subst (k : σ) {t u : MvPowerSeries σ K}
    (ht : MvPowerSeries.constantCoeff t = 0) (hu : MvPowerSeries.constantCoeff u = 0) (F : MvPowerSeries σ K) :
    MvPowerSeries.subst (upd k u) (MvPowerSeries.subst (upd k t) F) =
      MvPowerSeries.subst (upd k (MvPowerSeries.subst (upd k u) t)) F := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_upd k ht) (hasSubst_upd k hu)]
  congr 1
  funext i
  try dsimp only
  rcases eq_or_ne i k with rfl | h
  · rw [upd_self, upd_self]
  · rw [upd_ne t h, upd_ne _ h, MvPowerSeries.subst_X (hasSubst_upd k hu),
      upd_ne u h]

theorem fact_div {S : Subring K} {k : σ} {s G : MvPowerSeries σ K}
    (hs0 : MvPowerSeries.constantCoeff s = 0) (hsS : s ∈ SerS S σ)
    (hsk : ∀ t : MvPowerSeries σ K, MvPowerSeries.constantCoeff t = 0 → MvPowerSeries.subst (upd k t) s = s)
    (hG : G ∈ SerS S σ) (hz : MvPowerSeries.subst (upd k s) G = 0) :
    ∃ H ∈ SerS S σ, G = (MvPowerSeries.X k - s) * H := by
  have hz0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries σ K) = 0 := map_zero _
  have hp0 : MvPowerSeries.constantCoeff (MvPowerSeries.X k + s : MvPowerSeries σ K) = 0 := by
    rw [map_add (f := _), hs0, add_zero]; exact MvPowerSeries.constantCoeff_X k
  have hm0 : MvPowerSeries.constantCoeff (MvPowerSeries.X k - s : MvPowerSeries σ K) = 0 := by
    rw [map_sub, hs0, sub_zero]; exact MvPowerSeries.constantCoeff_X k
  have hG' : MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G ∈ PI.AddIntG.Wk.SerS S σ :=
    PI.AddIntG.Wk.mvsubst_mem_SerS S (upd_const hp0)
      (upd_mem k (add_mem (X_mem_SerS' S k) hsS)) hG
  have e0 : MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) (MvPowerSeries.X k + s) = s := by
    rw [MvPowerSeries.subst_add (hasSubst_upd k hz0), MvPowerSeries.subst_X (hasSubst_upd k hz0),
      upd_self, hsk 0 hz0, zero_add]
  have hdvd : (MvPowerSeries.X k : MvPowerSeries σ K) ∣ MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [← coeff_subst_upd_zero k _ m hm, subst_upd_subst_upd_eq_subst_upd_subst k hp0 hz0, e0, hz, map_zero]
  obtain ⟨H', hH'⟩ := hdvd
  have hH'S : H' ∈ PI.AddIntG.Wk.SerS S σ := by
    rw [PI.AddIntG.Wk.mem_SerS]
    intro e
    rw [← coeff_X_mul_shift k H' e, ← hH']
    exact (PI.AddIntG.Wk.mem_SerS S _).1 hG' _
  refine ⟨MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) H',
    PI.AddIntG.Wk.mvsubst_mem_SerS S (upd_const hm0)
      (upd_mem k (sub_mem (X_mem_SerS' S k) hsS)) hH'S, ?_⟩
  have e1 : MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) (MvPowerSeries.X k + s) = MvPowerSeries.X k := by
    rw [MvPowerSeries.subst_add (hasSubst_upd k hm0), MvPowerSeries.subst_X (hasSubst_upd k hm0),
      upd_self, hsk _ hm0, sub_add_cancel]
  have e2 : upd k (MvPowerSeries.X k : MvPowerSeries σ K) = MvPowerSeries.X := by
    funext i
    rcases eq_or_ne i k with rfl | h
    · exact upd_self _ _
    · exact upd_ne _ h
  calc G = MvPowerSeries.subst (MvPowerSeries.X : σ → MvPowerSeries σ K) G :=
        (congrFun (MvPowerSeries.subst_self (σ := σ) (R := K)) G).symm
    _ = MvPowerSeries.subst (upd k (MvPowerSeries.X k - s))
          (MvPowerSeries.subst (upd k (MvPowerSeries.X k + s)) G) := by
        rw [subst_upd_subst_upd_eq_subst_upd_subst k hp0 hm0, e1, e2]
    _ = (MvPowerSeries.X k - s) * MvPowerSeries.subst (upd k (MvPowerSeries.X k - s)) H' := by
        rw [hH', MvPowerSeries.subst_mul (hasSubst_upd k hm0), MvPowerSeries.subst_X (hasSubst_upd k hm0),
          upd_self]

end PI.FglTriFactor.Wk
end
end

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)

variable {p : ℕ} [Fact p.Prime]

theorem psubst_comm {σ τ : Type*} {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  have hA : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hA hb]

section Ops

variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}

theorem cc_lg (hl : PowerSeries.constantCoeff l = 0) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) : MvPowerSeries.constantCoeff (lg l a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha l hl

theorem cc_pt (hex : PowerSeries.constantCoeff ex = 0) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) : MvPowerSeries.constantCoeff (pt ex a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha ex hex

theorem cc_add (hl : PowerSeries.constantCoeff l = 0) (hex : PowerSeries.constantCoeff ex = 0)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  have h : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l a + PI.FglTriFactor.lg l b) = 0 := by
    rw [map_add (f := _), cc_lg hl ha, cc_lg hl hb, add_zero]
  exact cc_pt hex h

theorem subst_lg {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (lg l a) = lg l (MvPowerSeries.subst b a) :=
  psubst_comm ha hb l

theorem subst_pt {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (pt ex a) = pt ex (MvPowerSeries.subst b a) :=
  psubst_comm ha hb ex

theorem subst_add (hl : PowerSeries.constantCoeff l = 0) {b : σ → MvPowerSeries τ ℂ_[p]}
    (hb : MvPowerSeries.HasSubst b) {x y : MvPowerSeries σ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst b (add l ex x y) = add l ex (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) := by
  have h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x + PI.FglTriFactor.lg l y) = 0 := by
    rw [map_add (f := _), cc_lg hl hx, cc_lg hl hy, add_zero]
  unfold PI.FglTriFactor.add
  rw [subst_pt hb h0, MvPowerSeries.subst_add hb, subst_lg hb hx, subst_lg hb hy]

theorem subst_sub (hl : PowerSeries.constantCoeff l = 0) {b : σ → MvPowerSeries τ ℂ_[p]}
    (hb : MvPowerSeries.HasSubst b) {x y : MvPowerSeries σ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst b (sub l ex x y) = sub l ex (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) := by
  have h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x - PI.FglTriFactor.lg l y) = 0 := by
    rw [map_sub, cc_lg hl hx, cc_lg hl hy, sub_zero]
  unfold PI.FglTriFactor.sub
  rw [subst_pt hb h0, MvPowerSeries.subst_sub hb, subst_lg hb hx, subst_lg hb hy]

theorem lg_pt (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
    {Y : MvPowerSeries σ ℂ_[p]} (hY : MvPowerSeries.constantCoeff Y = 0) : lg l (pt ex Y) = Y := by
  have hY' : PowerSeries.HasSubst Y := PowerSeries.HasSubst.of_constantCoeff_zero hY
  unfold PI.FglTriFactor.lg PI.FglTriFactor.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex0) hY', hinv,
    PowerSeries.subst_X hY']

theorem pt_lg (hl0 : PowerSeries.constantCoeff l = 0) (hinv : PowerSeries.subst l ex = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) : pt ex (lg l x) = x := by
  have hx' : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  unfold PI.FglTriFactor.lg PI.FglTriFactor.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hx', hinv,
    PowerSeries.subst_X hx']

theorem pt_zero (hex0 : PowerSeries.constantCoeff ex = 0) : pt ex (0 : MvPowerSeries σ ℂ_[p]) = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero hex0

theorem lg_zero (hl0 : PowerSeries.constantCoeff l = 0) : lg l (0 : MvPowerSeries σ ℂ_[p]) = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero hl0

end Ops

section Pair

variable {τ : Type*}

def pr (x y : MvPowerSeries τ ℂ_[p]) (f : MvPowerSeries (Fin 2) ℂ_[p]) : MvPowerSeries τ ℂ_[p] :=
  MvPowerSeries.subst ![x, y] f

private theorem forall_fin_two_vec_of_both {α : Type*} (P : α → Prop) {x y : α} (hx : P x) (hy : P y) :
    ∀ i : Fin 2, P (![x, y] i) := by
  intro i
  fin_cases i
  exacts [hx, hy]

theorem hasSubst_pr {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.HasSubst ![x, y] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy)

theorem cc_pr {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) {f : MvPowerSeries (Fin 2) ℂ_[p]}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (pr x y f) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst ![x, y] f) = 0
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pr hx hy)
    (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy) hf

theorem pr_comp {υ : Type*} {b : τ → MvPowerSeries υ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (f : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst b (pr x y f) = pr (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) f := by
  unfold pr
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pr hx hy) hb]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem pr_mem {S : Subring ℂ_[p]} {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (hxS : x ∈ SerS S τ) (hyS : y ∈ SerS S τ)
    {f : MvPowerSeries (Fin 2) ℂ_[p]} (hf : f ∈ SerS S (Fin 2)) : pr x y f ∈ SerS S τ := by
  show MvPowerSeries.subst ![x, y] f ∈ PI.AddIntG.Wk.SerS S τ
  exact PI.AddIntG.Wk.mvsubst_mem_SerS S (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy)
    (forall_fin_two_vec_of_both (fun z => z ∈ PI.AddIntG.Wk.SerS S τ) hxS hyS) hf

theorem cc_subst_eq {σ : Type*} {a : σ → MvPowerSeries τ ℂ_[p]} (hA : MvPowerSeries.HasSubst a)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hg : MvPowerSeries.constantCoeff (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) = 0 := by
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h := MvPowerSeries.constantCoeff_subst_eq_zero hA ha hg
  rw [MvPowerSeries.subst_sub hA, MvPowerSeries.subst_C, map_sub, MvPowerSeries.constantCoeff_C,
    sub_eq_zero] at h
  exact h

theorem add_pr {l ex : PowerSeries ℂ_[p]} (hl : PowerSeries.constantCoeff l = 0)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    add l ex x y = pr x y (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  have hb := hasSubst_pr hx hy
  rw [pr, subst_add hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl

theorem sub_pr {l ex : PowerSeries ℂ_[p]} (hl : PowerSeries.constantCoeff l = 0)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    sub l ex x y = pr x y (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  have hb := hasSubst_pr hx hy
  rw [pr, subst_sub hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl

end Pair

end PI.FglTriFactor.Wk
end
end

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem wser_X {τ : Type*} (wq : PowerSeries ℂ_[p]) (i : τ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) (wser wq) =
      (MvPowerSeries.X i) ^ 3 * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) wq := by
  have hX := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X (R := ℂ_[p]) i)
  rw [wser, PowerSeries.subst_mul hX, PowerSeries.subst_pow hX, PowerSeries.subst_X hX]

theorem cc_wser (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (wser wq) = 0 := by
  simp [wser]

theorem lam_pr {τ : Type*} (wq : PowerSeries ℂ_[p]) {x y : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    (y - x) * pr x y (lam wq) = PowerSeries.subst y (wser wq) - PowerSeries.subst x (wser wq) := by
  have hb : MvPowerSeries.HasSubst (![x, y] : Fin 2 → MvPowerSeries τ ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have hcomp : ∀ i : Fin 2, MvPowerSeries.subst ![x, y] (PI.AddIntG.Wk.wv wq i) =
      PowerSeries.subst ((![x, y] : Fin 2 → MvPowerSeries τ ℂ_[p]) i) (wser wq) := by
    intro i
    have hXi : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
    rw [PI.AddIntG.Wk.wv, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hXi.const hb]
    simp only [MvPowerSeries.subst_X hb]
    rfl
  have h := congrArg (MvPowerSeries.subst ![x, y]) (PI.AddIntG.Wk.lam_mul wq)
  rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, hcomp 1, hcomp 0] at h
  simp only [MvPowerSeries.subst_X hb, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
  exact h

def Lab (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (lam wq)

def Lac (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 2) (lam wq)

def s3 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (Z3 W wq)

theorem T_eq (wq : PowerSeries ℂ_[p]) :
    T wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * (MvPowerSeries.X 2 - MvPowerSeries.X 0) * (Lac wq - Lab wq) := by
  have hAB := lam_pr wq (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 1)
    (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)
  have hAC := lam_pr wq (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 2)
    (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)
  rw [wser_X, wser_X] at hAB hAC
  simp only [T, Lab, Lac]
  linear_combination (MvPowerSeries.X 2 - MvPowerSeries.X 0) * hAB - (MvPowerSeries.X 1 - MvPowerSeries.X 0) * hAC

theorem lam_SerS {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : ∀ n, PowerSeries.coeff n wq ∈ S) :
    lam wq ∈ SerS S (Fin 2) := by
  refine ⟨fun e => ⟨lam wq e, ?_⟩, ?_⟩
  · show PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) ∈ S
    rw [wser, PowerSeries.coeff_X_pow_mul']
    split_ifs
    · exact hwq _
    · exact S.zero_mem
  · ext e
    rfl

private theorem coeff_pr_X_X (i j : Fin 3) (hij : i ≠ j) (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (pr (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X j) f) =
      if e = Finsupp.single i (e i) + Finsupp.single j (e j) then
        MvPowerSeries.coeff (Finsupp.single 0 (e i) + Finsupp.single 1 (e j)) f else 0 := by
  classical
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s k => (![MvPowerSeries.X i, MvPowerSeries.X j] s : MvPowerSeries (Fin 3) ℂ_[p]) ^ k) =
        MvPowerSeries.monomial (Finsupp.single i (d 0) + Finsupp.single j (d 1)) 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, mul_one]
  have hij' : j ≠ i := Ne.symm hij
  unfold pr
  rw [MvPowerSeries.coeff_subst ha]
  simp only [hprod, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (Finsupp.single 0 (e i) + Finsupp.single 1 (e j)) (fun d hd => by
      rw [if_neg]
      intro h'
      apply hd
      have hi := congrArg (fun f => f i) h'
      have hj := congrArg (fun f => f j) h'
      simp [Finsupp.single_apply, hij, hij'] at hi hj
      ext k
      fin_cases k
      · simp [hi]
      · simp [hj])]
    have e0 : (Finsupp.single (0 : Fin 2) (e i) + Finsupp.single 1 (e j) : Fin 2 →₀ ℕ) 0 = e i := by simp
    have e1 : (Finsupp.single (0 : Fin 2) (e i) + Finsupp.single 1 (e j) : Fin 2 →₀ ℕ) 1 = e j := by simp
    rw [if_pos (by rw [e0, e1]; exact h)]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp [Finsupp.single_apply, hij, hij']


set_option maxHeartbeats 800000 in
theorem mu_exists {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∃ μ ∈ SerS S (Fin 3), Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ := by
  classical
  obtain ⟨μ, hμc⟩ : ∃ μ : MvPowerSeries (Fin 3) ℂ_[p], ∀ e, MvPowerSeries.coeff e μ =
      MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 + e 2 + 1)) (lam wq) :=
    ⟨fun e => MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 + e 2 + 1)) (lam wq),
      fun e => by simp only [MvPowerSeries.coeff_apply]; exact MvPowerSeries.coeff_apply _ _⟩
  have hlam : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (lam wq) = PowerSeries.coeff (d 0 + d 1 + 1) (wser wq) :=
    fun d => by rw [MvPowerSeries.coeff_apply]; rfl
  refine ⟨μ, (mem_SerS S _).2 (fun e => ?_), ?_⟩
  · rw [hμc]
    exact (mem_SerS S _).1 (lam_SerS hwq) _
  · ext e
    have h02 : (e = Finsupp.single 0 (e 0) + Finsupp.single 2 (e 2)) ↔ e 1 = 0 := by
      constructor
      · intro h
        rw [h]
        simp [Finsupp.single_apply]
      · intro h
        ext k
        fin_cases k <;> simp [Finsupp.single_apply, h]
    have h01 : (e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1)) ↔ e 2 = 0 := by
      constructor
      · intro h
        rw [h]
        simp [Finsupp.single_apply]
      · intro h
        ext k
        fin_cases k <;> simp [Finsupp.single_apply, h]
    have hX : ∀ k : Fin 3, (MvPowerSeries.X k : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.monomial (Finsupp.single k 1) 1 := fun k => by
      rw [← MvPowerSeries.X_pow_eq, pow_one]
    rw [map_sub, Lac, Lab, coeff_pr_X_X 0 2 (by decide), coeff_pr_X_X 0 1 (by decide), sub_mul, map_sub, hX 2, hX 1,
      MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, hμc, hμc, hlam, hlam, hlam, hlam]
    simp only [Finsupp.single_le_iff, h02, h01, one_mul]
    have hidx : ∀ a b : ℕ, a = b → PowerSeries.coeff a (wser wq) = PowerSeries.coeff b (wser wq) :=
      fun a b h => by rw [h]
    by_cases h1 : e 1 = 0 <;> by_cases h2 : e 2 = 0
    · rw [if_pos h1, if_pos h2, if_neg (by omega), if_neg (by omega), sub_self, sub_eq_zero]
      apply hidx
      simp [Finsupp.single_apply, h1, h2]
    · rw [if_pos h1, if_neg h2, if_pos (by omega), if_neg (by omega), sub_zero, sub_zero]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply, h1]
      omega
    · rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega), zero_sub, zero_sub, neg_inj]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply, h2]
      omega
    · rw [if_neg h1, if_neg h2, if_pos (by omega), if_pos (by omega), sub_self, eq_comm, sub_eq_zero]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply]
      omega

theorem subst_pairSubst_zero_one (g : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1, (0 : MvPowerSeries (Fin 2) ℂ_[p])]
      (pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) g) = g := by
  have h3 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  rw [pr, MvPowerSeries.subst_comp_subst_apply h2 h3]
  have e : (fun s => MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] :
      Fin 3 → MvPowerSeries (Fin 2) ℂ_[p])
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) s)) =
      MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp [MvPowerSeries.subst_X h3]
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem pairSubst_zero_one_ne_zero {g : MvPowerSeries (Fin 2) ℂ_[p]} (hg : g ≠ 0) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) g ≠ 0 := by
  have h3 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  intro h
  apply hg
  rw [← subst_pairSubst_zero_one g, h, ← MvPowerSeries.coe_substAlgHom h3, map_zero]

theorem constantCoeff_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (s3 W wq) = 0 := by
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  exact MvPowerSeries.constantCoeff_subst_eq_zero h2 (fun i => by fin_cases i <;> simp)
    (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)

theorem liftedThirdRoot_sub_X (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    s3 W wq - MvPowerSeries.X (Fin.castSucc i) = pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (MvPowerSeries.X 1) (Z3 W wq - MvPowerSeries.X i) := by
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  simp only [s3, pr]
  rw [MvPowerSeries.subst_sub h2, MvPowerSeries.subst_X h2]
  fin_cases i <;> rfl

theorem liftedThirdRoot_sub_X_zero_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    s3 W wq - MvPowerSeries.X 0 ≠ 0 := by
  intro h
  apply pairSubst_zero_one_ne_zero (PI.AddIntG.Wk.thirdRoot_sub_var_zero_ne_zero W wq)
  rw [← liftedThirdRoot_sub_X W wq 0]
  exact h

theorem liftedThirdRoot_sub_X_one_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    s3 W wq - MvPowerSeries.X 1 ≠ 0 := by
  intro h
  apply pairSubst_zero_one_ne_zero (PI.AddIntG.Wk.thirdRoot_sub_var_one_ne_zero W wq)
  rw [← liftedThirdRoot_sub_X W wq 1]
  exact h

end PI.FglTriFactor.Wk
end
end

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem h0X (i : Fin 3) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
  simp

theorem lam_as {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) = Lab wq := by
  have H := hasSubst_pr (h0X (p := p) 0) (h0X 1)
  have hl := lam_pr wq (h0X (p := p) 0) (constantCoeff_liftedThirdRoot W wq)
  have hZ0 := PI.AddIntG.Wk.constantCoeff_thirdRoot W wq
  have ws : PowerSeries.subst (s3 W wq) (wser wq) = Lab wq * s3 W wq + pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (nu wq) := by
    rw [s3, pr, ← psubst_comm hZ0 H, PI.AddIntG.Wk.subst_thirdRoot_wSeries h, MvPowerSeries.subst_add H, MvPowerSeries.subst_mul H]
    rfl
  have hnu : pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) (nu wq) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (wser wq) - Lab wq * MvPowerSeries.X 0 := by
    simp only [nu, wv, PI.AddIntG.Xv]
    rw [pr, MvPowerSeries.subst_sub H, MvPowerSeries.subst_mul H, psubst_comm (by simp) H, MvPowerSeries.subst_X H]
    rfl
  rw [ws, hnu] at hl
  have key : (s3 W wq - MvPowerSeries.X 0) *
      (pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) - Lab wq) = 0 := by
    linear_combination hl
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (liftedThirdRoot_sub_X_zero_ne_zero W wq))

theorem mu_vanish {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {μ : MvPowerSeries (Fin 3) ℂ_[p]} (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (upd 2 (s3 W wq)) μ = 0 := by
  have Hφ := hasSubst_upd (2 : Fin 3) (constantCoeff_liftedThirdRoot W wq)
  have e := congrArg (MvPowerSeries.subst (upd 2 (s3 W wq))) hμ
  rw [MvPowerSeries.subst_sub Hφ, MvPowerSeries.subst_mul Hφ, MvPowerSeries.subst_sub Hφ, Lac, Lab,
    pr_comp Hφ (h0X 0) (h0X 2), pr_comp Hφ (h0X 0) (h0X 1), MvPowerSeries.subst_X Hφ, MvPowerSeries.subst_X Hφ,
    MvPowerSeries.subst_X Hφ, upd_ne _ (by decide : (0 : Fin 3) ≠ 2), upd_ne _ (by decide : (1 : Fin 3) ≠ 2),
    upd_self] at e
  rw [← Lab, lam_as h, sub_self] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (liftedThirdRoot_sub_X_one_ne_zero W wq)

theorem subst_updateVar_two_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (t : MvPowerSeries (Fin 3) ℂ_[p])
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.subst (upd 2 t) (s3 W wq) = s3 W wq := by
  have hz3 : ∀ i, MvPowerSeries.constantCoeff (upd 2 t i) = 0 := fun i => by
    fin_cases i <;> simp [upd, Function.update, ht]
  have hu : MvPowerSeries.HasSubst (upd 2 t) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz3
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz3 i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz3
  have hz2 : ∀ i, MvPowerSeries.constantCoeff
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := fun i => by
    fin_cases i <;> simp
  have h2 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.X 1] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz2
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz2 i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz2
  unfold s3 pr
  rw [MvPowerSeries.subst_comp_subst_apply h2 hu]
  congr 1
  funext i
  fin_cases i
  · show MvPowerSeries.subst (upd 2 t) (MvPowerSeries.X 0) = MvPowerSeries.X 0
    rw [MvPowerSeries.subst_X hu]
    simp [upd, Function.update_apply]
  · show MvPowerSeries.subst (upd 2 t) (MvPowerSeries.X 1) = MvPowerSeries.X 1
    rw [MvPowerSeries.subst_X hu]
    simp [upd, Function.update_apply]

theorem liftedThirdRoot_mem_coeffSubring {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    s3 W wq ∈ SerS S (Fin 3) :=
  pr_mem (h0X 0) (h0X 1) (X_mem_SerS' S 0) (X_mem_SerS' S 1) (PI.AddIntG.Wk.thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h)

def zc : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p] := ![0, 0, MvPowerSeries.X 2]

theorem zc_const (i : Fin 3) : MvPowerSeries.constantCoeff (zc (p := p) i) = 0 := by
  fin_cases i <;> simp [zc]

theorem hasSubst_zc : MvPowerSeries.HasSubst (zc (p := p)) := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun i => zc_const i)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun i => zc_const (p := p) i)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => zc_const i)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [zc_const i]; exact IsNilpotent.zero)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (a := zc (p := p)) (by intro i; exact zc_const i)

theorem pr_zero_zero (g : MvPowerSeries (Fin 2) ℂ_[p]) (hg : MvPowerSeries.constantCoeff g = 0) :
    pr (0 : MvPowerSeries (Fin 3) ℂ_[p]) 0 g = 0 := by
  unfold pr
  ext e
  have hz : ∀ i, MvPowerSeries.constantCoeff (![(0 : MvPowerSeries (Fin 3) ℂ_[p]), 0] i) = 0 := fun i => by
    fin_cases i <;> simp
  have ha : MvPowerSeries.HasSubst ![(0 : MvPowerSeries (Fin 3) ℂ_[p]), 0] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg]
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · fin_cases s <;> simp <;> exact hs

theorem subst_lastVarSubst_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst (zc (p := p)) (s3 W wq) = 0 := by
  rw [s3, pr_comp (hasSubst_zc (p := p)) (h0X 0) (h0X 1), MvPowerSeries.subst_X (hasSubst_zc (p := p)), MvPowerSeries.subst_X (hasSubst_zc (p := p))]
  exact pr_zero_zero _ (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)

theorem eq_of_X_two_mul_eq {f g : MvPowerSeries (Fin 3) ℂ_[p]} (h : MvPowerSeries.X 2 * f = MvPowerSeries.X 2 * g) :
    f = g := by
  refine mul_left_cancel₀ ?_ h
  intro h0
  have e := congrArg (MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) 1)) h0
  simp at e

theorem zc_mu {wq : PowerSeries ℂ_[p]} {μ : MvPowerSeries (Fin 3) ℂ_[p]}
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (zc (p := p)) μ = MvPowerSeries.X 2 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq := by
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hμ
  rw [MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_mul Hz, MvPowerSeries.subst_sub Hz, Lac, Lab,
    pr_comp Hz (h0X 0) (h0X 2), pr_comp Hz (h0X 0) (h0X 1), MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz,
    MvPowerSeries.subst_X Hz] at e
  have e0 : zc (p := p) 0 = 0 := rfl
  have e1 : zc (p := p) 1 = 0 := rfl
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e0, e1, e2, pr_zero_zero _ (PI.AddIntG.Wk.constantCoeff_lam wq), sub_zero, sub_zero] at e
  have hl := lam_pr wq (x := (0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 2) (by simp) (by simp)
  rw [PowerSeries.subst_zero_of_constantCoeff_zero (cc_wser wq), wser_X, sub_zero, sub_zero, e] at hl
  apply eq_of_X_two_mul_eq
  apply eq_of_X_two_mul_eq
  linear_combination hl

theorem m_exists {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    {μ : MvPowerSeries (Fin 3) ℂ_[p]} (hμS : μ ∈ SerS S (Fin 3))
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    ∃ m ∈ SerS S (Fin 3), MvPowerSeries.constantCoeff m = 1 ∧ μ = (MvPowerSeries.X 2 - s3 W wq) * m := by
  obtain ⟨m, hmS, hm⟩ := fact_div (k := 2) (constantCoeff_liftedThirdRoot W wq) (liftedThirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h) (subst_updateVar_two_liftedThirdRoot W wq) hμS
    (mu_vanish h hμ)
  refine ⟨m, hmS, ?_, hm⟩
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hm
  rw [zc_mu hμ, MvPowerSeries.subst_mul Hz, MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_X Hz, subst_lastVarSubst_liftedThirdRoot,
    sub_zero] at e
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e2] at e
  have e' := eq_of_X_two_mul_eq e
  rw [← cc_subst_eq Hz (zc_const (p := p)) m, ← e', PowerSeries.subst_def,
    cc_subst_eq (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => h0X (p := p) 2)) (fun _ => h0X (p := p) 2)]
  exact PI.AddIntG.Wk.wq_const h

end PI.FglTriFactor.Wk
end
end

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  first
  | exact PI.FglChordFactor.Wk.flog_const W wq
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl])
  | simp [flog]

theorem abel' {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    lg (flog W wq) (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg (flog W wq) (MvPowerSeries.X 1) +
      lg (flog W wq) (Z3 W wq) = 0 := PI.AddIntG.Wk.abel h

theorem inv' {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X) :
    PowerSeries.subst (flog W wq) ex = PowerSeries.X :=
  PI.AddIntG.Wk.subst_left_inv (cc_flog W wq) (PI.AddIntG.Wk.coeff_one_flog h) hex0 hex

theorem cc_X {τ : Type*} (i : τ) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) = 0 := by
  simp

theorem log_third_point_sum {τ : Type*} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    lg (flog W wq) (pr x y (Z3 W wq)) = -lg (flog W wq) x - lg (flog W wq) y := by
  have H := hasSubst_pr hx hy
  have e := congrArg (MvPowerSeries.subst ![x, y]) (abel' h)
  rw [MvPowerSeries.subst_add H, MvPowerSeries.subst_add H, subst_lg H (cc_X 0), subst_lg H (cc_X 1),
    subst_lg H (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq), MvPowerSeries.subst_X H, MvPowerSeries.subst_X H] at e
  have hz : MvPowerSeries.subst ![x, y] (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom H, map_zero]
  rw [hz] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [pr]
  linear_combination e

theorem sub_factor {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)) :
    ∃ u ∈ SerS S (Fin 2), MvPowerSeries.constantCoeff u = 1 ∧
      sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * u := by
  have hl0 := cc_flog W wq
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := map_zero _
  set Zn := pr (0 : MvPowerSeries (Fin 2) ℂ_[p]) (MvPowerSeries.X 1) (Z3 W wq) with hZn
  have hZn0 : MvPowerSeries.constantCoeff Zn = 0 := cc_pr h0 (cc_X 1) (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)
  have hZnS : Zn ∈ SerS S (Fin 2) :=
    pr_mem h0 (cc_X 1) (zero_mem _) (X_mem_SerS' S 1) (PI.AddIntG.Wk.thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h)
  have hlZn : lg (flog W wq) Zn = -lg (flog W wq) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hZn, log_third_point_sum h h0 (cc_X 1), lg_zero hl0, neg_zero, zero_sub]
  have hsa : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      add (flog W wq) ex (MvPowerSeries.X 0) Zn := by
    unfold sub add; rw [hlZn, sub_eq_add_neg]
  have hGS : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := by
    rw [hsa, add_pr hl0 (cc_X 0) hZn0]
    exact pr_mem (cc_X 0) hZn0 (X_mem_SerS' S 0) hZnS hF
  have HU := hasSubst_upd (0 : Fin 2) (cc_X (p := p) (1 : Fin 2))
  obtain ⟨u, huS, hu⟩ := fact_div (k := 0) (cc_X 1) (X_mem_SerS' S 1)
    (fun t ht => by rw [MvPowerSeries.subst_X (hasSubst_upd 0 ht), upd_ne _ (by decide)]) hGS (by
      rw [subst_sub hl0 HU (cc_X 0) (cc_X 1), MvPowerSeries.subst_X HU, MvPowerSeries.subst_X HU, upd_self,
        upd_ne _ (by decide : (1 : Fin 2) ≠ 0)]
      unfold sub; rw [sub_self, pt_zero hex0])
  refine ⟨u, huS, ?_, hu⟩
  have H1 := hasSubst_upd (1 : Fin 2) h0
  have e := congrArg (MvPowerSeries.subst (upd (1 : Fin 2) (0 : MvPowerSeries (Fin 2) ℂ_[p]))) hu
  rw [subst_sub hl0 H1 (cc_X 0) (cc_X 1), MvPowerSeries.subst_mul H1, MvPowerSeries.subst_sub H1,
    MvPowerSeries.subst_X H1, MvPowerSeries.subst_X H1, upd_self, upd_ne _ (by decide : (0 : Fin 2) ≠ 1),
    sub_zero] at e
  have e' : sub (flog W wq) ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) 0 = MvPowerSeries.X 0 := by
    unfold sub; rw [lg_zero hl0, sub_zero, pt_lg hl0 (inv' h hex0 hex) (cc_X 0)]
  rw [e'] at e
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h'
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h'
    simp [MvPowerSeries.coeff_X] at this
  have e2 : MvPowerSeries.X 0 * (MvPowerSeries.subst (upd (1 : Fin 2) (0 : MvPowerSeries (Fin 2) ℂ_[p])) u - 1) = 0 := by
    linear_combination -e
  have e3 := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hX0)
  rw [← cc_subst_eq H1 (upd_const h0) u, e3, map_one]

theorem add_factor {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)) :
    ∃ u ∈ SerS S (Fin 3), MvPowerSeries.constantCoeff u = 1 ∧
      add (flog W wq) ex (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) (MvPowerSeries.X 2) =
        (MvPowerSeries.X 2 - s3 W wq) * u := by
  have hl0 := cc_flog W wq
  set l := flog W wq with hl
  have hab0 : MvPowerSeries.constantCoeff
      (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1)) = 0 :=
    cc_add hl0 hex0 (cc_X 0) (cc_X 1)
  have hGS : add l ex (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1))
      (MvPowerSeries.X 2) ∈ SerS S (Fin 3) := by
    rw [add_pr hl0 hab0 (cc_X 2), add_pr hl0 (cc_X 0) (cc_X 1)]
    have hab0' := hab0
    rw [add_pr hl0 (cc_X 0) (cc_X 1)] at hab0'
    exact pr_mem hab0' (cc_X 2) (pr_mem (cc_X 0) (cc_X 1) (X_mem_SerS' S 0) (X_mem_SerS' S 1) hF)
      (X_mem_SerS' S 2) hF
  have hlab : lg l (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1)) =
      lg l (MvPowerSeries.X 0) + lg l (MvPowerSeries.X 1) := by
    unfold add
    exact lg_pt hex0 hex (by rw [map_add (f := _), cc_lg hl0 (cc_X 0), cc_lg hl0 (cc_X 1), add_zero])
  have HU := hasSubst_upd (2 : Fin 3) (constantCoeff_liftedThirdRoot W wq)
  obtain ⟨u, huS, hu⟩ := fact_div (k := 2) (constantCoeff_liftedThirdRoot W wq) (liftedThirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h) (subst_updateVar_two_liftedThirdRoot W wq) hGS (by
      rw [subst_add hl0 HU hab0 (cc_X 2), subst_add hl0 HU (cc_X 0) (cc_X 1), MvPowerSeries.subst_X HU,
        MvPowerSeries.subst_X HU, MvPowerSeries.subst_X HU, upd_self, upd_ne _ (by decide : (0 : Fin 3) ≠ 2),
        upd_ne _ (by decide : (1 : Fin 3) ≠ 2)]
      have hZ := log_third_point_sum h (cc_X (p := p) (0 : Fin 3)) (cc_X 1)
      rw [← hl] at hZ
      change pt ex (lg l (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) + lg l (s3 W wq)) = 0
      rw [hlab, s3, hZ]
      rw [show lg l (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) + lg l (MvPowerSeries.X 1) +
          (-lg l (MvPowerSeries.X 0) - lg l (MvPowerSeries.X 1)) = 0 by ring, pt_zero hex0])
  refine ⟨u, huS, ?_, hu⟩
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hu
  rw [subst_add hl0 Hz hab0 (cc_X 2), subst_add hl0 Hz (cc_X 0) (cc_X 1), MvPowerSeries.subst_mul Hz,
    MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz,
    subst_lastVarSubst_liftedThirdRoot, sub_zero] at e
  have e0 : zc (p := p) 0 = 0 := rfl
  have e1 : zc (p := p) 1 = 0 := rfl
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e0, e1, e2] at e
  have e00 : add l ex (0 : MvPowerSeries (Fin 3) ℂ_[p]) 0 = 0 := by
    unfold add; rw [lg_zero hl0, add_zero, pt_zero hex0]
  have ec : add l ex (0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 2) = MvPowerSeries.X 2 := by
    unfold add; rw [lg_zero hl0, zero_add, pt_lg hl0 (inv' h hex0 hex) (cc_X 2)]
  rw [e00, ec] at e
  have e' := eq_of_X_two_mul_eq (f := MvPowerSeries.subst (zc (p := p)) u) (g := 1) (by rw [mul_one]; exact e.symm)
  rw [← cc_subst_eq Hz (zc_const (p := p)) u, e', map_one]

end PI.FglTriFactor.Wk

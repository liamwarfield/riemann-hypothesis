module

public import Formalism.LocalToGlobal.CharacterGerms.NegMem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.CoeffAlongCvCongr
section -- merged from Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

def InL (l : ℕ) (f : PowerSeries C) : Prop := ∀ m, ¬ l ∣ m → PowerSeries.coeff m f = 0

def dnL (l : ℕ) (f : PowerSeries C) : PowerSeries C := PowerSeries.mk fun n => PowerSeries.coeff (l * n) f

theorem coeff_dnL (l : ℕ) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (dnL l f) = PowerSeries.coeff (l * n) f := by
  unfold dnL
  rw [PowerSeries.coeff_mk]

theorem InL.eq_subst {l : ℕ} (hl : 0 < l) {f : PowerSeries C} (hf : InL l f) :
    f = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (dnL l f) := by
  ext m
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [coeff_subst_X_pow hl, coeff_dnL]
  · rw [coeff_subst_X_pow_of_not_dvd hl _ _ hm, hf m hm]

theorem inL_subst {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    InL l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) :=
  fun m hm => coeff_subst_X_pow_of_not_dvd hl f m hm

theorem subst_X_pow_inj {l : ℕ} (hl : 0 < l) {f g : PowerSeries C}
    (h : PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) g) : f = g := by
  ext n
  have e := congrArg (PowerSeries.coeff (l * n)) h
  rwa [coeff_subst_X_pow hl, coeff_subst_X_pow hl] at e

theorem InL.add {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f + g) :=
  fun m hm => by rw [map_add (f := _), hf m hm, hg m hm, add_zero]

theorem InL.sub {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f - g) :=
  fun m hm => by rw [map_sub, hf m hm, hg m hm, sub_zero]

theorem InL.smul {l : ℕ} {f : PowerSeries C} (hf : InL l f) (c : C) : InL l (c • f) :=
  fun m hm => by rw [PowerSeries.coeff_smul, hf m hm, smul_zero]

theorem InL.zero {l : ℕ} : InL l (0 : PowerSeries C) :=
  fun m _ => map_zero _

theorem InL.sum {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) (hf : ∀ i ∈ s, InL l (f i)) :
    InL l (∑ i ∈ s, f i) :=
  fun m hm => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => hf i hi m hm

private theorem coeff_tyS_pow_eq_of_two_le {l : ℕ} (hl : 2 ≤ l) (b : ℕ → C) (s : ℕ) :
    PowerSeries.coeff (l ^ s) (tyS l b) = b s := by
  simp only [tyS, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl]
  · intro t _ ht
    rw [if_neg]
    intro e
    exact ht (Nat.pow_right_injective hl e)
  · intro hs
    exfalso
    apply hs
    rw [Finset.mem_range]
    have := Nat.lt_pow_self (by omega : 1 < l) (n := s)
    omega

private theorem coeff_tyS_eq_zero_of_ne_pow {l : ℕ} (b : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) :
    PowerSeries.coeff m (tyS l b) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)

theorem tyS_Vpow {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) :
    tyS l (fun s => if s < 1 then 0 else a (s - 1)) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l a) := by
  have hl0 : 0 < l := by omega
  ext m
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [coeff_subst_X_pow hl0]
    by_cases hk : ∃ t, l ^ t = k
    · obtain ⟨t, rfl⟩ := hk
      rw [← pow_succ', coeff_tyS_pow_eq_of_two_le hl, coeff_tyS_pow_eq_of_two_le hl]
      simp
    · push_neg at hk
      have hk' : ∀ s, l ^ s ≠ l * k := by
        intro s hs
        rcases s with _ | s
        · rw [pow_zero] at hs
          have h1 : l ∣ 1 := ⟨k, hs⟩
          have := Nat.le_of_dvd one_pos h1
          omega
        · rw [pow_succ'] at hs
          exact hk s (Nat.eq_of_mul_eq_mul_left hl0 hs)
      rw [coeff_tyS_eq_zero_of_ne_pow _ _ hk', coeff_tyS_eq_zero_of_ne_pow _ _ hk]
  · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hm]
    simp only [tyS, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs with h1 h2
    · rfl
    · exfalso
      apply hm
      rw [← h1]
      exact dvd_pow_self l (by omega)
    · rfl

theorem inL_of_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) {f : PowerSeries C}
    (h : PowerSeries.rescale ζ f = f) : InL l f := by
  intro m hm
  have h1 := congrArg (PowerSeries.coeff m) h
  rw [PowerSeries.coeff_rescale] at h1
  have h2 : ζ ^ m ≠ 1 := fun e => hm ((hζ.pow_eq_one_iff_dvd m).mp e)
  have h3 : (ζ ^ m - 1) * PowerSeries.coeff m f = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) h2
  · exact h4

theorem InL.rescale {l : ℕ} {ζ : C} (hζ : ζ ^ l = 1) {f : PowerSeries C} (hf : InL l f) :
    PowerSeries.rescale ζ f = f := by
  ext m
  rw [PowerSeries.coeff_rescale]
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [pow_mul, hζ, one_pow, one_mul]
  · rw [hf m hm, mul_zero]

theorem VF.ge_of_pow_eq_one (V : VF C) {ζ : C} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at h
    exact zero_ne_one h
  have h1 : n • V.v ζ = 0 := by
    rw [← AddValuation.map_pow, h, AddValuation.map_one]
  have ht : V.v ζ ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact hζ0
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul, mul_eq_zero] at h1
  have hr0 : r = 0 := h1.resolve_left (Nat.cast_ne_zero.mpr hn)
  unfold VF.Ge
  rw [← hr]
  exact WithTop.coe_le_coe.mpr hr0.ge

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem lg_inj (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {γ γ' : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ' : ∀ i, PowerSeries.constantCoeff (γ' i) = 0)
    (h : ∀ i, alongCv γ (X.lg i) = alongCv γ' (X.lg i)) : γ = γ' := by
  have key : ∀ (δ : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (δ i) = 0) → ∀ i,
      δ i = MvPowerSeries.subst (fun j => alongCv δ (X.lg j)) (X.ex i) := by
    intro δ hδ i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
    have e1 : MvPowerSeries.subst δ (MvPowerSeries.subst X.lg (X.ex i)) = δ i := by
      rw [hexlg i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0) hS]
    rfl
  funext i
  rw [key γ hγ i, key γ' hγ' i]
  simp only [h]

theorem unV_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {ζ : C} (hζ : IsPrimitiveRoot ζ V.l) (z : ℕ → I g ⊕ JJ I g → C) (hz : Vpow 1 z ∈ X.TySet V g) :
    z ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hz
  have hXl : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ V.l) = 0 := by simp [hl0.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hXl
  have hty : ∀ n, tyS V.l (fun s => Vpow 1 z s n) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (tyS V.l fun s => z s n) :=
    fun n => tyS_Vpow hl2 (fun s => z s n)

  have hLin : ∀ i, InL V.l (alongCv γ (X.lg i)) := by
    intro i
    rw [h1 i]
    refine InL.sum _ _ fun c _ => InL.smul ?_ _
    rw [hty]
    exact inL_subst hl0 _

  have hζX : PowerSeries.constantCoeff (ζ • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hγζ : (fun i => PowerSeries.subst (ζ • (PowerSeries.X : PowerSeries C)) (γ i)) = γ := by
    apply X.lg_inj hlg0 hexlg
    · intro i
      exact constantCoeff_subst_zero (σ := Unit) (fun _ => hζX) (hγ i).1
    · exact fun i => (hγ i).1
    · intro i
      rw [alongCv_repar (fun i => (hγ i).1) hζX, ← PowerSeries.rescale_eq_subst]
      exact (hLin i).rescale hζ.pow_eq_one
  have hγL : ∀ i, InL V.l (γ i) := by
    intro i
    apply inL_of_rescale hζ
    rw [PowerSeries.rescale_eq_subst]
    exact congrFun hγζ i
  have hδ : IsCv V fun i => dnL V.l (γ i) := by
    intro i
    refine ⟨?_, fun n => ?_⟩
    · show PowerSeries.constantCoeff (dnL V.l _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dnL, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hγ i).1
    · show V.Ge 0 (PowerSeries.coeff n (dnL V.l _))
      rw [coeff_dnL]
      exact (hγ i).2 _
  have hγδ : γ = fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (dnL V.l (γ i)) :=
    funext fun i => (hγL i).eq_subst hl0
  have hal : ∀ f : MvPowerSeries κ C, alongCv γ f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (alongCv (fun i => dnL V.l (γ i)) f) := by
    intro f
    rw [← alongCv_repar (fun i => (hδ i).1) hXl, ← hγδ]

  have hlamEq : ∀ q, lam q = tyS V.l (fun s => Vpow 1 z s (Sum.inr q)) + alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => Vpow 1 z s (Sum.inl c)) else 0) := by
    intro q
    rw [h2 q]
    abel
  have hlamL : ∀ q, InL V.l (lam q) := by
    intro q
    rw [hlamEq q]
    refine InL.sub (InL.add ?_ ?_) (InL.sum _ _ fun c _ => ?_)
    · rw [hty]; exact inL_subst hl0 _
    · rw [hal]; exact inL_subst hl0 _
    · split_ifs
      · rw [hty]; exact (inL_subst hl0 _).smul _
      · exact InL.zero
  have hlam' : IsCv V fun q => dnL V.l (lam q) := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · show PowerSeries.constantCoeff (dnL V.l _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dnL, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlam q).1
    · show V.Ge 0 (PowerSeries.coeff n (dnL V.l _))
      rw [coeff_dnL]
      exact (hlam q).2 _
  refine ⟨fun i => dnL V.l (γ i), fun q => dnL V.l (lam q), hδ, hlam', ?_, ?_⟩
  · intro i
    apply subst_X_pow_inj hl0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hal, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, PowerSeries.coe_substAlgHom hS, hty]
  · intro q
    apply subst_X_pow_inj hl0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hty, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add (f := _), map_sub, map_sum,
      PowerSeries.coe_substAlgHom hS, ← hal, ← (hlamL q).eq_subst hl0]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [← PowerSeries.coe_substAlgHom hS, map_smul, PowerSeries.coe_substAlgHom hS, hty]
    · rw [← PowerSeries.coe_substAlgHom hS, map_zero]

theorem F_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {ζ : C} (hζ : IsPrimitiveRoot ζ V.l)
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) : Fs V.l x ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  apply X.unV_mem V g hlg0 hexlg hζ
  have hsum : ∑ k ∈ Finset.range V.l, teich V.l (ζ ^ k) x ∈ X.TySet V g :=
    X.sum_mem V g h0 hadd _ _ fun k _ =>
      X.teich_mem V g _ ((V.ge_of_pow_eq_one (by omega) hζ.pow_eq_one).pow k) x hx
  have e : ∑ k ∈ Finset.range V.l, teich V.l (ζ ^ k) x = Vpow 1 (Fs V.l x) := by
    funext i n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ k ∈ Finset.range V.l, (ζ ^ k) ^ (V.l ^ i) * x i n = if i < 1 then 0 else (V.l : C) * x (i - 1 + 1) n
    rw [← Finset.sum_mul]
    cases i with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ i =>
      have h1 : ∀ k, (ζ ^ k) ^ (V.l ^ (i + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  rwa [e] at hsum

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem coeff_alongCv_congr {σ : Type} [Finite σ] {a a' : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, PowerSeries.constantCoeff (a' i) = 0) {k : ℕ}
    (h : ∀ i, ∀ m < k, PowerSeries.coeff m (a i) = PowerSeries.coeff m (a' i)) (f : MvPowerSeries σ C) :
    ∀ m < k, PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv a' f) := by
  intro m hm
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  have hdiff : ∀ i, a i - a' i ∈ Ideal.span {(PowerSeries.X : PowerSeries C) ^ k} := by
    intro i
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, h i n hn, sub_self]
  have hprod : ∀ e : σ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => a' s ^ n) := by
    intro e
    have hq : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a' s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [Ideal.Quotient.eq.2 (hdiff s)]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hq
    have hm' := hq m hm
    rwa [map_sub, sub_eq_zero] at hm'
  simp only [alongCv]
  change MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a' f)
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hA']
  refine finsum_congr fun e => ?_
  congr 1
  exact hprod e

theorem coeff_tyS_congr {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) (N : ℕ) (hab : ∀ i < N, a i = b i) (m : ℕ)
    (hm : m < l ^ N) : PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  simp only [tyS, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : l ^ s = m
  · rw [if_pos hs, if_pos hs]
    apply hab
    by_contra hc
    push_neg at hc
    have h1 : l ^ N ≤ l ^ s := Nat.pow_le_pow_right (by omega) hc
    rw [hs] at h1
    exact absurd hm (not_lt.2 h1)
  · rw [if_neg hs, if_neg hs]

theorem constantCoeff_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.constantCoeff (tyS l a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [tyS, PowerSeries.coeff_mk]
  simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem curve_eq_ex_lg (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (δ : κ → PowerSeries C) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) (i : κ) :
    δ i = alongCv (fun j => alongCv δ (X.lg j)) (X.ex i) := by
  have hA : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hB : MvPowerSeries.HasSubst δ := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
  simp only [alongCv]
  rw [← MvPowerSeries.subst_comp_subst_apply hA hB, hexlg i, MvPowerSeries.subst_X hB]

theorem Vpow_mem' (V : VF C) (g : Fin 2) (s : ℕ) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow s x ∈ X.TySet V g := by
  induction s with
  | zero => rwa [Vpow_zero]
  | succ s ih => rw [Vpow_succ]; exact X.V_mem V g _ ih

theorem sumV_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (y : ℕ → ℕ → I g ⊕ JJ I g → C) (hy : ∀ s, y s ∈ X.TySet V g) : sumV y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hP : ∀ N : ℕ, ∑ s ∈ Finset.range N, Vpow s (y s) ∈ X.TySet V g := fun N =>
    X.sum_mem V g h0 hadd _ _ fun s _ => X.Vpow_mem' V g s _ (hy s)
  have hPeq : ∀ N i, i < N → ∀ n, (∑ s ∈ Finset.range N, Vpow s (y s)) i n = sumV y i n := by
    intro N i hi n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ s ∈ Finset.range N, (if i < s then 0 else y s (i - s) n) = ∑ s ∈ Finset.range (i + 1), y s (i - s) n
    have hsub : Finset.range (i + 1) ⊆ Finset.range N := Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_neg]
      have := Finset.mem_range.1 hs
      omega
    · intro s _ hs
      rw [if_pos]
      have : ¬ s < i + 1 := fun h => hs (Finset.mem_range.2 h)
      omega
  choose γN lamN hγN hlamN h1N h2N using hP
  set A : κ → PowerSeries C := fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c)) with hA
  have hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0 := by
    intro i
    rw [hA]
    show PowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c))) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tyS hl2, smul_zero]
  set γ : κ → PowerSeries C := fun i => alongCv A (X.ex i) with hγdef
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hA0 (hex0 i)
  have hlgγ : ∀ i, alongCv γ (X.lg i) = A i := by
    intro i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
    have e1 : MvPowerSeries.subst A (MvPowerSeries.subst X.ex (X.lg i)) = A i := by
      rw [hlgex i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hex0) hS]
    rfl
  have htyN : ∀ N n, ∀ m < V.l ^ N, PowerSeries.coeff m (tyS V.l fun s => sumV y s n) =
      PowerSeries.coeff m (tyS V.l fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s n) := by
    intro N n m hm
    exact coeff_tyS_congr hl2 _ _ N (fun i hi => (hPeq N i hi n).symm) m hm
  have hγN' : ∀ N i, ∀ m < V.l ^ N, PowerSeries.coeff m (γ i) = PowerSeries.coeff m (γN N i) := by
    intro N i m hm
    rw [X.curve_eq_ex_lg hlg0 hexlg (γN N) (fun i => (hγN N i).1) i]
    refine coeff_alongCv_congr hA0 (fun j => constantCoeff_subst_zero (fun i => (hγN N i).1) (hlg0 j)) ?_ _ m hm
    intro j m' hm'
    show PowerSeries.coeff m' (∑ c : I g, X.u g c j • tyS V.l (fun s => sumV y s (Sum.inl c))) =
      PowerSeries.coeff m' (alongCv (γN N) (X.lg j))
    rw [h1N N j]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m' hm']
  have hγI : IsCv V γ := by
    intro i
    refine ⟨hγ0 i, fun n => ?_⟩
    rw [hγN' n i n (Nat.lt_pow_self (by omega))]
    exact (hγN n i).2 n
  set lam : JJ I g → PowerSeries C := fun q => tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0) with hlamdef
  have hlamN' : ∀ N q, ∀ m < V.l ^ N, PowerSeries.coeff m (lam q) = PowerSeries.coeff m (lamN N q) := by
    intro N q m hm
    have e : lamN N q = tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inr q)) +
        alongCv (γN N) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) •
          tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inl c)) else 0) := by
      rw [h2N N q]
      abel
    rw [e, hlamdef]
    show PowerSeries.coeff m (tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_add (f := _), map_add (f := _), map_sum, map_sum, htyN N _ m hm,
      coeff_alongCv_congr hγ0 (fun i => (hγN N i).1) (fun i => hγN' N i) _ m hm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m hm]
    · rfl
  have hlamI : IsCv V lam := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlamN' 0 q 0 (by simp),
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlamN 0 q).1
    · rw [hlamN' n q n (Nat.lt_pow_self (by omega))]
      exact (hlamN n q).2 n
  refine ⟨γ, lam, hγI, hlamI, hlgγ, ?_⟩
  intro q
  have hab : ∀ a b c : PowerSeries C, a = (a + b - c) - b + c := by
    intro a b c
    abel
  exact hab _ _ _

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Rename

theorem prod_X_rename {σ τ : Type} (φ : σ → τ) (e : σ →₀ ℕ) :
    (e.prod fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) =
      MvPowerSeries.monomial (e.mapDomain φ) 1 := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg,
      Finsupp.mapDomain_add, MvPowerSeries.monomial_mul_monomial, one_mul]
  · intro a b
    rw [Finsupp.prod_single_index (h := fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) (pow_zero _),
      Finsupp.mapDomain_single]
    simp only [MvPowerSeries.X_pow_eq]

theorem coeff_subst_rename_inj {σ τ : Type} [Finite σ] (φ : σ → τ) (hφ : Function.Injective φ)
    (F : MvPowerSeries σ C) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e.mapDomain φ)
      (MvPowerSeries.subst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) F) = MvPowerSeries.coeff e F := by
  have hA : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst hA, finsum_eq_single _ e]
  · rw [prod_X_rename, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    intro h
    exact hd (Finsupp.mapDomain_injective hφ h).symm

variable {dd : ℕ}

theorem snd_injective_fin_one : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := fun p q h => Prod.ext (Subsingleton.elim _ _) h

theorem hasSubst_snd : MvPowerSeries.HasSubst
    (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp)

theorem uncurry_eq_subst (f : PS C 1 dd) :
    un1 f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) f := by
  ext μ
  have h := coeff_subst_rename_inj (C := C) (fun p : Fin 1 × Fin dd => p.2) snd_injective_fin_one f
    (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  have e1 : (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).mapDomain (fun p : Fin 1 × Fin dd => p.2) = μ := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  rw [e1] at h
  exact h.symm

theorem subst_singlePointUncurry {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hasSubst_snd hA]
  congr 1
  funext p
  show MvPowerSeries.subst a (MvPowerSeries.X p.2) = a p.2
  rw [MvPowerSeries.subst_X hA]

theorem subst_oneVariableUncurry_eq_subst {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by
  have hB : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hB hasSubst_snd]
  congr 1
  funext s
  rw [uncurry_eq_subst]

theorem uncurry_X (i : Fin dd) : un1 (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd) = MvPowerSeries.X i := by
  rw [uncurry_eq_subst, MvPowerSeries.subst_X hasSubst_snd]

theorem eval_single_eq_subst {n : ℕ} (a : Pt C n dd) (f : PS C 1 dd) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  simp only [ev]
  congr 1
  funext p
  rw [Subsingleton.elim p.1 0]
  rfl

theorem uncurry_comp {φ a : Pt C 1 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (a j)) (un1 (φ i)) = un1 (comp1 φ a i) := by
  have hu : ∀ j, MvPowerSeries.constantCoeff (un1 (a j)) = 0 := by
    intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (a j) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha j
  rw [subst_singlePointUncurry hu]
  show _ = un1 (ev ![a] (φ i))
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => a p.2) (fun s => ha s.2)]

end Rename

section Inst

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.lg_const (i : Fin dd) : MvPowerSeries.constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_X] at h
  exact h

end Inst

end Formalism.L2.FormalSeriesBounds

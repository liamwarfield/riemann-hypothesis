module

public import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
public import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroFirstThenZero
public import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroDoubleMultiplicationPair
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.MmOfUnitMul
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfLinear

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MaximalIdealCongruence RowTiePE0 RowTiePProj RowTiePLSmall

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem coeff_aOf (Y : FBChart C V O dd) (u : Fin dd → C) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (Y.aOf u) = ∑ i, u i ^ V.l * MvPowerSeries.coeff
      (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1 := rfl

theorem aLin_mul_left (Y : FBChart C V O dd) (c : C) (u v : Fin dd → C) :
    Y.aLin (fun i => c * u i) v = c ^ V.l * Y.aLin u v := by
  unfold FBChart.aLin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_aOf, coeff_aOf, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring

theorem aLin_mul_right (Y : FBChart C V O dd) (c : C) (u v : Fin dd → C) :
    Y.aLin u (fun i => c * v i) = c * Y.aLin u v := by
  unfold FBChart.aLin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aLin_sum_right (Y : FBChart C V O dd) {ι : Type} [Fintype ι] (u : Fin dd → C) (b : ι → C)
    (e : ι → Fin dd → C) : Y.aLin u (∑ c, b c • e c) = ∑ c, b c * Y.aLin u (e c) := by
  unfold FBChart.aLin
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aLin_int (Y : FBChart C V O dd) {u v : Fin dd → C} (hu : ∀ i, V.Ge 0 (u i)) (hv : ∀ i, V.Ge 0 (v i)) :
    V.Ge 0 (Y.aLin u v) :=
  VF.Ge.sum fun j _ => (hv j).mul_int (intS_aOf Y (first_unit_series_integral C V O dd Y) u hu _)

theorem mm_of_unit_mul {c x : C} (hc : V.v c = 0) (h : V.MM (c * x)) : V.MM x := by
  unfold VF.MM at *
  rwa [V.v.map_mul, hc, zero_add] at h

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) : V.MM (A ^ V.l - B ^ V.l) := by
  have h1 := mm_add_pow (V := V) hB (hA.sub hB)
  have h2 : V.MM ((A - B) ^ V.l) := mm_pow h V.l_prime.ne_zero
  have e : A ^ V.l - B ^ V.l = ((B + (A - B)) ^ V.l - B ^ V.l - (A - B) ^ V.l) + (A - B) ^ V.l := by
    rw [add_sub_cancel]; ring
  rw [e]
  exact mm_add h1 h2

section Self

variable {d : ℕ} {I0 : Type} [Fintype I0]

theorem gm_frob (Y : FBChart C V O dd) (p : SelfData Y d I0) (a : ZMod d) (r s : Fin 2) :
    V.MM (p.gm (a + 1) r s - p.gm a r s ^ V.l) := by
  obtain ⟨M, hM⟩ := p.gm_lim 1
  have h0 := hM a r s
  have h1 := hM (a + 1) r s
  rw [Nat.cast_one] at h0 h1
  have e : p.gm (a + 1) r s - p.gm a r s ^ V.l =
      (p.gm (a + 1) r s - p.em (a + 1) (M r s)) + (p.em (a + 1) (M r s) - p.em a (M r s) ^ V.l) -
        (p.gm a r s ^ V.l - p.em a (M r s) ^ V.l) := by ring
  rw [e]
  exact mm_sub (mm_add (maximal_of_valuation_ge_one h1) (p.em_frob a _))
    (mm_pow_sub (SelfData.gm_int Y p a r s) (p.em_int a _) (maximal_of_valuation_ge_one h0))

end Self

theorem adj_seq (hAdj : ALinAdjSt) (Y : FBChart C V O dd) (s : ℕ → O) (h1 : ActCv Y s)
    (h2 : ActCv Y (fun n => star (s n))) :
    ∃ e eb : Pt C 1 dd,
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) ∧
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (eb i) - MvPowerSeries.coeff μ (Y.B.A.act (star (s n)) i))) ∧
      (∀ i, IntS V (eb i)) ∧
      ∀ u : Fin dd → C, (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
        V.MM (Y.aLin (linAct e u) v - Y.aLin u (linAct eb v)) := by
  obtain ⟨e, eb, hi, hib, he, heb, hhom, hexp⟩ := endomorphism_limit_integral Y s h1 h2
  refine ⟨e, eb, he, heb, hib, ?_⟩
  exact hAdj C V O dd Y e eb hi hib (const_of_lim Y (tends_of_endomorphism_limit Y he))
    (const_of_lim Y (a := fun n => star (s n)) (tends_of_endomorphism_limit Y (a := fun n => star (s n)) heb)) hhom hexp

theorem linAct_of_lim (Y : FBChart C V O dd) {s : ℕ → O} {e : Pt C 1 dd}
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i)))
    {u : Fin dd → C} {χ : ℕ → C} {c : C} (hu : ∀ n, linAct (Y.B.A.act (s n)) u = χ n • u) (hχ : Tends V χ c) :
    linAct e u = c • u := by
  funext i
  have L := linAct_tends (tends_of_endomorphism_limit Y he) u i
  have eq : (fun n => linAct (Y.B.A.act (s n)) u i) = fun n => χ n * u i := funext fun n => by
    rw [hu]; rfl
  rw [eq] at L
  exact L.unique (hχ.mul (tends_const _))

theorem actCv_const (Y : FBChart C V O dd) (β : O) : ActCv Y (fun _ => β) := fun N _ _ =>
  ⟨0, fun _ _ => by rw [sub_self]; exact VF.Ge.zero _⟩

theorem linAct_int {φ : Pt C 1 dd} (hφ : ∀ i, IntS V (φ i)) {v : Fin dd → C} (hv : ∀ i, V.Ge 0 (v i)) (i : Fin dd) :
    V.Ge 0 (linAct φ v i) :=
  VF.Ge.sum fun j _ => (hφ i _).mul_int (hv j)

section Self2

variable {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0]

theorem orth (hAdj : ALinAdjSt) (Y : FBChart C V O dd) (p : SelfData Y d I0) (a0 : ZMod d) (u0 : Fin dd → C)
    (hu0 : ∀ i, V.Ge 0 (u0 i)) (heig : ∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0) (hV1 : Y.FirstVanishingAt u0)
    (q : I0) (hq : a0 + 1 ≠ p.ty0 q + p.hd) : V.MM (Y.aLin u0 (p.e q)) := by
  obtain ⟨β, hβ⟩ := p.em_sep (a0 + 1) (p.ty0 q + p.hd) hq
  obtain ⟨e, eb, he, heb, -, hadj⟩ := adj_seq hAdj Y (fun _ => β) (actCv_const Y β) (actCv_const Y (star β))
  have e1 : linAct e u0 = p.em a0 β • u0 := linAct_of_lim Y he (fun _ => heig β) (tends_const _)
  have e2 : linAct eb (p.e q) = p.em (p.ty0 q + p.hd) β • p.e q :=
    linAct_of_lim Y (s := fun _ => star β) heb (fun _ => by rw [p.e_eig, p.em_conj]) (tends_const _)
  have h := hadj u0 hu0 hV1 (p.e q) (p.e_int q)
  rw [e1, e2] at h
  have f1 : Y.aLin (p.em a0 β • u0) (p.e q) = p.em a0 β ^ V.l * Y.aLin u0 (p.e q) :=
    aLin_mul_left Y (p.em a0 β) u0 (p.e q)
  have f2 : Y.aLin u0 (p.em (p.ty0 q + p.hd) β • p.e q) = p.em (p.ty0 q + p.hd) β * Y.aLin u0 (p.e q) :=
    aLin_mul_right Y _ u0 (p.e q)
  rw [f1, f2] at h
  have hL := aLin_int Y hu0 (p.e_int q)
  refine mm_of_unit_mul hβ ?_
  have e3 : (p.em (a0 + 1) β - p.em (p.ty0 q + p.hd) β) * Y.aLin u0 (p.e q) =
      (p.em (a0 + 1) β - p.em a0 β ^ V.l) * Y.aLin u0 (p.e q) +
        (p.em a0 β ^ V.l * Y.aLin u0 (p.e q) - p.em (p.ty0 q + p.hd) β * Y.aLin u0 (p.e q)) := by ring
  rw [e3]
  exact mm_add (mm_mul_ge (p.em_frob a0 β) hL) h

theorem onType (Y : FBChart C V O dd) (p : SelfData Y d I0) (g : Fin 2) (a0 : ZMod d) (u0 : Fin dd → C)
    (hu0 : ∀ i, V.Ge 0 (u0 i)) (q : I0) (hq : a0 + 1 = p.ty0 q + p.hd)
    (hc0 : V.MM (∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i) (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i))) :
    V.MM (Y.aLin u0 (p.e q)) := by
  have hty : p.ty0 q = a0 + 1 + p.hd := by
    rw [hq, add_assoc, p.hd_two, add_zero]
  have hL := aLin_int Y hu0 (p.e_int q)
  have e1 : ∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i) (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i) =
      (∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) * Y.aLin u0 (p.e q) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [aLin_mul_left, aLin_mul_right, hty]
    ring
  rw [e1] at hc0
  have hS : V.MM (1 - ∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) := by
    rw [← SelfData.gm_pair Y p (a0 + 1) g, ← Finset.sum_sub_distrib]
    refine mm_sum _ _ fun col _ => ?_
    rw [← sub_mul]
    exact mm_mul_ge (gm_frob Y p a0 col g) (SelfData.gm_int Y p _ _ _)
  have e2 : Y.aLin u0 (p.e q) =
      (1 - ∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) * Y.aLin u0 (p.e q) +
        (∑ col, p.gm a0 col g ^ V.l * p.gm (a0 + 1 + p.hd) col (1 - g)) * Y.aLin u0 (p.e q) := by ring
  rw [e2]
  exact mm_add (mm_mul_ge hS hL) hc0

end Self2

end SelfLinear


open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MaximalIdealCongruence RowTiePE0 RowTiePProj RowTiePLSmall SelfLinear in
theorem noLin_self (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) {C : Type} [Field C] [CharZero C] {V : VF C}
    {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) (g : Fin 2) (a0 : ZMod d) (u0 : Fin dd → C) (hu0 : ∀ i, V.Ge 0 (u0 i))
    (heig : ∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0) (hV1 : Y.FirstVanishingAt u0)
    (hc0 : ∀ q : I0, V.MM (∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i)
      (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i))) :
    ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) → V.MM (Y.aLin u0 v) := by
  open SelfLinear Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MaximalIdealCongruence RowTiePE0 RowTiePProj RowTiePLSmall in
  intro v hv
  have hq : ∀ q, V.MM (Y.aLin u0 (p.e q)) := fun q => by
    by_cases h : a0 + 1 = p.ty0 q + p.hd
    · exact onType Y p g a0 u0 hu0 q h (hc0 q)
    · exact orth hAdj Y p a0 u0 hu0 heig hV1 q h
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hl2 : 2 ≤ V.l := V.l_prime.two_le
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx _
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have cvA : ActCv Y (fun n => ε ^ V.l ^ n) := fun N i μ => by
    obtain ⟨n0, h⟩ := lSmall_holds C V O dd Y (fun n => ε ^ V.l ^ (n + 1)) (fun n => ε ^ V.l ^ n)
      (pow_cong hl2 hε) N i μ
    exact ⟨n0, h⟩
  have cvB : ActCv Y (fun n => star ε ^ V.l ^ n) := fun N i μ => by
    obtain ⟨n0, h⟩ := lSmall_holds C V O dd Y (fun n => star ε ^ V.l ^ (n + 1)) (fun n => star ε ^ V.l ^ n)
      (pow_cong hl2 hεs) N i μ
    exact ⟨n0, h⟩
  have sA : (fun n => star (ε ^ V.l ^ n)) = fun n => star ε ^ V.l ^ n := funext fun n => star_pow _ _
  obtain ⟨e, eb, he, heb, hib, hadj⟩ := adj_seq hAdj Y (fun n => ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  simp only [star_pow] at heb
  have e1 : linAct e u0 = (1 : C) • u0 :=
    linAct_of_lim Y he (χ := fun n => p.em a0 ε ^ V.l ^ n) (fun n => by rw [heig, map_pow]) (tends_pow_one (hε1 a0))
  rw [one_smul] at e1
  obtain ⟨b, hb⟩ := hPL C V O dd Y d I0 p (star ε) hεs hεs1 hεsx eb heb v
  obtain ⟨wd, hwd, hsat⟩ := p.e_sat
  have hbint : ∀ c, V.Ge 0 (b c) := by
    intro c
    have e : b c = ∑ x, linAct eb v x * wd x c := by
      rw [hb]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ c', ∑ x, b c' * p.e c' x * wd x c = b c' * (if c' = c then 1 else 0) := by
        intro c'
        rw [← hsat c' c, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e]
    exact VF.Ge.sum fun x _ => (linAct_int hib hv x).mul_int (hwd x c)
  have h := hadj u0 hu0 hV1 v hv
  rw [e1, hb, aLin_sum_right] at h
  have e2 : Y.aLin u0 v = (Y.aLin u0 v - ∑ c, b c * Y.aLin u0 (p.e c)) + ∑ c, b c * Y.aLin u0 (p.e c) := by ring
  rw [e2]
  exact mm_add h (mm_sum _ _ fun c _ => mm_mul_ge' (hbint c) (hq c))

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfCore
section -- merged from Formalism.LocalToGlobal.CharacterGerms.UncurryLinearCombination
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem FBChart.uncurry_log_constantCoeff_chart (Y : FBChart C V O dd) (i : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0 := by
  rw [constantCoeff_uncurry, Y.lg_const]

theorem FBChart.uncurry_exp_log_eq_X (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  rw [uncurry_comp Y.lg_const, Y.ex_lg]
  exact uncurry_X i

theorem FBChart.uncurry_linear_combination (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (un1 (Y.lg i)) =
      MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hμ), ← uncurry_X i]
  rfl

theorem FBChart.ex_lg_at' (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => Y.uncurry_log_constantCoeff_chart j
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', Y.uncurry_exp_log_eq_X, MvPowerSeries.subst_X hA']

theorem hom_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) (μ : Fin 2 →₀ ℕ) (hμ0 : μ 0 < V.l) (hμ1 : μ 1 < V.l) :
    MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)) = 0 := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hX : ∀ k : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 2) C) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X k
  have hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 := by
    rw [map_add (f := _), hX 0, hX 1, add_zero]
  have hP0 : ∀ (k : Fin 2) (j : Fin dd), MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X k) (γ j)) = 0 :=
    fun k j => const_cvAt (hX k) (hγ0 j)
  have hQ0 : ∀ j, MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j)) = 0 :=
    fun j => const_cvAt hS (hγ0 j)
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP0 q.1 q.2
  have hFP0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP0 q.1 q.2) (Y.B.G.const j)
  have hAt : ∀ (s : MvPowerSeries (Fin 2) C), MvPowerSeries.constantCoeff s = 0 → ∀ j,
      Agr (V.l ^ 2) (MvPowerSeries.subst (fun j' => cvAt s (γ j')) (un1 (Y.lg j))) (U j • s) := by
    intro s hs j
    rw [subst_cvAt hs hγ0, ← cvAt_smul_X hs]
    exact agr_subst_right (a := fun _ : Unit => s) (fun _ => hs) (hlg j)
  have hsum : ∀ j, Agr (V.l ^ 2)
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j)))
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) := by
    intro j
    refine ((hAt _ (hX 0) j).add (hAt _ (hX 1) j)).trans ?_
    rw [← smul_add]
    exact (hAt _ hS j).symm
  have e1 := Y.ex_lg_at' _ hFP0 i
  have e1' : (fun j => MvPowerSeries.subst
      (fun j' => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j'))
      (un1 (Y.lg j))) = fun j =>
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j)) := by
    funext j
    exact lg_addOf Y (fun k j' => cvAt (MvPowerSeries.X k) (γ j')) hP0 j
  rw [e1'] at e1
  have e2 := Y.ex_lg_at' _ hQ0 i
  have hc : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) = 0 := by
    intro j
    rw [map_add (f := _), MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 0 j') (fun j' => hP0 0 j') (Y.uncurry_log_constantCoeff_chart j),
      MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 1 j') (fun j' => hP0 1 j') (Y.uncurry_log_constantCoeff_chart j),
      add_zero]
  have hc' : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0) hQ0 (Y.uncurry_log_constantCoeff_chart j)
  have hag := agr_subst_left hc hc' hsum (un1 (Y.ex i))
  rw [e1, e2] at hag
  have hdeg : μ.degree < V.l ^ 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    nlinarith
  rw [map_sub, sub_eq_zero]
  exact hag μ hdeg

theorem coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 (un1 (Y.lg i)) (MvPowerSeries.X i) := fun e he => Y.uncurry_linear_combination i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (hlg i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

theorem agr_of_ty {I : Fin 2 → Type} [∀ g, Fintype (I g)] {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (cf : I g → C) :
    Agr (V.l ^ 2) (∑ c : I g, cf c • tyS V.l (fun s => x s (Sum.inl c)))
      ((∑ c, cf c * w c) • (MvPowerSeries.X () : PowerSeries C)) := by
  intro e he
  have hl := V.l_prime.two_le
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [Finsupp.degree_single] at he
  change PowerSeries.coeff n _ = PowerSeries.coeff n _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul, coeffX']
  simp only [map_smul, smul_eq_mul, tyS_good_coeff h0 h1 hl _ n he]
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn1]

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def NoLinSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (g : Fin 2) (a0 : ZMod d) (u0 : Fin dd → C), (∀ i, V.Ge 0 (u0 i)) →
    (∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0) → Y.FirstVanishingAt u0 →
    (∀ q : I0, V.MM (∑ col, Y.aLin (fun i => p.gm a0 col g * u0 i)
      (fun i => p.gm (p.ty0 q) col (1 - g) * p.e q i))) →
    ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) → V.MM (Y.aLin u0 v)

namespace SelfAdjointTop

open MaximalIdealCongruence

variable {C : Type} [Field C]

theorem not_mm_one {V : VF C} : ¬ V.MM (1 : C) := by
  intro h
  have h1 : (0 : WithTop ℝ) < V.v 1 := h
  rw [AddValuation.map_one] at h1
  exact lt_irrefl _ h1

theorem mm_of_unit_mul {V : VF C} {c x : C} (hc : ¬ V.MM c) (hc0 : V.Ge 0 c) (h : V.MM (c * x)) : V.MM x := by
  have hc0' : (0 : WithTop ℝ) ≤ V.v c := hc0
  have hc' : ¬ (0 : WithTop ℝ) < V.v c := hc
  have h0 : V.v c = 0 := le_antisymm (not_lt.mp hc') hc0'
  have h1 : (0 : WithTop ℝ) < V.v (c * x) := h
  rw [AddValuation.map_mul, h0, zero_add] at h1
  exact h1

theorem tyS_coeff_l {l : ℕ} (hl : 2 ≤ l) (f : ℕ → C) : PowerSeries.coeff l (tyS l f) = f 1 := by
  unfold tyS
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 1]
  · rw [pow_one, if_pos rfl]
  · intro s _ hs
    rw [if_neg]
    intro h
    apply hs
    have h' : l ^ s = l ^ 1 := by rw [pow_one]; exact h
    exact Nat.pow_right_injective hl h'
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem linAct_comb {dd : ℕ} {ι : Type} [Fintype ι] (φ : Pt C 1 dd) (w : ι → C) (e : ι → Fin dd → C) :
    linAct φ (fun i => ∑ c, w c * e c i) = fun i => ∑ c, w c * linAct φ (e c) i := by
  funext i
  unfold linAct
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem coeff_aOf_smul (Y : FBChart C V O dd) (c : C) (u : Fin dd → C) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (Y.aOf fun i => c * u i) = c ^ V.l * MvPowerSeries.coeff ν (Y.aOf u) := by
  show ∑ i, (c * u i) ^ V.l * _ = c ^ V.l * ∑ i, u i ^ V.l * _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, mul_assoc]

theorem aLin_single (Y : FBChart C V O dd) (u : Fin dd → C) (j : Fin dd) :
    Y.aLin u (Pi.single j 1) = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u) := by
  unfold FBChart.aLin
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem first_vanishing_of_unit_smul (Y : FBChart C V O dd) {c : C} (hc : ¬ V.MM c) (hc0 : V.Ge 0 c) {u : Fin dd → C}
    (h : Y.FirstVanishingAt fun i => c * u i) : Y.FirstVanishingAt u := by
  intro k
  have hk := h k
  have e : ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * (c * u i) ^ V.l =
      c ^ V.l * ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * u i ^ V.l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
  rw [e] at hk
  exact mm_of_unit_mul (fun h' => hc (mm_of_pow h')) (hc0.pow _) hk

end SelfAdjointTop


open SelfAdjointTop MaximalIdealCongruence in
theorem rank_maximal_self_core (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hNL : NoLinSelfSt) :
    RankMaximalSelfOfNondegenerate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p hN hrk Hc hAlt g a hbig w x hG hc0 c
  by_contra hwc
  have hl := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, hlg, hfil⟩ := ((Y.rawSelf p).mem_tySet_iff V g x).1 hG.1.1
  have h0 : x 0 = Sum.elim w 0 := hG.1.2.1
  have h1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2
  have hγ0 : ∀ s, MvPowerSeries.constantCoeff (γ s) = 0 := fun s => (hγ s).1

  obtain ⟨a0, ha0⟩ : ∃ a0 : ZMod d, ∀ c : I0, w c ≠ 0 → p.ty0 c = a0 := by
    refine ⟨if g = 0 then a else a + p.hd, fun c' hw => ?_⟩
    by_contra hne
    apply hw
    have h2 := hG.1.2.2 0 (Sum.inl c') (by
      show (if g = 0 then p.ty0 c' else p.ty0 c' + p.hd) ≠ a + ((0 : ℕ) : ZMod d)
      rw [Nat.cast_zero, add_zero]
      by_cases hg : g = 0
      · rw [if_pos hg] at hne ⊢
        exact hne
      · rw [if_neg hg] at hne ⊢
        intro h3
        apply hne
        rw [← h3, add_assoc, p.hd_two, add_zero])
    rw [h0] at h2
    exact h2
  have hwI : ∀ c : I0, V.Ge 0 (w c) := fun c' => by
    have h2 := (Hc g).t2 x hG.1.1 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) (Sum.inl c')
    rw [h0] at h2
    exact h2
  let u0 : Fin dd → C := fun i => ∑ c : I0, w c * p.e c i
  let U : Fin 2 → Fin dd → C := fun col i => p.gm a0 col g * u0 i
  let γc : Fin 2 → Fin dd → PowerSeries C := fun col i => γ (col, i)
  have hu0I : ∀ i, V.Ge 0 (u0 i) := fun i => VF.Ge.sum fun c' _ => VF.Ge.mul_int (hwI c') (p.e_int c' i)
  have hgI : ∀ b r s, V.Ge 0 (p.gm b r s) := fun b r s => SelfData.gm_int Y p b r s
  have hUI : ∀ col i, V.Ge 0 (U col i) := fun col i => VF.Ge.mul_int (hgI _ _ _) (hu0I i)
  have hU : ∀ col i, ∑ c : I0, (Y.rawSelf p).u g c (col, i) * w c = U col i := by
    intro col i
    show ∑ c : I0, (p.gm (p.ty0 c) col g * p.e c i) * w c = p.gm a0 col g * ∑ c : I0, w c * p.e c i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    by_cases hw : w c' = 0
    · rw [hw]; ring
    · rw [ha0 c' hw]; ring
  have hcv : ∀ col, IsCv V (γc col) := fun col i => hγ (col, i)
  have hcol : ∀ (col : Fin 2) (f : MvPowerSeries (Fin dd) C), alongCv γ (inCol col f) = alongCv (γc col) f :=
    fun col f => subst_inCol hγ0 col f
  have hLg : ∀ col, Y.LgLin (γc col) (U col) := by
    intro col i
    have h2 : alongCv (γc col) (un1 (Y.lg i)) =
        ∑ c : I0, (Y.rawSelf p).u g c (col, i) • tyS V.l (fun s => x s (Sum.inl c)) := by
      rw [← hcol]
      exact hlg (col, i)
    rw [h2, ← hU]
    exact agr_of_ty (I := fun _ => I0) h0 h1 _

  obtain ⟨col, hcolU⟩ : ∃ col, ¬ V.MM (p.gm a0 col g) := by
    by_contra hall
    push Not at hall
    apply SelfAdjointTop.not_mm_one (V := V)
    rw [← SelfData.gm_pair Y p a0 g]
    exact mm_sum _ _ fun r _ => mm_mul_ge (hall r) (hgI _ _ _)
  have hV1U : ∀ r, Y.FirstVanishingAt (U r) := fun r => hV1 C V O dd Y (γc r) (U r) (hcv r) (hLg r)
  have hV1u : Y.FirstVanishingAt u0 := SelfAdjointTop.first_vanishing_of_unit_smul Y hcolU (hgI _ _ _) (hV1U col)
  have heig : ∀ β, linAct (Y.B.A.act β) u0 = p.em a0 β • u0 := by
    intro β
    show linAct (Y.B.A.act β) (fun i => ∑ c : I0, w c * p.e c i) = _
    rw [SelfAdjointTop.linAct_comb]
    funext i
    show ∑ c : I0, w c * linAct (Y.B.A.act β) (p.e c) i = p.em a0 β * ∑ c : I0, w c * p.e c i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [p.e_eig]
    show w c' * (p.em (p.ty0 c') β * p.e c' i) = _
    by_cases hw : w c' = 0
    · rw [hw]; ring
    · rw [ha0 c' hw]; ring

  have hlink : ∀ q : I0, V.MM (∑ r, Y.aLin (U r) (fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)) := by
    intro q
    have hq := congrArg (PowerSeries.coeff V.l) (hfil q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SelfAdjointTop.tyS_coeff_l hl, map_add (f := _), map_sub, map_sum] at hq
    have hz : ∑ c : I0, PowerSeries.coeff V.l (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun c' _ => ?_
      split_ifs
      · rw [map_smul, SelfAdjointTop.tyS_coeff_l hl, h1 c', smul_zero]
      · rw [map_zero]
    rw [hz, add_zero] at hq
    have hsg : alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) =
        ∑ r, alongCv (γc r) (un1 (Y.sgP fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)) := by
      rw [Y.rawSelf_sg p, Fin.sum_univ_two, Fin.sum_univ_two, ← hcol, ← hcol, Y.rawCol_sg, Y.rawCol_sg]
      exact MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsg, map_sum] at hq
    have hc := hc0 q
    have hc' : V.MM ((V.l : C) * x 1 (Sum.inr q)) := hc
    rw [hq] at hc'
    have hvI : ∀ r i, V.Ge 0 (p.gm (p.ty0 q) r (1 - g) * p.e q i) :=
      fun r i => VF.Ge.mul_int (hgI _ _ _) (p.e_int q i)
    have hL := fun r => hC0 C V O dd Y (γc r) (U r) (hcv r) (hLg r) _ (hvI r)
    have e : ∑ r, Y.aLin (U r) (fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i) =
        (V.l : C) * PowerSeries.coeff V.l (lam q) -
          (V.l : C) * (PowerSeries.coeff V.l (lam q) -
            ∑ r, PowerSeries.coeff V.l (alongCv (γc r) (un1 (Y.sgP fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)))) -
          ∑ r, ((V.l : C) * PowerSeries.coeff V.l
            (alongCv (γc r) (un1 (Y.sgP fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i))) -
              Y.aLin (U r) (fun i => p.gm (p.ty0 q) r (1 - g) * p.e q i)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [e]
    exact MaximalIdealCongruence.mm_sub (MaximalIdealCongruence.mm_sub (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)) hc') (mm_sum _ _ fun r _ => hL r)
  have hnl := hNL C V O dd Y d I0 p g a0 u0 hu0I heig hV1u hlink

  have hfun : (fun i => PowerSeries.coeff 1 (γc col i)) = U col :=
    funext fun i => coeff1_of_lgLin Y (hcv col) (hLg col) i
  obtain ⟨b, hb, hbc⟩ := first_step_second_half C V Y.algClosed dd Y.B.G Y.intF (Y.aOf (U col)) (Y.chartLinearTerm (U col))
    (intS_aOf Y (first_unit_series_integral C V O dd Y) _ (hUI col)) (intS_c2lin Y _ (hUI col))
    (fun j => by
      rw [SelfAdjointTop.coeff_aOf_smul Y (p.gm a0 col g) u0, ← SelfAdjointTop.aLin_single]
      refine MaximalIdealCongruence.mm_mul_ge' ((hgI _ _ _).pow _) (hnl _ fun i => ?_)
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact VF.Ge.one
      · rw [Pi.single_eq_of_ne hij]; exact VF.Ge.zero 0)
    (hFE C V O dd Y (U col) (hUI col) (hV1U col))
  refine hN (γc col) (hcv col) ?_ ?_ ⟨b, hb, ?_⟩
  · by_contra hall
    push Not at hall
    apply hwc
    have hall' : ∀ i, V.MM (U col i) := fun i => by rw [← congrFun hfun i]; exact hall i
    have hu0M : ∀ i, V.MM (u0 i) := fun i => SelfAdjointTop.mm_of_unit_mul hcolU (hgI _ _ _) (hall' i)
    obtain ⟨wd, hwd, hsat⟩ := p.e_sat
    have e : w c = ∑ i, u0 i * wd i c := by
      show w c = ∑ i, (∑ c' : I0, w c' * p.e c' i) * wd i c
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ c' : I0, ∑ i, w c' * p.e c' i * wd i c = w c' * (if c' = c then 1 else 0) := by
        intro c'
        rw [← hsat c' c, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e]
    exact mm_sum _ _ fun i _ => mm_mul_ge (hu0M i) (hwd i c)
  · intro i μ hμ0 hμ1
    rw [hom_of_lgLin Y (hcv col) (hLg col) i μ hμ0 hμ1]
    exact mm_zero
  · rw [hfun]
    exact hbc

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

theorem noLinSelf_of (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) : NoLinSelfSt :=
  fun _ _ _ _ _ _ _ _ Y _ _ _ _ p g a0 u0 hu0 heig hV1 hc0 => noLin_self hAdj hPL Y p g a0 u0 hu0 heig hV1 hc0

theorem rank_maximal_self_of_projection (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) :
    RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_core hV1 hFE hC0 (noLinSelf_of hAdj hPL)

theorem rank_maximal_self_of_eigen (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hAdj : ALinAdjSt)
    (hE : RowTiePKey.KeyEigSt) : RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_of_projection hV1 hFE hC0 hAdj (projLieSelf_of hE)

end Formalism.L2.FormalSeriesBounds

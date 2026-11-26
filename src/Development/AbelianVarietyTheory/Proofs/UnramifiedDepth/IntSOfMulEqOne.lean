module

public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CocycleIntegral
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeCocycle

open MvPowerSeries

variable {C : Type} [Field C]

def valRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem intS_iff_ig (V : VF C) {σ : Type} (f : MvPowerSeries σ C) : IntS V f ↔ f ∈ Ig (valRing V) C σ := by
  constructor
  · intro hf
    let g : MvPowerSeries σ (valRing V) := fun n => ⟨coeff n f, hf n⟩
    refine RingHom.mem_range.2 ⟨g, ?_⟩
    ext n
    rw [coeff_map]
    rfl
  · intro hf n
    obtain ⟨g, rfl⟩ := RingHom.mem_range.1 hf
    rw [coeff_map]
    exact (coeff n g).2

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}

omit [CharZero C] in
theorem map_self {σ : Type} (f : MvPowerSeries σ C) : MvPowerSeries.map (algebraMap C C) f = f := by
  ext n
  rw [coeff_map]
  rfl

end GlobalTheory.GaugeCocycle
end
end

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.GaugeCocycle ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.RowVal

open MvPowerSeries

variable {C : Type} [Field C]

theorem mvExp_eq_subst [CharZero C] {σ : Type} {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    mvExp F = PowerSeries.subst F (PowerSeries.exp C) := by
  classical
  ext m
  have hS : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show (∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hk'
    apply hk
    have h1 : m.degree < k := by simpa using hk'
    have h0 : coeff m (F ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hF)
      exact_mod_cast h1
    rw [h0, smul_zero]

theorem mvExp_add [CharZero C] {σ : Type} {F G : MvPowerSeries σ C} (hF : constantCoeff F = 0)
    (hG : constantCoeff G = 0) : mvExp (F + G) = mvExp F * mvExp G := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst hG, mvExp_eq_subst (by rw [map_add (f := _), hF, hG, add_zero]),
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hF hG]

theorem mvExp_zero' [CharZero C] {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  rw [mvExp_eq_subst (map_zero _), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]

theorem mvExp_sum [CharZero C] {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C}
    (hF : ∀ i, constantCoeff (F i) = 0) : mvExp (∑ i ∈ s, F i) = ∏ i ∈ s, mvExp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero']
  | insert a s ha ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert ha, Finset.prod_insert ha, mvExp_add (hF a) (by simp [map_sum, hF]), ih]

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add (f := _), constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem subst_mvExp [CharZero C] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    subst a (mvExp F) = mvExp (subst a F) := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst (by rw [cc_subst ha, hF]), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hF]

theorem intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) :=
  (intS_iff_ig V _).2 (ig_subst (fun s => (intS_iff_ig V _).1 (hi s)) ha ((intS_iff_ig V _).1 hF))

theorem intS_X {V : VF C} {σ : Type} (s : σ) : IntS V (X s : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (ig_X s)

theorem intS_one {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (one_mem _)

theorem intS_zero {V : VF C} {σ : Type} : IntS V (0 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (zero_mem _)

theorem intS_mul {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) :=
  (intS_iff_ig V _).2 (mul_mem ((intS_iff_ig V _).1 hF) ((intS_iff_ig V _).1 hG))

theorem intS_prod {V : VF C} {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C} (hF : ∀ i, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) :=
  (intS_iff_ig V _).2 (prod_mem fun i _ => (intS_iff_ig V _).1 (hF i))

theorem intS_of_mul_eq_one {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F)
    (h1 : constantCoeff F = 1) (hFG : F * G = 1) : IntS V G := by
  obtain ⟨U, hU⟩ := RingHom.mem_range.1 ((intS_iff_ig V _).1 hF)
  have hU1 : constantCoeff U = 1 := by
    apply Subtype.ext
    have e := congrArg constantCoeff hU
    rw [constantCoeff_map, h1] at e
    exact e
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 := MvPowerSeries.mul_invOfUnit U 1 (by simp [hU1])
  have e : G = MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1) := by
    have h2 := congrArg (MvPowerSeries.map (σ := σ) (algebraMap (valRing V) C)) hinv
    rw [map_mul, map_one, hU] at h2
    calc G = G * (F * MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1)) := by
          rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm G F, hFG, one_mul]
  rw [e]
  exact (intS_iff_ig V _).2 (ig_map _)

def logInt [CharZero C] (V : VF C) (σ : Type) : AddSubgroup (MvPowerSeries σ C) where
  carrier := {F | constantCoeff F = 0 ∧ IntS V (mvExp F)}
  zero_mem' := ⟨map_zero _, by rw [mvExp_zero']; exact intS_one⟩
  add_mem' := fun {F G} hF hG => ⟨by rw [map_add (f := _), hF.1, hG.1, add_zero], by
    rw [mvExp_add hF.1 hG.1]; exact intS_mul hF.2 hG.2⟩
  neg_mem' := fun {F} hF => ⟨by rw [map_neg, hF.1, neg_zero], by
    refine intS_of_mul_eq_one hF.2 ?_ ?_
    · rw [mvExp_eq_subst hF.1, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp hF.1]
    · rw [← mvExp_add hF.1 (by rw [map_neg, hF.1, neg_zero]), add_neg_cancel, mvExp_zero']⟩

theorem mem_logInt [CharZero C] {V : VF C} {σ : Type} {F : MvPowerSeries σ C} :
    F ∈ logInt V σ ↔ constantCoeff F = 0 ∧ IntS V (mvExp F) := Iff.rfl

theorem logInt_subst [CharZero C] {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C}
    (hF : F ∈ logInt V σ) : subst a F ∈ logInt V τ :=
  ⟨by rw [cc_subst ha, hF.1], by rw [← subst_mvExp ha hF.1]; exact intS_subst ha hi hF.2⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def IntEnd (X : RawChart C d I κ) (V : VF C) (A : Matrix κ κ C) : Prop :=
  ∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)

def hEnd (X : RawChart C d I κ) (A B : Matrix κ κ C) : MvPowerSeries κ C :=
  hAt X (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C)) (endP X B (MvPowerSeries.X : κ → MvPowerSeries κ C))

end GlobalTheory.RowVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegralStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → IntGerm V t = ExpInt X V := by
  first | exact @GlobalTheory.RowLaw.intGerm_eq_expInt | exact GlobalTheory.RowLaw.intGerm_eq_expInt | (intros; apply GlobalTheory.RowLaw.intGerm_eq_expInt <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimits
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimits
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem coeff_alongCv_congr {C : Type} [Field C] {κ : Type} [Finite κ] {a b : κ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0)
    (f : MvPowerSeries κ C) (m : ℕ)
    (h : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (a i) = PowerSeries.coeff k (b i)) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hq : ∀ i, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (a i) =
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (b i) := by
    intro i
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, h i k (by omega), sub_self]
  have hp : ∀ e : κ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => b s ^ n) := by
    intro e
    have h1 : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => b s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow, hq]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 m (by omega)
    rwa [map_sub, sub_eq_zero] at h2
  show MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst b f)
  rw [MvPowerSeries.coeff_subst hsa, MvPowerSeries.coeff_subst hsb]
  refine finsum_congr fun e => ?_
  exact congrArg (fun z => MvPowerSeries.coeff e f • z) (hp e)

theorem exists_forall_le_of_eventually {P : ℕ → ℕ → Prop} (h : ∀ m, ∃ n0, ∀ n ≥ n0, P m n) (m : ℕ) :
    ∃ n, ∀ k ≤ m, P k n := by
  choose N hN using h
  refine ⟨(Finset.range (m + 1)).sup N, fun k hk => hN k _ ?_⟩
  exact Finset.le_sup (f := N) (Finset.mem_range.2 (by omega))

theorem cv_closed_under_limits : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hR g a b ha hlim
  choose γ lam hγ hlam hlg hsg using ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    have := hR.lin i 0 (by simp)
    simpa using this
  have hslg : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hsex : MvPowerSeries.HasSubst X.ex := MvPowerSeries.hasSubst_of_constantCoeff_zero hR.exc
  have hsγ : ∀ n, MvPowerSeries.HasSubst (γ n) := fun n =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ n i).1
  have ha0 : ∀ n i, PowerSeries.constantCoeff ((a n).1 i) = 0 := by
    intro n i
    rw [← hlg n i]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (hsγ n) (fun i => (hγ n i).1) (hlg0 i)
  have hb0 : ∀ i, PowerSeries.constantCoeff (b.1 i) = 0 := by
    intro i
    obtain ⟨n, hn⟩ := hlim 0
    have := (hn n le_rfl).1 i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [← this, ha0]
  have hsb : MvPowerSeries.HasSubst b.1 := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  have hγeq : ∀ n i, γ n i = alongCv (a n).1 (X.ex i) := by
    intro n i
    have h1 : (a n).1 = fun j => MvPowerSeries.subst (γ n) (X.lg j) := funext fun j => (hlg n j).symm
    rw [h1]
    show γ n i = MvPowerSeries.subst (fun j => MvPowerSeries.subst (γ n) (X.lg j)) (X.ex i)
    rw [← MvPowerSeries.subst_comp_subst_apply hslg (hsγ n), hR.exlg, MvPowerSeries.subst_X (hsγ n)]
  let Γ : κ → PowerSeries C := fun i => alongCv b.1 (X.ex i)
  have hΓ0 : ∀ i, PowerSeries.constantCoeff (Γ i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_subst_eq_zero hsb hb0 (hR.exc i)
  have key : ∀ m, ∃ n, (∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i)) ∧
      ∀ q, PowerSeries.coeff m (lam n q) = PowerSeries.coeff m (b.2 q + alongCv Γ (X.sg (X.u (1 - g) q))) := by
    intro m
    obtain ⟨n, hn⟩ := exists_forall_le_of_eventually hlim m
    have h1 : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i) := by
      intro i k hk
      rw [hγeq]
      exact coeff_alongCv_congr (ha0 n) hb0 _ k fun j k' hk' => (hn k' (hk'.trans hk)).1 j
    refine ⟨n, h1, fun q => ?_⟩
    rw [map_add (f := _), ← (hn m le_rfl).2 q, hsg n q, map_sub,
      coeff_alongCv_congr (fun i => (hγ n i).1) hΓ0 _ m h1, sub_add_cancel]
  refine ⟨Γ, fun q => b.2 q + alongCv Γ (X.sg (X.u (1 - g) q)), fun i => ⟨hΓ0 i, fun m => ?_⟩,
    fun q => ⟨?_, fun m => ?_⟩, fun i => ?_, fun q => by simp⟩
  · obtain ⟨n, hn, -⟩ := key m
    rw [← hn i m le_rfl]
    exact (hγ n i).2 m
  · obtain ⟨n, -, hn⟩ := key 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hn q, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hlam n q).1
  · obtain ⟨n, -, hn⟩ := key m
    rw [← hn q]
    exact (hlam n q).2 m
  · show MvPowerSeries.subst (fun j => MvPowerSeries.subst b.1 (X.ex j)) (X.lg i) = b.1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hsex hsb, hR.lgex, MvPowerSeries.subst_X hsb]

end GlobalTheory.RowLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.cv_closed_under_limits | exact GlobalTheory.RowLaw.cv_closed_under_limits | (intros; apply GlobalTheory.RowLaw.cv_closed_under_limits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphismsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphisms
noncomputable section

open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ActLimit

variable {C : Type} [Field C] {V : VF C}

def Tends (V : VF C) (s : ℕ → C) (x : C) : Prop := ∀ w : ℝ, ∀ᶠ n in atTop, V.Ge w (x - s n)

theorem exists_ge (x : C) : ∃ w : ℝ, w ≤ 0 ∧ V.Ge w x := by
  unfold VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_rfl, le_top⟩
  | coe t => exact ⟨min t 0, min_le_right _ _, by exact_mod_cast min_le_left _ _⟩

theorem eq_zero_of_ge {x : C} (h : ∀ w : ℝ, V.Ge w x) : x = 0 := by
  by_contra hx
  have hv : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hv
  have h1 := h (t + 1)
  unfold VF.Ge at h1
  rw [← ht] at h1
  have : t + 1 ≤ t := by exact_mod_cast h1
  linarith

theorem Tends.const (x : C) : Tends V (fun _ => x) x := fun w =>
  Eventually.of_forall fun _ => by simpa using VF.Ge.zero (V := V) w

theorem Tends.add {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n + t n) (x + y) := fun w => by
  filter_upwards [hs w, ht w] with n h1 h2
  have := h1.add h2
  rwa [show x - s n + (y - t n) = x + y - (s n + t n) by ring] at this

theorem Tends.neg {s : ℕ → C} {x : C} (hs : Tends V s x) : Tends V (fun n => -s n) (-x) := fun w => by
  filter_upwards [hs w] with n h1
  have := h1.neg
  rwa [show -(x - s n) = -x - -s n by ring] at this

theorem Tends.mul {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n * t n) (x * y) := fun w => by
  obtain ⟨a, -, ha⟩ := exists_ge (V := V) x
  obtain ⟨b, -, hb⟩ := exists_ge (V := V) y
  filter_upwards [hs (w - b), ht (w - a), ht b] with n h1 h2 h3
  have h4 : V.Ge b (t n) := by simpa using hb.sub h3
  have h5 : V.Ge w (x * (y - t n)) := by simpa using ha.mul h2
  have h6 : V.Ge w ((x - s n) * t n) := by simpa using h1.mul h4
  have := h5.add h6
  rwa [show x * (y - t n) + (x - s n) * t n = x * y - s n * t n by ring] at this

theorem Tends.unique {s : ℕ → C} {x y : C} (hx : Tends V s x) (hy : Tends V s y) : x = y := by
  apply sub_eq_zero.1
  refine eq_zero_of_ge (V := V) fun w => ?_
  obtain ⟨n, h1, h2⟩ := ((hx w).and (hy w)).exists
  simpa using h1.sub h2

theorem Tends.ge {s : ℕ → C} {x : C} {w : ℝ} (hx : Tends V s x) (hs : ∀ n, V.Ge w (s n)) : V.Ge w x := by
  obtain ⟨n, h1⟩ := (hx w).exists
  simpa using h1.add (hs n)

def convRing (V : VF C) : Subring ((ℕ → C) × C) where
  carrier := {p | Tends V p.1 p.2}
  mul_mem' := fun ha hb => Tends.mul ha hb
  one_mem' := Tends.const 1
  add_mem' := fun ha hb => Tends.add ha hb
  zero_mem' := Tends.const 0
  neg_mem' := fun ha => Tends.neg ha

def TendsS (V : VF C) {τ : Type} (f : ℕ → MvPowerSeries τ C) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ, Tends V (fun n => MvPowerSeries.coeff μ (f n)) (MvPowerSeries.coeff μ g)

theorem TendsS.const {τ : Type} (g : MvPowerSeries τ C) : TendsS V (fun _ => g) g := fun _ => Tends.const _

theorem TendsS.sub {τ : Type} {f f' : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f' g') : TendsS V (fun n => f n - f' n) (g - g') := fun μ => by
  simpa [sub_eq_add_neg] using (h μ).add (h' μ).neg

theorem TendsS.unique {τ : Type} {f : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f g') : g = g' := by
  ext μ; exact (h μ).unique (h' μ)

theorem TendsS.const_zero {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C}
    (h : TendsS V f g) (hf : ∀ n, MvPowerSeries.constantCoeff (f n) = 0) : MvPowerSeries.constantCoeff g = 0 := by
  have h0 := h 0
  simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf] at h0
  exact h0.unique (Tends.const 0)

def TendsS.lift {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C} (h : TendsS V f g) :
    MvPowerSeries τ (convRing V) :=
  fun μ => ⟨(fun n => MvPowerSeries.coeff μ (f n), MvPowerSeries.coeff μ g), h μ⟩

def term (V : VF C) (n : ℕ) : convRing V →+* C :=
  ((Pi.evalRingHom (fun _ : ℕ => C) n).comp (RingHom.fst _ _)).comp (convRing V).subtype

def lim (V : VF C) : convRing V →+* C := (RingHom.snd _ _).comp (convRing V).subtype

theorem TendsS.subst {σ τ : Type} [Finite σ] {a : ℕ → σ → MvPowerSeries τ C} {b : σ → MvPowerSeries τ C}
    (ha : ∀ n s, MvPowerSeries.constantCoeff (a n s) = 0) (hab : ∀ s, TendsS V (fun n => a n s) (b s))
    {f : ℕ → MvPowerSeries σ C} {g : MvPowerSeries σ C} (h : TendsS V f g) :
    TendsS V (fun n => MvPowerSeries.subst (a n) (f n)) (MvPowerSeries.subst b g) := by
  have hA : MvPowerSeries.HasSubst fun s => (hab s).lift := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    apply Subtype.ext
    refine Prod.ext (funext fun n => ha n s) ((hab s).const_zero fun n => ha n s)
  have h1 : ∀ n, MvPowerSeries.map (term V n) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst (a n) (f n) := fun n => MvPowerSeries.map_subst hA _
  have h2 : MvPowerSeries.map (lim V) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst b g := MvPowerSeries.map_subst hA _
  intro μ
  simp only [← h1, ← h2, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff μ (MvPowerSeries.subst (fun s => (hab s).lift) h.lift)).2

theorem exists_tends (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {s : ℕ → C} (hs : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (s (n + 1) - s n)) : ∃ x, Tends V s x := by
  choose k hk using hs
  have hd : ∀ N m n, k N ≤ m → m ≤ n → V.Ge N (s n - s m) := by
    intro N m n hm hn
    induction n, hn using Nat.le_induction with
    | base => simpa using VF.Ge.zero (V := V) N
    | succ n hn ih => simpa using (hk N n (hm.trans hn)).add ih
  let φ : ℕ → ℕ := fun N => (Finset.range (N + 1)).sup k
  have h1 : ∀ N, k N ≤ φ N := fun N => Finset.le_sup (f := k) (Finset.self_mem_range_succ N)
  have h2 : ∀ N, φ N ≤ φ (N + 1) := fun N => Finset.sup_mono (Finset.range_mono (by omega))
  obtain ⟨x, hx⟩ := cpl (fun N => s (φ N)) fun N => hd N _ _ (h1 N) (h2 N)
  refine ⟨x, fun w => ?_⟩
  filter_upwards [eventually_ge_atTop (φ ⌈w⌉₊)] with n hn
  have := (hx ⌈w⌉₊).sub (hd ⌈w⌉₊ _ _ (h1 _) hn)
  simpa using this.mono (Nat.le_ceil w)

variable {dd : ℕ}

theorem const_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem const_of_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : ev a f = 0) : MvPowerSeries.constantCoeff f = 0 := by
  have h := const_ev ha (f := f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) (by simp)
  unfold ev at h hf
  rw [MvPowerSeries.subst_sub (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2), hf,
    MvPowerSeries.subst_C] at h
  simpa using h

theorem const_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd j i) = 0 := by
  simp [pt]

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {a : Pt C n dd}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  const_ev (fun j i => by fin_cases j; exact ha i) (hφ i)

theorem tends_comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {e : Pt C 1 dd} (h : ∀ i, TendsS V (fun k => φ k i) (e i))
    {a : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) a i) (comp1 e a i) :=
  TendsS.subst (a := fun _ (p : Fin 1 × Fin dd) => ![a] p.1 p.2)
    (fun _ p => by obtain ⟨j, i⟩ := p; fin_cases j; exact ha i) (fun _ => TendsS.const _) (h i)

theorem constantCoeff_germEvalTwo_eq_zero {n : ℕ} {a b : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) {f : PS C 2 dd} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![a, b] f) = 0 :=
  const_ev (fun j i => by fin_cases j; exacts [ha i, hb i]) hf

theorem tendsToCoeffwise_germEvalTwo {n : ℕ} {a b : ℕ → Pt C n dd} {a' b' : Pt C n dd}
    (ha : ∀ k i, MvPowerSeries.constantCoeff (a k i) = 0) (hb : ∀ k i, MvPowerSeries.constantCoeff (b k i) = 0)
    (ha' : ∀ i, TendsS V (fun k => a k i) (a' i)) (hb' : ∀ i, TendsS V (fun k => b k i) (b' i)) (f : PS C 2 dd) :
    TendsS V (fun k => ev ![a k, b k] f) (ev ![a', b'] f) :=
  TendsS.subst (a := fun k (p : Fin 2 × Fin dd) => ![a k, b k] p.1 p.2)
    (fun k p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha k i, hb k i])
    (fun p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha' i, hb' i]) (TendsS.const f)

theorem exists_lim [CharZero C] {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {a : ℕ → O}
    (ha : ActCv Y a) : ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i) := by
  choose e he using fun i μ => exists_tends Y.cpl (s := fun n => MvPowerSeries.coeff μ (Y.B.A.act (a n) i))
    fun N => ha N i μ
  exact ⟨fun i μ => e i μ, he⟩

theorem limit_endomorphisms : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  intro C _ _ V O _ _ dd Y a ha hb
  obtain ⟨e, he⟩ := exists_lim Y ha
  obtain ⟨eb, heb⟩ := exists_lim Y hb
  have hc := Y.B.A.const
  refine ⟨e, eb, fun i μ => (he i μ).ge fun n => Y.intAct _ i μ, fun i μ => (heb i μ).ge fun n => Y.intAct _ i μ,
    fun N i μ => eventually_atTop.1 (he i μ N), fun N i μ => eventually_atTop.1 (heb i μ N), ?_, ?_⟩
  · funext i
    have h1 := tends_comp1 he (a := addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1))
      (fun i => constantCoeff_germEvalTwo_eq_zero (const_pt 0) (const_pt 1) (Y.B.G.const i)) i
    have h2 := tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun k => const_comp1 (hc (a k)) (const_pt 1)) (tends_comp1 he (const_pt 0))
      (tends_comp1 he (const_pt 1)) (Y.B.G.F i)
    refine h1.unique ?_
    simp only [Y.B.A.hom]
    exact h2
  · have hh : MvPowerSeries.constantCoeff Y.h = 0 :=
      const_of_ev (fun j i => by fin_cases j; exacts [map_zero _, const_pt 0 i]) Y.gauge.ax0
    have hid : ∀ {τ : Type} (f : MvPowerSeries τ C), MvPowerSeries.map (algebraMap C C) f = f := fun f => by
      ext μ; simp
    have hK : ∀ x, Y.B.actK C x = Y.B.A.act x := fun x => funext fun i => hid _
    have h1 := (tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun _ => const_pt 1) (tends_comp1 he (const_pt 0)) (fun i => TendsS.const _) Y.h).sub
      (tendsToCoeffwise_germEvalTwo (V := V) (fun _ => const_pt (n := 2) 0) (fun k => const_comp1 (hc (star (a k))) (const_pt 1))
        (fun i => TendsS.const _) (tends_comp1 heb (const_pt 1)) Y.h)
    have h2 := TendsS.subst (σ := Unit) (fun k _ => by
      rw [map_sub, constantCoeff_germEvalTwo_eq_zero (const_comp1 (hc (a k)) (const_pt (n := 2) 0)) (const_pt 1) hh,
        constantCoeff_germEvalTwo_eq_zero (const_pt (n := 2) 0) (const_comp1 (hc (star (a k))) (const_pt 1)) hh, sub_zero])
      (fun _ => h1) (TendsS.const (PowerSeries.exp C))
    intro μ
    refine (h2 μ).ge fun n => ?_
    have h3 := Y.gauge.ad (a n)
    rw [hK, hK] at h3
    have h4 := Y.intAd (a n) μ
    rw [(hid (Y.B.ad (a n))).symm.trans h3] at h4
    exact h4

end GlobalTheory.ActLimit
end
end

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  first | exact @GlobalTheory.ActLimit.limit_endomorphisms | exact GlobalTheory.ActLimit.limit_endomorphisms | (intros; apply GlobalTheory.ActLimit.limit_endomorphisms <;> assumption)
end

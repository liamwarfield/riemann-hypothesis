module

public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieLab
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ge_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  obtain ⟨p, hpm, hp⟩ := hx
  have hZ : ∀ z : ℤ, V.Ge 0 (algebraMap ℤ C z) := by
    intro z
    rw [eq_intCast]
    refine Int.induction_on z ?_ ?_ ?_
    · rw [Int.cast_zero]; exact VF.Ge.zero 0
    · intro i ih
      rw [Int.cast_add, Int.cast_one]
      exact VF.Ge.add ih VF.Ge.one
    · intro i ih
      rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]
      exact VF.Ge.add ih (VF.Ge.neg VF.Ge.one)
  by_contra hneg
  have hlt : V.v x < ((0 : ℝ) : WithTop ℝ) := not_le.mp hneg
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hr0 : r < 0 := by
    rw [← hr] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr
    exact WithTop.coe_ne_top hr
  set yv := x⁻¹ with hyv
  have hy0 : yv ≠ 0 := inv_ne_zero hx0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (fun h => hy0 ((AddValuation.top_iff V.v).mp h))
  have hrs : r + s = 0 := by
    have h1 : V.v (x * yv) = 0 := by rw [hyv, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [AddValuation.map_mul, ← hr, ← hs] at h1
    exact_mod_cast h1
  have hy : V.Ge (-r) yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hy0' : V.Ge 0 yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hpow : ∀ k : ℕ, V.Ge 0 (yv ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact VF.Ge.one
    | succ k ih => rw [pow_succ]; exact VF.Ge.mul_int ih hy0'
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hp
  set n := p.natDegree
  have hsum : 1 + ∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) = 0 := by
    have h2 := congrArg (· * yv ^ n) hp
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [← h2]
    congr 1
    · rw [← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := le_of_lt (Finset.mem_range.mp hi)
      conv_rhs => rw [show n = (n - i) + i from (Nat.sub_add_cancel hi').symm]
      rw [pow_add, mul_assoc, mul_left_comm (x ^ i), ← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow, mul_one]
  have hS : V.Ge (-r) (∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i)) := by
    refine Finset.sum_induction _ (fun z => V.Ge (-r) z) (fun _ _ ha hb => VF.Ge.add ha hb) (VF.Ge.zero _) ?_
    intro i hi
    have hi' : n - i = (n - i - 1) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [hi', pow_succ, ← mul_assoc]
    exact VF.Ge.mul_int (VF.Ge.mul_int (hZ _) (hpow _)) hy
  have h1 : (1 : C) = -∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) :=
    eq_neg_of_add_eq_zero_left hsum
  have hS' := VF.Ge.neg hS
  rw [← h1] at hS'
  unfold VF.Ge at hS'
  rw [AddValuation.map_one] at hS'
  have : (-r : ℝ) ≤ 0 := by exact_mod_cast hS'
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem embedding_integral (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) : V.Ge 0 (emA3 io ι τ x) := by
  exact ge_of_isIntegral V ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map (emA3 io ι τ).toIntAlgHom)

theorem embK_conj (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by
  unfold embK
  apply Subtype.ext
  simp [embF]
  rw [hstar]
  rw [show (algebraMap (𝓞 E) E) (H.bar x) = ((H.bar x : 𝓞 E) : E) from rfl, H.bar_eq x,
    IsCMField.complexEmbedding_complexConj]

theorem embedding_conjugate (hstar : ∀ a : 𝓞 E, star a = H.bar a) (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) :
    emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (star x) := by
  simp only [emA3, RingHom.coe_comp, Function.comp_apply, embK_conj hstar]

theorem a3uvec_int (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by
  rw [show chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) from C3.gen.1.2.2.2.2.2.2 ℓ i]
  exact embIntSt_holds T C V ι hι _

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

end Core

variable (Xo c)

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
noncomputable section
open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def RowData.rk (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card

structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rk g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a

def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rk g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)

def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)

namespace GlobalTheory

def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N

variable (X : RowData C V d I J) (F : Flag X)

def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rk (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rk g a) (e a))

def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none

def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rk g a') then e a' k else 0

def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)

end GlobalTheory

def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}

def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))

def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rk g a) (e a)

def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rk g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)

def ValBlocks {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o))
    (Z : Finset Orb) (nW : ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∑ o ∈ Z, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun p => p.1.wt (X o) g a k).sum = ga o g a k) →
    ν ≤ ∑ o ∈ Z, ((L o).map Prod.snd).sum

def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k

structure WtHyp (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (bgr : ZMod (N.ordP l) → Fin 2)
    (rk : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ)
    (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (N.R.k - 1) = alongOrb N l z W a + alongOrb N l z exc a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (N.R.k - 1) (ga z) N.R.r : ℝ) +
    ∑ a, ((N.R.k : ℝ) - 1) * ((alongOrb N l z exc a : ℕ) : ℝ))

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

theorem coeff_rename_zero {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ) (s : τ)
    (hs : e s ≠ 0) (hsr : ∀ a, φ a ≠ s) :
    coeff e (subst (fun a => (X (φ a) : MvPowerSeries τ C)) F) = 0 := by
  have hA : MvPowerSeries.HasSubst (fun a => (MvPowerSeries.X (φ a) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
  intro h
  apply hs
  rw [h, Finsupp.mapDomain_notin_range]
  rintro ⟨a, ha⟩
  exact hsr a ha

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

def FBChart.rawCol : RawChart C 1 (fun _ => Empty) (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := Y.k
  u := fun _ c => c.elim
  ty := fun _ c => c.elim
  n := 0
  j := 0
  j' := 0
  big := fun _ _ => False

theorem FBChart.rawCol_sg (v : Fin dd → C) : Y.rawCol.sg v = un1 (Y.sgP v) := by
  ext μ
  show -∑ i, v i * MvPowerSeries.coeff (μ.mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), i) 1) Y.h =
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.sgP v)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [FBChart.sgP, map_neg, map_sum, MvPowerSeries.coeff_C_mul, coeff_eval_second_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [MvPowerSeries.coeff_pderiv, Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨x, hx⟩
    simp at hx

theorem FBChart.addCvCol (hG : GermISt Y) : Y.rawCol.AddCvSt V := by
  intro γ γ' hγ hγ'
  set ρ : Fin 2 × Fin dd → PowerSeries C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact intS_ps.2 (hγ j).2
    · exact intS_ps.2 (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → PowerSeries C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hγ''I : IsCv V γ'' := fun j => ⟨hγ''0 j, intS_ps.1 (IntS.subst hρ0 hρI (Y.intF j))⟩
  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = alongCv (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    unfold alongCv
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', hγ''I, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add (f := _), MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have hsg0 : MvPowerSeries.constantCoeff (Y.rawCol.sg v) = 0 := Y.rawCol.constantCoeff_sg (gauge_axes Y 0) v
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_sub]
      have e1 : PowerSeries.constantCoeff (alongCv γ'' (Y.rawCol.sg v)) = 0 := constantCoeff_subst_zero hγ''0 hsg0
      have e2 : PowerSeries.constantCoeff (alongCv γ (Y.rawCol.sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ i).1) hsg0
      have e3 : PowerSeries.constantCoeff (alongCv γ' (Y.rawCol.sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ' i).1) hsg0
      rw [e1, e2, e3]
      simp
    · have h := IntS.subst hρ0 hρI (hG v hv)
      rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
        hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← Y.rawCol_sg v] at h
      exact intS_ps.1 h

variable {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem hCol_inj (c : Fin 2) : Function.Injective (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.2

theorem coeff_inCol_sg (c : Fin 2) (v : Fin 2 × Fin dd → C) (μ : Fin 2 × Fin dd →₀ ℕ) :
    coeff μ (inCol c (Y.rawCol.sg fun i => v (c, i))) =
      -∑ x, v x * coeff (μ.mapDomain (fun x => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), x) 1) (hCol c Y.h) := by
  unfold inCol hCol
  by_cases hr : ∀ x, μ x ≠ 0 → x.1 = c
  · have hμ : (μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => (c, x)) = μ := by
      rw [← Finsupp.mapDomain_comp]
      conv_rhs => rw [← Finsupp.mapDomain_id (v := μ)]
      apply Finsupp.mapDomain_congr
      intro x hx
      exact Prod.ext (hr x (Finsupp.mem_support_iff.1 hx)).symm rfl
    rw [← hμ, coeff_subst_rename_inj _ (col_inj c)]
    show -∑ i, v (c, i) * MvPowerSeries.coeff
      ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) Y.h = _
    rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hE : ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => (c, x))).mapDomain (fun x => ((0 : Fin 2), x)) +
          Finsupp.single ((1 : Fin 2), (c, i)) 1 =
          ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
            Finsupp.single ((1 : Fin 2), i) 1).mapDomain (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) := by
        rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
        simp only [← Finsupp.mapDomain_comp]
        rfl
      rw [hE, coeff_subst_rename_inj _ (hCol_inj c)]
    · intro c' _ hc'
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_rename_zero (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) _ _ ((1 : Fin 2), (c', i)) (by simp), mul_zero]
      intro q hq
      simp only [Prod.mk.injEq] at hq
      exact hc' hq.2.1.symm
    · intro h
      exact absurd (Finset.mem_univ c) h
  · push_neg at hr
    obtain ⟨x0, hx0, hx0c⟩ := hr
    rw [coeff_rename_zero (fun x : Fin dd => (c, x)) _ μ x0 hx0 (fun a ha => hx0c (by rw [← ha]))]
    symm
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro x _
    have hne : (μ.mapDomain (fun x => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), x) 1 : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ)
        ((0 : Fin 2), x0) ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.ext_iff.1 h).2), Finsupp.single_apply,
        if_neg (by simp)]
      simpa using hx0
    rw [coeff_rename_zero (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) _ _ ((0 : Fin 2), x0) hne, mul_zero]
    intro q hq
    simp only [Prod.mk.injEq] at hq
    exact hx0c (by rw [← hq.2])

theorem FBChart.rawSelf_sg (v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg v = ∑ c, inCol c (Y.rawCol.sg fun i => v (c, i)) := by
  ext μ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_inCol_sg, Finset.sum_neg_distrib]
  show -∑ x, v x * MvPowerSeries.coeff (μ.mapDomain (fun x : Fin 2 × Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), x) 1) (∑ col, hCol col Y.h) = _
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem addCvSelf_of (hG : GermIAllSt) : AddCvSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p γ γ' hγ hγ'
  have hA := Y.addCvCol (hG C V O dd Y)
  choose G hGcv hGlg hGsg using fun c : Fin 2 =>
    hA (fun i => γ (c, i)) (fun i => γ' (c, i)) (fun i => hγ (c, i)) (fun i => hγ' (c, i))
  have hcv : IsCv V (fun x : Fin 2 × Fin dd => G x.1 x.2) := fun x => hGcv x.1 x.2
  have along : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ c (f : MvPowerSeries (Fin dd) C),
      alongCv δ (inCol c f) = alongCv (fun i => δ (c, i)) f :=
    fun δ hδ c f => subst_inCol (fun x => (hδ x).1) c f
  have hsum : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ f : Fin 2 → MvPowerSeries (Fin dd) C,
      alongCv δ (∑ c, inCol c (f c)) = ∑ c, alongCv (fun i => δ (c, i)) (f c) := by
    intro δ hδ f
    have hS := hasSubst_of_constantCoeff_zero fun x => (hδ x).1
    unfold alongCv
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hS, map_sum, MvPowerSeries.coe_substAlgHom hS]
    exact Finset.sum_congr rfl fun c _ => along δ hδ c (f c)
  refine ⟨fun x => G x.1 x.2, hcv, ?_, ?_⟩
  · rintro ⟨c, i⟩
    show alongCv _ (inCol c (un1 (Y.lg i))) = alongCv γ (inCol c (un1 (Y.lg i))) + alongCv γ' (inCol c (un1 (Y.lg i)))
    rw [along _ hcv c, along γ hγ c, along γ' hγ' c]
    exact hGlg c i
  · intro v hv
    rw [Y.rawSelf_sg p v, hsum _ hcv, hsum γ hγ, hsum γ' hγ', ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine ⟨?_, fun n => ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun c _ => (hGsg c _ (fun i => hv (c, i))).1
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact VF.Ge.sum fun c _ => (hGsg c _ (fun i => hv (c, i))).2 n

theorem cartesian_self_conj_of_germs (hPT : PTSelfSt) (hG : GermIAllSt) (hStab : HStabSelfSt) : CartSelfSt := cartSelf_of hPT (addCvSelf_of hG) hStab

theorem addCvSelf_holds : AddCvSelfSt := addCvSelf_of germIAll_holds

theorem cartesian_self_conj_of_stability (hPT : PTSelfSt) (hStab : HStabSelfSt) : CartSelfSt := cartesian_self_conj_of_germs hPT germIAll_holds hStab

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace AllStart

variable {C : Type} [Field C]

theorem linAct_sum {dd : ℕ} (φ : Pt C 1 dd) {ι : Type} (S : Finset ι) (w : ι → C) (u : ι → Fin dd → C) :
    linAct φ (∑ c ∈ S, w c • u c) = ∑ c ∈ S, w c • linAct φ (u c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem coeff_one_subst {dd : ℕ} (f : PS C 1 dd)
    (hf : ∀ (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ f = 0)
    (P : Fin 1 × Fin dd → PowerSeries C) (hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0) :
    MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P f) = 0 := by
  have hA : MvPowerSeries.HasSubst P := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
  by_cases hμ : μ.degree ≤ 1
  · rw [hf μ hμ, zero_smul]
  · push_neg at hμ
    have hX : ∀ q, (PowerSeries.X : PowerSeries C) ∣ P q := fun q => PowerSeries.X_dvd_iff.2 (hP0 q)
    have hdeg : μ.degree = ∑ s ∈ μ.support, μ s := rfl
    have h1 : (PowerSeries.X : PowerSeries C) ^ μ.degree ∣ μ.prod fun s e => P s ^ e := by
      rw [hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun s _ => pow_dvd_pow_of_dvd (hX s) _
    have hdvd : (PowerSeries.X : PowerSeries C) ^ 2 ∣ μ.prod fun s e => P s ^ e := (pow_dvd_pow _ hμ).trans h1
    have h2 := (PowerSeries.X_pow_dvd_iff.1 hdvd) 1 (by norm_num)
    rw [show MvPowerSeries.coeff (Finsupp.single () 1) (μ.prod fun s e => P s ^ e) = 0 from h2, smul_zero]

end AllStart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePGmExLem
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.GmExArith

open Formalism.L2.FormalSeriesBounds NumberField

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact add_pos_of_pos_of_nonneg ha hb'

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem ge_intCast' (m : ℤ) : V.Ge 0 (m : C) := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact ge_natCast' n
  | negSucc n => rw [Int.cast_negSucc]; exact (ge_natCast' (n + 1)).neg

theorem geom_int {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (n : ℕ) :
    V.Ge 0 (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) :=
  VF.Ge.sum fun i _ => (hA.pow i).mul_int (hB.pow _)

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) (n : ℕ) :
    V.MM (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact mm_int_mul (geom_int hA hB n) h

end Formalism.L2.FormalSeriesBounds.GmExArith
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieValL
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

def RawChart.TCoordSt {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
    {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∀ (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ (g : Fin 2) (c : I g), ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t g c)

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]

theorem cc_toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    MvPowerSeries.constantCoeff (toAllS o F) = MvPowerSeries.constantCoeff F := by
  unfold toAllS
  exact VP.cc_subst_eq (fun _ => MvPowerSeries.constantCoeff_X _) F

theorem toAllS_subst {κ : Type} [Finite κ] (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    (hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0) (T : MvPowerSeries κ C) :
    toAllS o (MvPowerSeries.subst E T) = MvPowerSeries.subst (fun x => toAllS o (E x)) T := by
  unfold toAllS
  exact VP.subst_subst hE (fun _ => MvPowerSeries.constantCoeff_X _) T

theorem germLift_gen {σ : Type} [Finite σ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) (t : ∀ g, I o g → MvPowerSeries (I o g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (hT : ∀ w : WV (I o), ∃ T : MvPowerSeries σ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst A T = toAllS o (upG w.1 (t w.1 w.2))) :
    ∀ F ∈ IntGerm V t, ∃ G : MvPowerSeries σ C, IntS V G ∧ MvPowerSeries.subst A G = toAllS o F := by
  intro F hF
  obtain ⟨γ, hγ, rfl⟩ := hF
  choose T hTi hT0 hTA using hT
  have hE : ∀ w : WV (I o), MvPowerSeries.constantCoeff (upG w.1 (t w.1 w.2)) = 0 := fun w => by
    unfold upG
    exact VP.cc_subst (fun _ => MvPowerSeries.constantCoeff_X _) (ht0 _ _)
  refine ⟨MvPowerSeries.subst T γ, IntS.subst hT0 hTi hγ, ?_⟩
  rw [VP.subst_subst hT0 hA, toAllS_subst o hE]
  congr 1
  funext w
  exact hTA w

theorem tLift_gen {σ κ : Type} [Finite σ] [Finite κ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    {π : κ → MvPowerSeries σ C} (hπi : ∀ x, IntS V (π x)) (hπ0 : ∀ x, MvPowerSeries.constantCoeff (π x) = 0)
    (hπ : ∀ x, MvPowerSeries.subst A (π x) = toAllS o (E x))
    {T : MvPowerSeries κ C} (hTi : IntS V T) (hT0 : MvPowerSeries.constantCoeff T = 0) :
    ∃ T' : MvPowerSeries σ C, IntS V T' ∧ MvPowerSeries.constantCoeff T' = 0 ∧
      MvPowerSeries.subst A T' = toAllS o (MvPowerSeries.subst E T) := by
  have hπA : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.subst A (π x)) = 0 := fun x => VP.cc_subst hA (hπ0 x)
  have hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0 := fun x => by
    rw [← cc_toAllS o (E x), ← hπ x]
    exact hπA x
  refine ⟨MvPowerSeries.subst π T, IntS.subst hπ0 hπi hTi, VP.cc_subst hπ0 hT0, ?_⟩
  rw [VP.subst_subst hπ0 hA, toAllS_subst o hE]
  congr 1
  funext x
  exact hπ x

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb]

section Pairs

variable {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Pairs

section Self

variable {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

def ProjSelfSt (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin 2 × Fin dd → PS C 2 dd, (∀ x, IntS V (π x)) ∧
    (∀ x, MvPowerSeries.constantCoeff (π x) = 0) ∧
    ∀ x, pull2 Y p (π x) = toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g x)

theorem germLiftSelf_of (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (hP : ProjSelfSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSelfSt Y p H := by
  intro hsep o S t hS F hF
  unfold pull2
  have hA : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 := VP.cc_linPt Y (uS Y p)
  refine VP.germLift_gen (I := IS I0) hA o t (fun g c => (hS g).1 c) (fun w => ?_) F hF
  obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
  obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
  obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen (I := IS I0) hA o hπi hπ0 hπ hTi hT0
  exact ⟨T', h1, h2, by rw [h3, hTe]⟩

end Self

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Rename₂

theorem coeff_rename_outside {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (ν : τ →₀ ℕ) {s : τ}
    (hs : ν s ≠ 0) (hr : ∀ x, φ x ≠ s) :
    coeff ν (MvPowerSeries.subst (fun x => (X (φ x) : MvPowerSeries τ C)) F) = 0 := by
  refine coeff_subst_rename_out φ F ν fun e' he => hs ?_
  rw [← he]
  exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; exact hr x hx)

variable {dd : ℕ}

theorem coeff_hCol (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  unfold hCol
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    have hφ : Function.Injective (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2
    have he : E2 ((0 : Fin 2), (col, i)) ((1 : Fin 2), (col, j)) =
        (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)).mapDomain (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      simp [E2, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [he, coeff_subst_rename_inj _ hφ]
  · by_cases h1 : c1 = col
    · have h2 : c2 ≠ col := fun h2 => hc ⟨h1, h2⟩
      refine coeff_rename_outside _ h (E2 _ _) (s := ((1 : Fin 2), (c2, j))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h2 hx.2.1.symm
    · refine coeff_rename_outside _ h (E2 _ _) (s := ((0 : Fin 2), (c1, i))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h1 hx.2.1.symm

end Rename₂

section Self

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]

theorem coeff_E2_sum_hCol_eq_ite (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_hCol]
  rw [Fin.sum_univ_two]
  by_cases h12 : c1 = c2
  · subst h12
    fin_cases c1 <;> simp
  · fin_cases c1 <;> fin_cases c2 <;> simp_all

theorem FBChart.self_raw_first_pairing_eq (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by
  have hsg : ∀ x : Fin 2 × Fin dd, MvPowerSeries.coeff (Finsupp.single x 1) ((Y.rawSelf p).sg v) =
      -∑ i : Fin 2 × Fin dd, v i *
        (if x.1 = i.1 then MvPowerSeries.coeff (E2 ((0 : Fin 2), x.2) ((1 : Fin 2), i.2)) Y.h else 0) := by
    intro x
    show (-∑ i, v i * MvPowerSeries.coeff ((Finsupp.single x 1).mapDomain (fun y => ((0 : Fin 2), y)) +
      Finsupp.single ((1 : Fin 2), i) 1) (∑ col, hCol col Y.h)) = _
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_single]
    rw [show Finsupp.single ((0 : Fin 2), x) 1 + Finsupp.single ((1 : Fin 2), i) 1 =
      E2 ((0 : Fin 2), (x.1, x.2)) ((1 : Fin 2), (i.1, i.2)) from rfl, coeff_E2_sum_hCol_eq_ite]
  simp only [RawChart.sg1, hsg, bil, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_add]
  congr 1 <;> (congr 1; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

end Self

theorem hStabSelf_holds : HStabSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g c q hty
  have hne : p.ty0 c ≠ p.ty0 q + p.hd := by
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact hty
    · intro e
      apply hty
      show p.ty0 c + p.hd = p.ty0 q
      rw [e, add_assoc, p.hd_two, add_zero]
  obtain ⟨a, ha⟩ := p.em_sep _ _ hne
  have hb := Y.bil_ad a (p.e c) (p.e q)
  rw [p.e_eig c a, p.e_eig q (star a), p.em_conj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.e c) (p.e q)) := bil_int (Y.intAd a) (p.e_int c) (p.e_int q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.e c) (p.e q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha, zero_add] at hint
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    obtain ⟨M, hM⟩ := p.gm_lim 0
    intro a r s
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := h1.add (p.em_int a (M r s))
    simpa using h2
  show V.Ge 0 ((Y.rawSelf p).sg1 (fun x => p.gm (p.ty0 c) x.1 g * p.e c x.2)
    (fun x => p.gm (p.ty0 q) x.1 (1 - g) * p.e q x.2))
  rw [Y.self_raw_first_pairing_eq]
  apply VF.Ge.neg
  apply VF.Ge.sum
  intro col _
  show V.Ge 0 (bil Y.h (p.gm (p.ty0 c) col g • p.e c) (p.gm (p.ty0 q) col (1 - g) • p.e q))
  rw [bil_smul_left, bil_smul_right]
  exact (hgm _ _ _).mul_int ((hgm _ _ _).mul_int hβ)

end Formalism.L2.FormalSeriesBounds
end
end

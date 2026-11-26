module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIof {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o : Orb) (g : Fin 2) : Type :=
  Σ t : ZMod d, Fin (r (tau o g t))

section Defs

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
  {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]

def blkProd (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin n) : MvPolynomial (Fin n × WVO I) C :=
  ∏ o, toAll o (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o))

end Defs

section Mem

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (O : Subring C) (n : ℕ)

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

end Mem

end Formalism.L2.FormalSeriesBounds.RF
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieCuts
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def EmbIntSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ t : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr t))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AllSet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {L | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • PowerSeries.mk (fun n => L n (Sum.inl c))) ∧
    ∀ q : JJ I g, PowerSeries.mk (fun n => L n (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun n => L n (Sum.inl c)) else 0}

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace IndependenceBoundPlain

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
  [Fintype κ] (X : RawChart C d I κ)

def PlainCoefficientIdentity (H : ∀ g, X.CartHyp V g) : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)

theorem independence_bound_raw [IsAlgClosed C] [NeZero d] (hrk : X.RankHyp) (H : ∀ g, X.CartHyp V g) (hR2 : RawChart.RankMaximalCondition H)
    (hcoef : PlainCoefficientIdentity X H) : RawChart.IndependenceBoundCondition H := by
  intro hAlt g a hbig N w x hg hV hind
  have key : ∀ g' : Fin 2, X.big g' a → X.big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ X.big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // X.ty (1 - g) q = a + 2} = X.j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := hcoef hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  have hspan : ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * M (σ r).1 q) := by
    intro w x hg hV
    obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
    refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
    have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
      rw [← Finset.sum_filter_of_ne (p := fun q' => X.ty (1 - g) q' = a + 2)
        (fun q' _ hne => by
          by_contra hq
          exact hne (by rw [hsupp q' hq, zero_mul]))]
      rw [Finset.sum_subtype (Finset.univ.filter fun q' => X.ty (1 - g) q' = a + 2)
        (p := fun q' => X.ty (1 - g) q' = a + 2) (fun q' => by simp)]
      exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
    rw [← hsum]
    exact hc1 q
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) (fun r => M (σ r).1) hspan
    N w x hg hV hind

end IndependenceBoundPlain

section Closed

def CoefficientIdentitySelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, IndependenceBoundPlain.PlainCoefficientIdentity X H

theorem independence_bound_self_conj (h : CoefficientIdentitySelfConjugate) : IndependenceBoundSelfConjugate := by
  unfold IndependenceBoundSelfConjugate AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.rawSelf p) hrk H hR2 (h C V O dd Y d I0 p hrk H)

end Closed

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartDerivativeCoefficient (C3 : IntChart T io y) (k n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  nabValN (a3B C3) T.Fr (a3h C3) H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) P

theorem nuLocC_le_nval (C3 : IntChart T io y) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN Dw n) T.Fr) (hP : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n (chD C3.ch)) (hf : IsIntPS T f) :
    nuLocC C3 e k a n ≤ nval T.V e (chartDerivativeCoefficient C3 k n f P) := by
  unfold nuLocC chartDerivativeCoefficient
  exact le_trans (iInf₂_le P hP) (iInf₂_le f hf)

end Chart

section Val

variable {C : Type} [Field C] {V : VF C}

theorem le_v_sum (x : WithTop ℝ) {m : ℕ} (z : Fin m → C) (h : ∀ i, x ≤ V.v (z i)) : x ≤ V.v (∑ i, z i) := by
  refine Finset.sum_induction z (fun w => x ≤ V.v w)
    (fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)) ?_ (fun i _ => h i)
  rw [AddValuation.map_zero]
  exact le_top

end Val

variable (Xo c)

def NabMapSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C)
    (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr),
      Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι f) (MvPolynomial.map ι P) = ι (chartDerivativeCoefficient C3 k n f P)

def DescSpanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P ∈ (chartLetterSystem C3 V ι a).FF n, ∀ f : PS C n (chD C3.ch), IntS V f →
      ∃ (m : ℕ) (r : Fin m → C) (Pi : Fin m → MvPolynomial (LtN Dw n) T.Fr) (fi : Fin m → PS T.Fr n (chD C3.ch)),
        (∀ i, V.Ge 0 (r i)) ∧ (∀ i, Pi i ∈ FFV (Dw := Dw) T a n) ∧ (∀ i, IsIntPS T (fi i)) ∧
        Y.nab (chartLetterSystem C3 V ι a) n f P =
          ∑ i, r i * Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i))

def NvalEqSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ x : T.Fr, (WithBot.some (V.v (ι x)) : WithBot (WithTop ℝ)) = nval T.V (eOf T V) x

variable {Xo c}

theorem descent_of (h1 : NabMapSt Xo c) (h2 : DescSpanSt Xo c) (h3 : NvalEqSt) : DescentSt Xo c := by
  intro T io y C3 C _ _ V ι hι k Y hY a n
  unfold FBChart.nuPlE
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨P, hP, f, hf, rfl⟩ := hx
  obtain ⟨m, r, Pi, fi, hr, hPi, hfi, heq⟩ := h2 T io y C3 C V ι hι k Y hY a n P hP f hf
  have hz : ∀ i, nuLocC C3 (eOf T V) k a n ≤ (WithBot.some (V.v (Y.nab (chartLetterSystem C3 V ι a) n
      (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i)))) : WithBot (WithTop ℝ)) := by
    intro i
    rw [h1 T io y C3 C V ι k Y hY a n (fi i) (Pi i), h3 T C V ι hι]
    exact nuLocC_le_nval C3 (eOf T V) k a n (Pi i) (hPi i) (fi i) (hfi i)
  rw [heq]
  generalize nuLocC C3 (eOf T V) k a n = ν at hz ⊢
  rcases ν with _ | w
  · exact bot_le
  · refine WithBot.coe_le_coe.mpr (le_v_sum w _ fun i => ?_)
    have hzi := WithBot.coe_le_coe.mp (hz i)
    rw [AddValuation.map_mul]
    calc w = 0 + w := (zero_add w).symm
      _ ≤ V.v (r i) + _ := add_le_add (hr i) hzi

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePAxesSelfSt
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

theorem van_sum {τ ι : Type} {T : Set τ} (s : Finset ι) (f : ι → MvPowerSeries τ C) (hf : ∀ i ∈ s, Van T (f i)) :
    Van T (∑ i ∈ s, f i) := by
  intro ν hν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi ν hν)

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_inCol (col : Fin 2) (f : MvPowerSeries (Fin dd) C) (hf : constantCoeff f = 0) :
    constantCoeff (inCol col f) = 0 := by
  have hb : MvPowerSeries.HasSubst
      (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  unfold inCol
  rw [MvPowerSeries.constantCoeff_subst hb, finsum_eq_single _ 0]
  · simp [hf]
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => (MvPowerSeries.X (col, s) : MvPowerSeries (Fin 2 × Fin dd) C) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hi]
    rw [h0, smul_zero]

theorem van_hCol (col g : Fin 2) (h : PS C 2 dd)
    (hh : ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    Van {w : Fin 2 × (Fin 2 × Fin dd) | w.1 = g} (hCol col h) := by
  unfold hCol
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = g} (fun _ => constantCoeff_X _) ?_ ?_
  · intro s hs
    exact van_X hs
  · intro e he
    exact hh e he

theorem gauge_axes (Y : FBChart C V O dd) (g : Fin 2) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0 := by
  fin_cases g
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl

theorem axesSelf_holds : AxesSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
    apply constantCoeff_inCol
    rw [constantCoeff_uncurry]
    exact Y.ex_const x.2
  · intro g e he
    show coeff e (∑ col, hCol col Y.h) = 0
    exact van_sum Finset.univ _ (fun col _ => van_hCol col g Y.h (gauge_axes Y g)) e he

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyGlue
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

section Glue

variable {C : Type} [Field C] {V : VF C}

theorem tends_pow_zero {a : C} (ha : V.MM a) : Tends V (fun n => a ^ V.l ^ n) 0 := by
  unfold Tends VF.MM at *
  intro w
  by_cases ha0 : a = 0
  · refine ⟨0, fun n _ => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [ha0, zero_pow (pow_pos V.l_prime.pos n).ne', sub_zero, AddValuation.map_zero]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff V.v).mpr ha0)
    have hr0 : 0 < r := by
      rw [← hr] at ha
      exact WithTop.coe_pos.mp ha
    refine ⟨⌈w / r⌉₊, fun n hn => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [zero_sub, AddValuation.map_neg, AddValuation.map_pow, ← hr, ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul]
    have h1 : (n : ℝ) ≤ ((V.l ^ n : ℕ) : ℝ) := by
      first
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt n).le
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt).le
    have h2 : w / r ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (div_mul_cancel₀ w hr0.ne').ge.trans (mul_le_mul_of_nonneg_right (h2.trans h1) hr0.le)

variable [CharZero C] {O : Type} [CommRing O] {n d : ℕ}

theorem chi_kill (K : KeyData C V O n d) (w : Fin n → C) (hw : w ≠ 0) (hP : Matrix.mulVec K.P w = w)
    (χ : O →+* C) (hχ : ∀ x, Matrix.mulVec (K.ρ x) w = χ x • w) :
    (∀ y, V.Ge 0 (χ y)) ∧ ∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z) := by
  have hint : ∀ y, V.Ge 0 (χ y) := fun y => eig_int (K.ρ y) (K.ρ_int y) w hw (χ y) (hχ y)
  refine ⟨hint, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  have hT : Tends V (fun m => χ K.ε ^ V.l ^ m * w i) (w i) := by
    have h1 : Tends V (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) (Matrix.mulVec K.P w i) := by
      simp only [Matrix.mulVec, dotProduct]
      refine Tends.sum _ fun j _ => Tends.mul ?_ (tends_const _)
      exact RowTiePProj.tends_of_nat fun N => K.P_lim N i j
    have e : (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) = fun m => χ K.ε ^ V.l ^ m * w i := by
      funext m
      rw [hχ, map_pow]; rfl
    rw [e, hP] at h1
    exact h1
  have hunit : ¬ V.MM (χ K.ε) := by
    intro hm
    have h0 := (tends_pow_zero hm).mul (tends_const (V := V) (w i))
    rw [zero_mul] at h0
    exact hi (hT.unique h0)
  intro z hz
  obtain ⟨y, hy⟩ := K.ε_ann z hz
  have h1 := congrArg (fun t => V.v (χ t)) hy
  simp only [map_mul, map_natCast, AddValuation.map_mul, V.v_l] at h1
  unfold VF.MM at hunit ⊢
  push_neg at hunit
  have he0 : V.v (χ K.ε) = 0 := le_antisymm hunit (hint K.ε)
  rw [he0, zero_add] at h1
  rw [h1]
  have := hint y
  unfold VF.Ge at this
  calc (0 : WithTop ℝ) < 1 := by exact_mod_cast one_pos
    _ = 1 + 0 := (add_zero _).symm
    _ ≤ 1 + V.v (χ y) := add_le_add le_rfl (by exact_mod_cast this)

end Glue

section Top

theorem keyLA_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) (C : Type) [Field C] [CharZero C] (V : VF C)
    (hac : IsAlgClosed C)
    (hcpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (x : O) :
    Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P = 0 := by
  have hv : ∀ v : Fin n → C,
      Matrix.mulVec (Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P) v = 0 := by
    intro v
    obtain ⟨m, w, χ, hPv, hw⟩ := hE C V hac hcpl O n d K v
    rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h0 : w j = 0
    · rw [h0, Matrix.mulVec_zero]
    obtain ⟨hPw, hχ⟩ := hw j
    obtain ⟨hint, hkill⟩ := chi_kill K (w j) h0 hPw (χ j) hχ
    obtain ⟨c, hc⟩ := hR C V O n d K (χ j) hint hkill
    have heq := hD C V O n d K (χ j) c hint hc
    rw [aeval_mulVec _ _ _ (hχ x), Polynomial.eval_prod]
    have : ∏ c' : ZMod d, Polynomial.eval (χ j x) (Polynomial.X - Polynomial.C (K.em c' x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        heq, sub_self])
    rw [this, zero_smul]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Top

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePLimTy
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace LimTy

variable {C : Type} [Field C] {V : VF C}

theorem tendsS_sum {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} {F : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ S, TendsS V (f i) (F i)) : TendsS V (fun k => ∑ i ∈ S, f i k) (∑ i ∈ S, F i) := by
  intro μ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  exact Tends.sum S (fun i hi => h i hi μ)

theorem tendsS_smul {σ : Type} (c : C) {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => c • f k) (c • F) := by
  intro μ
  first
    | simp only [map_smul, smul_eq_mul]
    | simp only [MvPowerSeries.coeff_smul]
  exact (tends_const c).mul (h μ)

theorem tendsS_ite {σ : Type} (P : Prop) [Decidable P] {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => if P then f k else 0) (if P then F else 0) := by
  split_ifs
  · exact h
  · exact TendsS.const 0

theorem coeff_tyS_mv (l : ℕ) (b : ℕ → C) (μ : Unit →₀ ℕ) :
    MvPowerSeries.coeff μ (tyS l b) = ∑ s ∈ Finset.range (μ () + 1), if l ^ s = μ () then b s else 0 := rfl

theorem tendsS_tyS (l : ℕ) {a : ℕ → ℕ → C} {a' : ℕ → C} (h : ∀ s, Tends V (fun k => a k s) (a' s)) :
    TendsS V (fun k => tyS l (a k)) (tyS l a') := by
  intro μ
  simp only [coeff_tyS_mv]
  refine Tends.sum _ (fun s _ => ?_)
  split_ifs
  · exact h s
  · exact tends_const 0

theorem tendsP {f : ℕ → PowerSeries C} {F : PowerSeries C} (h : TendsS V f F) (n : ℕ) :
    Tends V (fun k => PowerSeries.coeff n (f k)) (PowerSeries.coeff n F) :=
  h (Finsupp.single () n)

private theorem eq_zero_of_tends_const_zero {y : C} (h : Tends V (fun _ => (0 : C)) y) : y = 0 := by
  by_contra hy
  have hne : V.v y ≠ ⊤ := fun ht => hy ((AddValuation.top_iff V.v).mp ht)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨n0, hn0⟩ := h (r + 1)
  have h1 : ((r + 1 : ℝ) : WithTop ℝ) ≤ V.v (y - 0) := hn0 n0 le_rfl
  rw [sub_zero, ← hr] at h1
  have h2 := WithTop.coe_le_coe.mp h1
  linarith

private theorem ge_zero_of_tends_of_forall_ge_zero {s : ℕ → C} {y : C} (h : Tends V s y) (hs : ∀ k, V.Ge 0 (s k)) :
    V.Ge 0 y := by
  obtain ⟨n0, hn0⟩ := h 0
  have h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (y - s n0) := hn0 n0 le_rfl
  have h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (s n0) := hs n0
  have e : y = (y - s n0) + s n0 := by ring
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v y
  rw [e]
  exact le_trans (le_min h1 h2) (V.v.map_add _ _)

theorem isCv_lim {σ : Type} {γ : ℕ → σ → PowerSeries C} {Γ : σ → PowerSeries C}
    (h : ∀ i, TendsS V (fun k => γ k i) (Γ i)) (hc : ∀ k, IsCv V (γ k)) : IsCv V Γ := by
  intro i
  have hcoef : ∀ n, Tends V (fun k => PowerSeries.coeff n (γ k i)) (PowerSeries.coeff n (Γ i)) :=
    fun n => tendsP (h i) n
  refine ⟨?_, fun n => ge_zero_of_tends_of_forall_ge_zero (hcoef n) (fun k => (hc k i).2 n)⟩
  have e : ∀ k, PowerSeries.coeff 0 (γ k i) = 0 := fun k => by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hc k i).1
  have h0 := hcoef 0
  simp only [e] at h0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact eq_zero_of_tends_const_zero h0

theorem constantCoeff_lin {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    (X : RawChart C d I κ) (l : ℕ) (hl : 2 ≤ l) (g : Fin 2) (b : I g → ℕ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS l (b c)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  first
    | rw [map_smul, coeff_tyS_mv]
    | rw [MvPowerSeries.coeff_smul, coeff_tyS_mv]
  simp

private theorem hasSubst_of_constantCoeff_eq_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)

theorem lim_mem {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
    (hl : 2 ≤ V.l)
    (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0) (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C)
    (hx : ∀ k, x k ∈ X.TySet V g) (hlim : VLim V x x') : x' ∈ X.TySet V g := by
  classical
  unfold RawChart.TySet at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  choose γk lamk hγk hlamk hA hB using hx
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → κ → PowerSeries C,
      T = fun k i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x k s (Sum.inl c)) := ⟨_, rfl⟩
  obtain ⟨T', hT'def⟩ : ∃ T' : κ → PowerSeries C,
      T' = fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x' s (Sum.inl c)) := ⟨_, rfl⟩
  have hT0 : ∀ k i, MvPowerSeries.constantCoeff (T k i) = 0 := by
    intro k i
    rw [hTdef]
    exact constantCoeff_lin X V.l hl g (fun c s => x k s (Sum.inl c)) i
  have hT'0 : ∀ i, MvPowerSeries.constantCoeff (T' i) = 0 := by
    intro i
    rw [hT'def]
    exact constantCoeff_lin X V.l hl g (fun c s => x' s (Sum.inl c)) i
  have hTlim : ∀ i, TendsS V (fun k => T k i) (T' i) := by
    intro i
    simp only [hTdef, hT'def]
    exact tendsS_sum Finset.univ (fun c _ => tendsS_smul (X.u g c i)
      (tendsS_tyS (a := fun k s => x k s (Sum.inl c)) (a' := fun s => x' s (Sum.inl c)) V.l
        (fun s w => hlim w s (Sum.inl c))))
  have hHSlg : MvPowerSeries.HasSubst X.lg := hasSubst_of_constantCoeff_eq_zero' hlg0
  have hHSex : MvPowerSeries.HasSubst X.ex := hasSubst_of_constantCoeff_eq_zero' hex0
  have hHS : ∀ k, MvPowerSeries.HasSubst (γk k) := fun k =>
    hasSubst_of_constantCoeff_eq_zero' (fun i => (hγk k i).1)
  have hHST' : MvPowerSeries.HasSubst T' := hasSubst_of_constantCoeff_eq_zero' hT'0
  have hγeq : ∀ k i, γk k i = MvPowerSeries.subst (T k) (X.ex i) := by
    intro k i
    have e1 : T k = fun j => MvPowerSeries.subst (γk k) (X.lg j) := by
      funext j
      rw [hTdef]
      exact (hA k j).symm
    rw [e1, ← MvPowerSeries.subst_comp_subst_apply hHSlg (hHS k), hexlg, MvPowerSeries.subst_X (hHS k)]
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : κ → PowerSeries C, γ' = fun i => MvPowerSeries.subst T' (X.ex i) :=
    ⟨_, rfl⟩
  have hγlim : ∀ i, TendsS V (fun k => γk k i) (γ' i) := by
    intro i
    simp only [hγeq, hγ'def]
    exact TendsS.subst (fun k j => hT0 k j) hT'0 hTlim (TendsS.const _)
  have hγ' : IsCv V γ' := isCv_lim hγlim hγk
  have hγ'0 : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hrel : ∀ i, alongCv γ' (X.lg i) = T' i := by
    intro i
    unfold alongCv
    rw [hγ'def, ← MvPowerSeries.subst_comp_subst_apply hHSex hHST', hlgex, MvPowerSeries.subst_X hHST']
  obtain ⟨lam', hlam'def⟩ : ∃ lam' : JJ I g → PowerSeries C, lam' = fun q =>
      tyS V.l (fun s => x' s (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x' s (Sum.inl c)) else 0) := ⟨_, rfl⟩
  have hlamlim : ∀ q, TendsS V (fun k => lamk k q) (lam' q) := by
    intro q
    have e : ∀ k, lamk k q = tyS V.l (fun s => x k s (Sum.inr q)) + alongCv (γk k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x k s (Sum.inl c)) else 0) := by
      intro k
      rw [hB k q]
      ring
    simp only [e, hlam'def]
    refine TendsS.sub (TendsS.add ?_ ?_) ?_
    · exact tendsS_tyS (a := fun k s => x k s (Sum.inr q)) (a' := fun s => x' s (Sum.inr q)) V.l
        (fun s w => hlim w s (Sum.inr q))
    · unfold alongCv
      exact TendsS.subst (fun k j => (hγk k j).1) hγ'0 hγlim (TendsS.const _)
    · refine tendsS_sum _ (fun c _ => ?_)
      split_ifs
      · exact tendsS_smul _ (tendsS_tyS (a := fun k s => x k s (Sum.inl c))
          (a' := fun s => x' s (Sum.inl c)) V.l (fun s w => hlim w s (Sum.inl c)))
      · exact TendsS.const 0
  refine ⟨γ', lam', hγ', isCv_lim hlamlim hlamk, fun i => ?_, fun q => ?_⟩
  · rw [hrel i, hT'def]
  · simp only [hlam'def]
    ring

end LimTy

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeichDef
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def TeichSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (n d : ℕ), d ≠ 0 → ∀ (A : Set (Matrix (Fin n) (Fin n) C)),
      (∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) → (∀ a ∈ A, -a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, ∀ i j, V.Ge 0 (a i j)) →
      (∀ (s : ℕ → Matrix (Fin n) (Fin n) C) (b : Matrix (Fin n) (Fin n) C), (∀ k, s k ∈ A) →
        (∀ i j, RowTiePE0.Tends V (fun k => s k i j) (b i j)) → b ∈ A) →
      (∀ a ∈ A, ((V.l : C)⁻¹) • (a ^ V.l ^ d - a) ∈ A) →
      ∀ b ∈ A, ∃ τ ∈ A, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b - τ) ∈ A

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

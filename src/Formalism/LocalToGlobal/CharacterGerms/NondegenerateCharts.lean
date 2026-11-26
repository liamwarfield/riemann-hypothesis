module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
public import Formalism.DropLevelBounds.ThBounds
public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Formal

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.chartLinearTerm (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 2 dd :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2

def cvAt (s : MvPowerSeries (Fin 2) C) (γ : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  MvPowerSeries.subst (fun _ : Unit => s) γ

def NDG (Y : FBChart C V O dd) : Prop :=
  ∀ γ : Fin dd → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => cvAt (MvPowerSeries.X p.1) (γ p.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
      (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
        (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
          ev (n := 2) ![pt C dd 1] b)))

end Formal

def RankMaximalOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    NDG Y → (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def NondegenerateCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → NDG Y

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

structure LabS (E : Type) [Field E] (C : Type) (Orb : Type) (d : ℕ) where
  tau : Orb → ZMod d → (E →+* ℂ)
  hd : ZMod d
  gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop

abbrev LabS.II {Orb : Type} {d : ℕ} (lab : LabS E C Orb d) (Dw : Datum H) (o : Orb) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o a))

section Pairs

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

def selfLieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : LabS E C Orb d) (o : Orb) (x : lab.II Dw o) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)

structure LabSArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : LabS E C Orb d) : Prop where
  inj : Function.Injective fun x : Orb × ZMod d => lab.tau x.1 x.2
  hd_ne : lab.hd ≠ 0
  hd_two : lab.hd + lab.hd = 0
  conj : ∀ o a, ComplexEmbedding.conjugate (lab.tau o a) = lab.tau o (a + lab.hd)
  frob : ∀ o a x, V.MM (emA3 io ι (lab.tau o (a + 1)) x - emA3 io ι (lab.tau o a) x ^ V.l)
  sep : ∀ x x' : Orb × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0
  unr : ∀ o, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y
  gm_lim : ∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s,
    V.Ge N (lab.gm o a r s - emA3 io ι (lab.tau o a) (M r s))
  gm_hyp : ∀ o a (s s' : Fin 2), ∑ r, lab.gm o (a + lab.hd) r s * lab.gm o a r s' = if s = s' then 0 else 1

structure LabSGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : LabS E C Orb d) :
    Prop where
  em_int : ∀ o a x, V.Ge 0 (emA3 io ι (lab.tau o a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + lab.hd)) x
  e_int : ∀ o x i, V.Ge 0 (selfLieBasisVector C3 ι lab o x i)
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

def selfOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) : SelfData Y d (lab.II Dw o) where
  em := fun a => emA3 io ι (lab.tau o a)
  em_int := hg.em_int o
  em_frob := ha.frob o
  em_sep := fun a a' h => ha.sep (o, a) (o, a') (fun e => h (Prod.mk.inj e).2)
  em_unr := ha.unr o
  hd := lab.hd
  hd_ne := ha.hd_ne
  hd_two := ha.hd_two
  em_conj := hg.em_conj o
  e := selfLieBasisVector C3 ι lab o
  ty0 := fun x => x.1
  e_int := hg.e_int o
  e_eig := hg.e_eig o
  e_sat := by
    obtain ⟨w, h1, h2⟩ := hg.e_sat o
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  e_full := hg.e_full o
  gm := lab.gm o
  gm_lim := ha.gm_lim o
  gm_hyp := ha.gm_hyp o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o

theorem selfSep_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) : SelfSep Y (selfOfLab ha hg) := by
  intro x x' hne
  exact ha.sep x x' hne

def LabS.RankOK (lab : LabS E C Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ a, lab.big o 0 a → Dw.mult (lab.tau o a) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 0 a → Dw.mult (lab.tau o a) = lab.j') ∧
    (∀ a, lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.j')

theorem card_sigma_shift (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  have e1 : (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a) =
      (Finset.univ.filter fun b : ZMod d => b + h = a).sigma fun b => Finset.univ := by
    ext ⟨b, i⟩
    simp
  have e2 : (Finset.univ.filter fun b : ZMod d => b + h = a) = {a - h} := by
    ext b
    simp [eq_sub_iff_add_eq]
  rw [e1, Finset.card_sigma, e2, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]

theorem rankHyp_ofLabS {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
  refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab]
      convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
      exact Finset.filter_congr (fun _ _ => Iff.rfl)
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab]
      convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
      exact Finset.filter_congr (fun _ _ => Iff.rfl)
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)

end Pairs

section Named

variable (Xo c)

def GmExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (tau : Orb → ZMod d → (E →+* ℂ)) (hd : ZMod d), hd ≠ 0 → hd + hd = 0 →
    (∀ o a, ComplexEmbedding.conjugate (tau o a) = tau o (a + hd)) →
    (∀ o a x, V.MM (emA3 io ι (tau o (a + 1)) x - emA3 io ι (tau o a) x ^ V.l)) →
    (∀ x x' : Orb × ZMod d, x ≠ x' → ∃ a : 𝓞 E, V.v (emA3 io ι (tau x.1 x.2) a - emA3 io ι (tau x'.1 x'.2) a) = 0) →
    ∃ gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C,
      (∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s, V.Ge N (gm o a r s - emA3 io ι (tau o a) (M r s))) ∧
      ∀ o a (s s' : Fin 2), ∑ r, gm o (a + hd) r s * gm o a r s' = if s = s' then 0 else 1

def AllSelfConjugateCharts (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin 2 × Fin dd) → Prop) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, Φ C V d (fun _ => lab.II Dw o) (chD C3.ch) (Y.rawSelf (selfOfLab ha hg o))

def RankMaximalSelfCharts : Prop := AllSelfConjugateCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition Hc

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

end Top

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
noncomputable section
open scoped BigOperators

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

def i0 (k l : ℕ) : ℕ := sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}

def ThlEq : Prop := ∀ k l : ℕ, 1 ≤ k → 2 ≤ l →
  Odd (i0 k l) ∧ 3 ≤ i0 k l ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i0 k l ∧
    thl k l = ((l : ℝ) ^ i0 k l)⁻¹

def LevelBound : Prop := ∀ k l : ℕ, 1 ≤ k → 5 ≤ l → ((i0 k l : ℝ) - 1) ≤ 2 + 2 * Real.log k

structure Plan (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) where
  y : ZMod d → ℕ → ℕ
  u : ZMod d → ℕ
  supp : ∀ a i, i ∉ oddLevels d → y a i = 0
  bal : ∀ a, W a = (∑ i ∈ oddLevels d, l ^ i * y a i) +
    (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a

def Plan.triv (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) : Plan l d W where
  y := fun _ _ => 0
  u := W
  supp := fun _ _ _ => rfl
  bal := fun a => by simp

def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)

def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))

def Plan.bound {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Plan l d W) (n m : ℕ) : ℝ :=
  (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (p.y a i)) + ∑ a, chBd l n m (p.u a)

def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S

def IsReps (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) : Prop :=
  ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z'

def alongOrb {X : Type} (N : NumDatum) (l : ℕ) (z : RPl N.R) (W : RPl N.R → X) : ZMod (N.ordP l) → X :=
  fun s => W (N.pos l z s.val)

def FInertReps : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    N.FInert j l = ∑ z ∈ Z, Fnum l (N.ordP l)
        (fun s => ((N.R.k : ℝ) - 1) * alongOrb N l z (N.w j) s) ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → N.FjP j l = N.FInert j l)

def LemmaFe : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, (∀ a, 0 ≤ D a) →
    (∀ a a', D a' ≤ l * D a) → Fnum l d D = rho l * ∑ a, D a

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Col

variable {dd : ℕ}

theorem hasSubst_col (col : Fin 2) :
    HasSubst (fun x : Fin dd => (X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem col_inj (col : Fin 2) : Function.Injective (fun x : Fin dd => (col, x)) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by
  have hS := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_col col) hS]
  congr 1
  funext i
  rw [subst_X hS]

theorem inCol_X (col : Fin 2) (i : Fin dd) : inCol col (X i : MvPowerSeries (Fin dd) C) = X (col, i) := by
  unfold inCol
  rw [subst_X (hasSubst_col col)]

theorem coeff_subst_rename_out {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ)
    (he : ∀ e' : σ →₀ ℕ, e'.mapDomain φ ≠ e) :
    coeff e (subst (fun s => (X (φ s) : MvPowerSeries τ C)) F) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e'
  rw [prod_X_rename, coeff_monomial, if_neg (fun h => he e' h.symm), smul_zero]

theorem coeff_inCol_lin (col : Fin 2) (f f' : MvPowerSeries (Fin dd) C)
    (h : ∀ μ : Fin dd →₀ ℕ, μ.degree ≤ 1 → coeff μ f = coeff μ f') (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ (inCol col f) = coeff μ (inCol col f') := by
  unfold inCol
  by_cases hr : ∃ μ' : Fin dd →₀ ℕ, μ'.mapDomain (fun x => (col, x)) = μ
  · obtain ⟨μ', rfl⟩ := hr
    rw [coeff_subst_rename_inj _ (col_inj col), coeff_subst_rename_inj _ (col_inj col)]
    exact h μ' (by rw [Finsupp.degree_mapDomain] at hμ; exact hμ)
  · push_neg at hr
    rw [coeff_subst_rename_out _ _ _ hr, coeff_subst_rename_out _ _ _ hr]

end Col

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem FBChart.self_chart_log_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).lg x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.lg x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.lg_const x.2

theorem FBChart.self_chart_exp_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).ex x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.ex_const x.2

theorem FBChart.rawSelf_axis0 (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    coeff e (Y.rawSelf p).h = 0 := by
  show coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 0 Y.h (gauge_axes Y 0)) e he

theorem FBChart.rawSelf_exlg (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).lg (inCol col (un1 (Y.ex i))) = _
  rw [subst_inCol (Y.self_chart_log_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.lg j))) (un1 (Y.ex i)) = _
  have hL : HasSubst (fun j => un1 (Y.lg j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.lg_const]
  have hx : un1 (comp1 Y.ex Y.lg i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.ex_lg]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.lg_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lgex (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).ex (inCol col (un1 (Y.lg i))) = _
  rw [subst_inCol (Y.self_chart_exp_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.ex j))) (un1 (Y.lg i)) = _
  have hL : HasSubst (fun j => un1 (Y.ex j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.ex_const]
  have hx : un1 (comp1 Y.lg Y.ex i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.lg_ex]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.ex_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lin (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ ((Y.rawSelf p).lg x) = coeff μ (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show coeff μ (inCol col (un1 (Y.lg i))) = _
  rw [← inCol_X col i]
  refine coeff_inCol_lin col _ _ (fun ν hν => ?_) μ hμ
  show coeff (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hν), ← uncurry_X i]
  rfl

theorem SelfData.gm_int (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h := hM a r s
  rw [Nat.cast_zero] at h
  have e : p.gm a r s = (p.gm a r s - p.em a (M r s)) + p.em a (M r s) := by ring
  rw [e]
  exact h.add (p.em_int a _)

theorem FBChart.rawSelf_u_integral (g : Fin 2) (c : I0) (x : Fin 2 × Fin dd) : V.Ge 0 ((Y.rawSelf p).u g c x) :=
  VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (p.e_int c x.2)

theorem SelfData.gm_pair (a : ZMod d) (g : Fin 2) :
    ∑ col, p.gm a col g * p.gm (a + p.hd) col (1 - g) = 1 := by
  have h := p.gm_hyp (a + p.hd) g (1 - g)
  rw [add_assoc, p.hd_two, add_zero, if_neg (by fin_cases g <;> decide)] at h
  exact h

theorem FBChart.exists_integral_right_inverse (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, huw⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c',
    fun x c' => VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (hw0 _ _), fun c c' => ?_⟩
  show ∑ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') = _
  have e1 : ∀ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') =
      (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (1 - g)) * (p.e c x.2 * w0 x.2 c') := fun x => by ring
  simp_rw [e1]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, huw c c']
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl]
    simp only [mul_one]
    exact SelfData.gm_pair Y p _ g
  · simp [hc]

def PTSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabSelfSt : Prop :=
  AllSelf fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

theorem cartSelf_of (hPT : PTSelfSt) (hAdd : AddCvSelfSt) (hStab : HStabSelfSt) : CartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  have := Y.algClosed
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have h0 := (Y.rawSelf p).zero_mem (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
  have hadd := (Y.rawSelf p).add_mem V g (hAdd C V O dd Y d I0 p) (fun g c x => Y.rawSelf_u_integral p g c x)
  exact
    { zero := h0
      add := hadd
      neg := (Y.rawSelf p).neg_mem V g Y.l_odd
      teich := (Y.rawSelf p).teich_mem V g
      Vm := (Y.rawSelf p).V_mem V g
      Fm := (Y.rawSelf p).F_mem V g (Y.self_chart_log_constantCoeff p) (Y.rawSelf_exlg p) hζ h0 hadd
      sumV := (Y.rawSelf p).sumV_mem V g (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_exlg p) (Y.rawSelf_lgex p) h0 hadd
      t2 := (Y.rawSelf p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.rawSelf_lin p) (Y.rawSelf_axis0 p) (Y.exists_integral_right_inverse p g) (hStab C V O dd Y d I0 p g)
      t3 := (Y.rawSelf p).const_mem_type_set_of_nonneg (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
      t4 := hPT C V O dd Y d I0 p g }

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem vV_algebraMap_nonneg (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by
  have hle := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t
  unfold vV valV
  generalize (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
    (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    have ha : a ≤ 1 := WithZero.coe_le_one.1 hle
    have hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a := rfl
    rw [hlog, neg_nonneg]
    exact ha

theorem embIntSt_holds : EmbIntSt := by
  unfold EmbIntSt
  intro T C _ V ι h t
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, map_zero]
    exact VF.Ge.zero 0
  · have hx : algebraMap T.V T.Fr t ≠ 0 :=
      fun h0 => ht ((IsFractionRing.injective T.V T.Fr) (by rw [h0, map_zero]))
    have hl : ((V.l : ℕ) : T.Fr) = algebraMap T.V T.Fr ((V.l : ℕ) : T.V) := (map_natCast _ _).symm
    have h1 := vV_algebraMap_nonneg T t
    have h2 := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rw [← hl] at h2
    unfold VF.Ge
    rw [h (algebraMap T.V T.Fr t) hx]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2))

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieChar
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ

def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

def keyL (ℓ : Letter T r n) : T × ℕ × Fin n := (ℓ.1, ℓ.2.1.val, ℓ.2.2)

theorem keyL_inj : Function.Injective (keyL (T := T) (r := r) (n := n)) := by
  rintro ⟨σ, i, c⟩ ⟨σ', i', c'⟩ h
  simp only [keyL, Prod.mk.injEq] at h
  obtain ⟨rfl, hi, rfl⟩ := h
  obtain rfl : i = i' := Fin.ext hi
  rfl

theorem rowShift_X (σ : T) (i i' : Fin (r σ)) (t : C) (ℓ : Letter T r n) :
    rowShift r n C σ i i' t (X ℓ) =
      if keyL ℓ = (σ, i.val, ℓ.2.2) then X ℓ + MvPolynomial.C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ := by
  unfold rowShift
  simp only [MvPolynomial.aeval_X]
  have key : (∃ b, ℓ = ⟨σ, (i, b)⟩) ↔ keyL ℓ = (σ, ↑i, ℓ.snd.2) := by
    constructor
    · rintro ⟨b, rfl⟩
      rfl
    · intro h
      exact ⟨ℓ.snd.2, keyL_inj (show keyL ℓ = keyL ⟨σ, (i, ℓ.snd.2)⟩ from h)⟩
  by_cases h : keyL ℓ = (σ, ↑i, ℓ.snd.2)
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (mt key.mp h), if_neg h]

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin n}

end Fam

end Formalism.L2.FormalSeriesBounds.RF
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.NormOneIntegral
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C]

def ZP (C : Type) [Field C] (σ : Type) : Subring (MvPolynomial σ C) := (MvPolynomial.map (Int.castRingHom C)).range

theorem X_mem_ZP {σ : Type} (x : σ) : (MvPolynomial.X x : MvPolynomial σ C) ∈ ZP C σ :=
  RingHom.mem_range.2 ⟨MvPolynomial.X x, MvPolynomial.map_X _ _⟩

theorem rename_mem_ZP {σ τ : Type} (k : σ → τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) :
    MvPolynomial.rename k P ∈ ZP C τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  exact RingHom.mem_range.2 ⟨MvPolynomial.rename k Q, MvPolynomial.map_rename _ _ _⟩

theorem det_mem {R : Type} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (h : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun s _ => ?_
  rw [Units.smul_def]
  exact S.zsmul_mem (S.prod_mem fun i _ => h _ _) _

theorem minorK_mem_ZP (N N' k : ℕ) : minorK C N N' k ∈ ZP C (Fin N × Fin N') := by
  unfold minorK
  split_ifs with h
  · exact det_mem _ _ fun i j => X_mem_ZP _
  · exact one_mem _

theorem minorMonomial_mem_ZP (N N' : ℕ) (e : ℕ → ℕ) : monP C N N' e ∈ ZP C (Fin N × Fin N') := by
  unfold monP
  exact prod_mem fun k _ => pow_mem (minorK_mem_ZP N N' k) _

end Gen

theorem poly_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (b : GlobalTheory d) : b.poly X F ∈ ZP C _ := by
  unfold GlobalTheory.poly
  cases b with
  | bi g a i y =>
    exact mul_mem (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
      (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
  | ch g a u => exact pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _
  | mon g e N => exact prod_mem fun a _ => rename_mem_ZP _ (minorMonomial_mem_ZP _ _ _)

theorem blkProd_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : blkProd X F n L pl ∈ ZP C _ := by
  unfold blkProd toAll prodAll
  exact prod_mem fun o _ => rename_mem_ZP _ (prod_mem fun i _ => rename_mem_ZP _ (poly_mem_ZP _ _ _))

end Formalism.L2.FormalSeriesBounds.RF
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}

def mpt {n : ℕ} (a : Pt R n d) : Pt S n d := fun i => MvPowerSeries.map φ (a i)

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j => mpt φ (a j)) (MvPowerSeries.map φ f) := by
  unfold ev
  exact MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS R 1 d) :
    MvPowerSeries.map φ (ev ![a] f) = ev ![mpt φ a] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a] (by intro j i; fin_cases j; simp [ha]) f]
  congr 1
  funext j
  fin_cases j
  rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mpt φ a, mpt φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f]
  congr 1
  funext j
  fin_cases j <;> rfl

omit [CommRing S] in
theorem cc_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact (cc_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf

omit [CommRing S] in
@[simp] theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]


omit [CommRing S] in
@[simp] theorem cc_comp1 {n : ℕ} (ψ : Pt R 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    constantCoeff (comp1 ψ a i) = 0 := cc_ev ![a] (by intro j i; fin_cases j; simp [ha]) (ψ i) (hψ i)

omit [CommRing S] in
theorem zc_zero {n : ℕ} : ∀ i : Fin d, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp

@[simp] theorem mpt_pt {n : ℕ} (j : Fin n) : mpt φ (pt R d j) = pt S d j := by
  funext i
  simp [mpt, pt]

@[simp] theorem mpt_zero {n : ℕ} : mpt φ (0 : Pt R n d) = 0 := by
  funext i
  simp [mpt]

theorem mpt_comp1 {n : ℕ} (ψ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mpt φ (comp1 ψ a) = comp1 (mpt φ ψ) (mpt φ a) := by
  funext i
  exact map_ev1 φ a ha (ψ i)

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

end Formalism.L2.FormalSeriesBounds
end
end

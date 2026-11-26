module

public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Agr

variable {C : Type} [Field C]

def Agr {τ : Type} (k : ℕ) (f g : MvPowerSeries τ C) : Prop :=
  ∀ e : τ →₀ ℕ, e.degree < k → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g

theorem Agr.symm {τ : Type} {k : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) : Agr k g f :=
  fun e he => (h e he).symm

theorem Agr.trans {τ : Type} {k : ℕ} {f g g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k g g') : Agr k f g' :=
  fun e he => (h e he).trans (h' e he)

theorem Agr.add {τ : Type} {k : ℕ} {f g f' g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k f' g') :
    Agr k (f + f') (g + g') := fun e he => by rw [map_add (f := _), map_add (f := _), h e he, h' e he]

theorem agr_iff_trunc {τ : Type} [Finite τ] (k : ℕ) (f g : MvPowerSeries τ C) :
    Agr k f g ↔ MvPowerSeries.truncTotal k f = MvPowerSeries.truncTotal k g := by
  constructor
  · intro h
    ext e
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with he
    · exact h e he
    · rfl
  · intro h e he
    have h2 := congrArg (AddMonoidAlgebra.coeff · e) h
    rwa [MvPowerSeries.coeff_truncTotal _ he, MvPowerSeries.coeff_truncTotal _ he] at h2

theorem agr_subst_left {σ τ : Type} [Finite σ] [Finite τ] {a b : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    {k : ℕ} (h : ∀ s, Agr k (a s) (b s)) (f : MvPowerSeries σ C) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst b f) := by
  have h' : ∀ s, MvPowerSeries.truncTotal k (a s) = MvPowerSeries.truncTotal k (b s) :=
    fun s => (agr_iff_trunc k _ _).1 (h s)
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst hb]
  simp only [h']

theorem agr_subst_right {σ τ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {k : ℕ} {f g : MvPowerSeries σ C} (h : Agr k f g) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha,
    (agr_iff_trunc k f g).1 h]

end Agr

section Wit

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def RawChart.TyWit (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C)
    (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C) : Prop :=
  IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0

theorem RawChart.mem_tySet_iff (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ ∃ γ lam, X.TyWit V g x γ lam := Iff.rfl

end Wit

section MM

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero]
  exact WithTop.coe_lt_top 0

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_mul_ge {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem mm_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact mm_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end MM

section Step2

variable {C : Type} [Field C]

theorem Agr.mono {τ : Type} {k k' : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) (hk : k' ≤ k) : Agr k' f g :=
  fun e he => h e (lt_of_lt_of_le he hk)

theorem const_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {γ : PowerSeries C}
    (hγ : PowerSeries.constantCoeff γ = 0) : MvPowerSeries.constantCoeff (cvAt s γ) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs) (fun _ => hs) hγ

theorem subst_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {σ : Type} [Finite σ]
    {γ : σ → PowerSeries C} (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (F : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) F = cvAt s (MvPowerSeries.subst γ F) := by
  unfold cvAt
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs)]

theorem cvAt_smul_X {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) (c : C) :
    cvAt s (c • (MvPowerSeries.X () : PowerSeries C)) = c • s := by
  unfold cvAt
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs
  rw [MvPowerSeries.subst_smul hS, MvPowerSeries.subst_X hS]

theorem eval_points_two {dd : ℕ} (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  unfold ev
  have e : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      fun q => (MvPowerSeries.X q : PS C 2 dd) := by
    funext ⟨k, j⟩
    fin_cases k <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem tyS_good_coeff {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (hl : 2 ≤ V.l) (c : I g) (n : ℕ)
    (hn : n < V.l ^ 2) :
    PowerSeries.coeff n (tyS V.l (fun s => x s (Sum.inl c))) = if n = 1 then w c else 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · rw [pow_zero]
    by_cases hn1 : n = 1
    · subst hn1
      rw [if_pos rfl, if_pos rfl]
      simp [h0]
    · have hn1' : ¬ (1 = n) := fun h => hn1 h.symm
      rw [if_neg hn1', if_neg hn1]
  · intro s _ hs0
    by_cases hs1 : s = 1
    · subst hs1
      simp [h1 c]
    · rw [if_neg]
      intro hsn
      have h2 : 2 ≤ s := by omega
      have h3 : V.l ^ 2 ≤ V.l ^ s := Nat.pow_le_pow_right (by omega) h2
      rw [hsn] at h3
      exact absurd hn (not_lt.mpr h3)
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

theorem coeffX' (n : ℕ) : PowerSeries.coeff n (MvPowerSeries.X () : PowerSeries C) = if n = 1 then 1 else 0 :=
  PowerSeries.coeff_X n

theorem lg_addOf (Y : FBChart C V O dd) {τ : Type} (P : Fin 2 → Fin dd → MvPowerSeries τ C)
    (hP : ∀ k j, MvPowerSeries.constantCoeff (P k j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j))
        (un1 (Y.lg i)) =
      MvPowerSeries.subst (P 0) (un1 (Y.lg i)) + MvPowerSeries.subst (P 1) (un1 (Y.lg i)) := by
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => P q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP q.1 q.2
  have hF0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP q.1 q.2) (Y.B.G.const j)
  rw [subst_singlePointUncurry hF0, subst_singlePointUncurry (hP 0), subst_singlePointUncurry (hP 1)]
  have key := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2)) (Y.lg_add i)
  have hadd : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext j
    exact eval_points_two (Y.B.G.F j)
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => Y.B.G.F q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => Y.B.G.const q.2
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => pt C (n := 2) dd k q.2) :=
    fun k => MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  rw [hadd, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst, MvPowerSeries.subst_add hPP,
    MvPowerSeries.subst_comp_subst_apply hA hPP, MvPowerSeries.subst_comp_subst_apply (hX 0) hPP,
    MvPowerSeries.subst_comp_subst_apply (hX 1) hPP] at key
  simp only [pt, MvPowerSeries.subst_X hPP] at key
  exact key

end Step2

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieMemC
section -- merged from Formalism.LocalToGlobal.CharacterGerms.ValBlocksCChart
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Gen

variable {d : ℕ} [NeZero d] (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

abbrev rdS (o : Orb) : RowData C V d (fun _ => I0 o) (JJ fun _ => I0 o) := (Y.rawSelf (p o)).rowData (H o)

def imgFamS {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_self (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : ValO (fun o => rdS Y p H o) N (imgFamS Y p Ls n pl) ν := by
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have key := val_self (hs := hs) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po) (hQ := hQ)
    (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hg)
  exact WithBot.coe_le_coe.1 (hν.trans key)

end Gen

section Two

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y 2 (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

end Two

end Formalism.L2.FormalSeriesBounds.RF
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIs {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (o : Orb) : Type := Σ t : ZMod 2, Fin (r (tau o t))

def subG {C : Type} [Field C] {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T)
    (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n) :
    MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  MvPolynomial.aeval fun x => ∑ col : Fin 2, MvPolynomial.C (gm x.2.1 x.2.2.2.1 col x.2.2.1) *
    MvPolynomial.X (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n)

def WtTieC {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (gaC : Orb → ZMod 2 → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o s (i : ℕ), i < r (tau o s) → a (tau o s) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o s)), gaC o s k) ∧
  ∀ σ, (∀ o s, tau o s ≠ σ) → ∀ i, i < r σ → a σ i = 0

structure SelfConjugatePlaceSetting {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N) : Prop where

  inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2
  conj : ∀ o t, cc (tau o t) = tau o (t + 1)

  gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1

  hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  alt : ∀ o, (X o).Alt
  hj : ∀ o, (X o).j' < (X o).n
  supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s

  mon : ∀ o, ∀ q ∈ L o, ∀ g e M, q.1 = GlobalTheory.mon g e M → ∃ s : ZMod 2, ∀ b k, b ≠ s → e b k = 0
  wt : ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k
  tie : WtTieC r tau gaC a
  plinj : Function.Injective pl

def IsotropicToStdSubstHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n) (isX : T → Prop),
      subG r tau gm plc (blkProd X F N L pl) ∈ harmK r n C cc isX (fun _ => 1)

def IsotropicToStdSubstLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowInv r n C (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstLineDegree : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowDeg r n C a (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N) (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n)
    (O : Subring C), (∀ o t q s, gm o t q s ∈ O) → ∀ m, (subG r tau gm plc (blkProd X F N L pl)).coeff m ∈ O

section Mem

variable {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  (O : Subring C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def selfConjTuplesInLattice : Set (∀ o, MvPolynomial (Fin N × WV fun _ => IIs r tau o) C) :=
  {Po | subG r tau gm plc (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

theorem block_membership_self_conj_first (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree) (h4 : IsotropicToStdSubstIntegral)
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (conj : ∀ o t, cc (tau o t) = tau o (t + 1))
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (gm_int : ∀ o t q s, gm o t q s ∈ O)
    (hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (alt : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s) (tie : WtTieC r tau gaC a) :
    BlockMembershipSelfConjugate X N F (selfConjTuplesInLattice r cc isX a tau gm O plc) gaC := by
  intro L mon wt pl plinj
  have H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl := ⟨inj, conj, gm_hyp, hty, std, alt, hj, supp, mon, wt, tie, plinj⟩
  exact ⟨⟨h1 C V T r cc a Orb tau gm J X F gaC N L pl H n plc isX, h2 C V T r cc a Orb tau gm J X F gaC N L pl H n plc,
    h3 C V T r cc a Orb tau gm J X F gaC N L pl H n plc⟩, h4 C V T r Orb tau gm J X F N L pl n plc O gm_int⟩

end Mem

def OP {C : Type} [Field C] (O : Subring C) (σ : Type) : Subring (MvPolynomial σ C) :=
  (MvPolynomial.map O.subtype).range

theorem coeff_mem_of_OP {C : Type} [Field C] {O : Subring C} {σ : Type} {P : MvPolynomial σ C} (h : P ∈ OP O σ)
    (m : σ →₀ ℕ) : P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map]
  exact (Q.coeff m).2

theorem aeval_mem_OP {C : Type} [Field C] {O : Subring C} {σ τ : Type} (f : σ → MvPolynomial τ C)
    (hf : ∀ x, f x ∈ OP O τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) : MvPolynomial.aeval f P ∈ OP O τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  clear h
  induction Q using MvPolynomial.induction_on
  · rename_i z
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, eq_intCast (Int.castRingHom C) z, map_intCast]
    exact intCast_mem _ z
  · rename_i p q hp hq
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hp hq
  · rename_i p x hp
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp (hf x)

theorem first_chern_integral : IsotropicToStdSubstIntegral := by
  intro C _ V T r Orb _ tau gm J _ X F N L pl n plc O hO m
  apply coeff_mem_of_OP
  unfold subG
  refine aeval_mem_OP _ (fun x => ?_) (blkProd_mem_ZP X F N L pl)
  refine sum_mem fun col _ => mul_mem ?_ ?_
  · exact RingHom.mem_range.2 ⟨MvPolynomial.C ⟨_, hO _ _ _ _⟩, by rw [MvPolynomial.map_C]; rfl⟩
  · exact RingHom.mem_range.2 ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩

end Formalism.L2.FormalSeriesBounds.RF
end
end

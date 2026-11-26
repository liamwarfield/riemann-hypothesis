module

public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieValG
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}

def colLin (M : Var → Fin n × Fin dd → C) (b : Fin n) : Var → Fin dd → C := fun x i => M x (b, i)

variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

def linPt (q : Fin n × Fin dd) : MvPowerSeries Var C := MvPowerSeries.subst (linS (colLin M q.1)) (e Y q.2)

def linPull (F : PS C n dd) : MvPowerSeries Var C := MvPowerSeries.subst (linPt Y M) F

theorem cc_linPt (q : Fin n × Fin dd) : MvPowerSeries.constantCoeff (linPt Y M q) = 0 := by
  unfold linPt
  exact VP.cc_subst (fun s => by simp [linS, MvPowerSeries.smul_eq_C_mul]) (cc_e Y q.2)

theorem linPull_mul (F G : PS C n dd) : linPull Y M (F * G) = linPull Y M F * linPull Y M G := by
  unfold linPull
  exact VP.subst_mul (cc_linPt Y M) F G

theorem linPull_prod {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    linPull Y M (∏ i ∈ s, F i) = ∏ i ∈ s, linPull Y M (F i) := by
  unfold linPull
  exact VP.subst_prod (cc_linPt Y M) s F

theorem linear_pullback_eval_point_zero (b : Fin n) (G : PS C 2 dd) :
    linPull Y M (ev (n := n) ![pt C dd b, 0] G) =
      MvPowerSeries.subst (linS (colLin M b)) (MvPowerSeries.subst (exZero Y) G) := by
  have hL : ∀ s, MvPowerSeries.constantCoeff (linS (colLin M b) s : MvPowerSeries Var C) = 0 := fun s => by
    simp [linS, MvPowerSeries.smul_eq_C_mul]
  unfold linPull ev
  rw [VP.subst_subst (fun q => VP.constantCoeff_two_points_zero b q) (cc_linPt Y M), VP.subst_subst (cc_exZero Y) hL]
  congr 1
  funext q
  rcases q with ⟨i, k⟩
  fin_cases i
  · simp [pt, exZero, linPt, e, VP.subst_X (cc_linPt Y M)]
  · simp [exZero, VP.subst_zero' (cc_linPt Y M), VP.subst_zero' hL]

def RR (b : Fin n) (i j : Fin dd) : MvPowerSeries Var C :=
  linPull Y M (ev (n := n) ![pt C dd b, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.FK C j)))

theorem linPull_DofN (b : Fin n) (u : Fin dd → C) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b u F) =
      ∑ j, (∑ i, MvPowerSeries.C (u i) * RR Y M b i j) * linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F) := by
  unfold DofN
  simp only [← MvPowerSeries.smul_eq_C_mul]
  simp only [linPull, RR, VP.subst_sum (cc_linPt Y M), VP.subst_mul (cc_linPt Y M), VP.subst_smul (cc_linPt Y M)]

theorem pderiv_linPull (x : Var) (F : PS C n dd) :
    MvPowerSeries.pderiv (R := C) x (linPull Y M F) =
      ∑ b, ∑ j, (∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F) := by
  have hE := expODE Y
  unfold ExpODESt at hE
  have hJ : ∀ b j, MvPowerSeries.pderiv (R := C) x (linPt Y M (b, j)) =
      ∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j := by
    intro b j
    simp only [linPt, e, hE, pderiv_subst_linS, colLin, RR, linear_pullback_eval_point_zero, MvPowerSeries.smul_eq_C_mul]
  unfold linPull
  rw [pderiv_subst (VP.og (cc_linPt Y M)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hJ b j]

theorem dpullG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b0 u F) = ∑ x, c x • MvPowerSeries.pderiv (R := C) x (linPull Y M F) := by
  have key : ∀ b j, ∑ x, c x • ((∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
      linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F)) =
      (∑ i, MvPowerSeries.C (if b = b0 then u i else 0) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F) := by
    intro b j
    simp_rw [← hc b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, MvPowerSeries.smul_eq_C_mul, mul_assoc]
    exact Finset.sum_comm
  rw [linPull_DofN]
  simp only [pderiv_linPull, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single b0 (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem jet_iterG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (k : ℕ) :
    ∀ (q : MvPolynomial Var C) (g : PS C n dd),
      jetAt0 q (linPull Y M ((DofN (Y.B.FK C) b0 u)^[k] g)) =
        jetAt0 (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) (linPull Y M g) := by
  induction k with
  | zero => intro q g; simp
  | succ k ih =>
    intro q g
    rw [Function.iterate_succ_apply, ih, dpullG Y M b0 u c hc]
    have h := jet_lin (fun x : Var => x) (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) c (linPull Y M g)
    rw [← h]
    congr 1
    ring

theorem jet_listG {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → Var → C) (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) →
    ∀ q : MvPolynomial Var C,
      jetAt0 q (linPull Y M (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ x, MvPolynomial.C (co l x) * MvPolynomial.X x) ^ m l).prod)
          (linPull Y M f) := by
  intro ls
  induction ls with
  | nil => intro _ q; simp
  | cons l ls ih =>
    intro h q
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    have h' : ∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0 :=
      fun ℓ hℓ => h ℓ (by simp [hℓ])
    by_cases hm : m l = 0
    · rw [hm]
      simp only [Function.iterate_zero, id, pow_zero, one_mul]
      exact ih h' q
    · rw [jet_iterG Y M (cp l) (uv l) (co l) (h l (by simp) hm) (m l), ih h']
      congr 1
      ring

theorem logCoordG {ι : Type} [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (co : ι → Var → C)
    (hco : ∀ ℓ ∈ P.vars, ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) (F : PS C n dd) :
    MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) =
      jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) P) (linPull Y M F) := by
  have hj1 : ∀ G : MvPowerSeries Var C, jetAt0 (1 : MvPolynomial Var C) G = MvPowerSeries.constantCoeff G :=
    fun G => by simpa using jet_C (σ := Var) (1 : C) G
  have hD : ∀ m ∈ P.support, MvPowerSeries.constantCoeff (DmonN (Y.B.FK C) cp uv m F) =
      jetAt0 (∏ ℓ, (∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) ^ m ℓ) (linPull Y M F) := by
    intro m hm
    have h1 := jet_listG Y M cp uv co m F (Finset.univ : Finset ι).toList
      (fun ℓ _ hmℓ => hco ℓ ((MvPolynomial.mem_vars_iff_mem_support ℓ).2 ⟨m, hm, Finsupp.mem_support_iff.2 hmℓ⟩)) 1
    rw [one_mul, Finset.prod_map_toList, hj1, linPull, VP.cc_subst_eq (cc_linPt Y M)] at h1
    exact h1
  unfold DpolyN
  conv_rhs => rw [MvPolynomial.as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [tpjet_jetAt0_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [MvPolynomial.aeval_monomial, map_mul, MvPowerSeries.constantCoeff_C, hD m hm, MvPolynomial.algebraMap_eq,
    mul_comm (MvPolynomial.C (AddMonoidAlgebra.coeff P m)), jet_mul_C, Finsupp.prod_fintype _ _ (fun ℓ => pow_zero _)]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

abbrev IS (I0 : Orb → Type) : Orb → Fin 2 → Type := fun o _ => I0 o

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

def uS (w : WVO (IS I0)) : Fin 2 × Fin dd → C := (Y.rawSelf (p w.1)).u w.2.1 w.2.2

def pull2 (F : PS C 2 dd) : MvPowerSeries (WVO (IS I0)) C := VP.linPull Y (uS Y p) F

def MS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (x : Fin N × WVO (IS I0)) (q : Fin n × Fin dd) : C :=
  ∑ col : Fin 2, if pl (x.1, col) = q.1 then uS Y p x.2 (col, q.2) else 0

def pullS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : PS C n dd) : MvPowerSeries (Fin N × WVO (IS I0)) C :=
  VP.linPull Y (MS Y p pl) F

def UnitSelfSt : Prop :=
  SelfSep Y p → ∃ U : PS C 2 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)

def GermLiftSelfSt (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g))
    (t : ∀ _ : Fin 2, I0 o → MvPowerSeries (I0 o) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 2 dd, IntS V G ∧ pull2 Y p G = toAllS (I := IS I0) o F

end Defs

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

theorem MS_pl (ρ' ρ : Fin N) (w : WVO (IS I0)) (col : Fin 2) (i : Fin dd) :
    MS Y p pl (ρ', w) (pl (ρ, col), i) = if ρ' = ρ then uS Y p w (col, i) else 0 := by
  simp only [MS, pl.injective.eq_iff, Prod.mk.injEq]
  by_cases h : ρ' = ρ
  · simp [h]
  · simp [h]

theorem MS_off (x : Fin N × WVO (IS I0)) (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) :
    MS Y p pl x (b, i) = 0 := by
  simp only [MS]
  exact Finset.sum_eq_zero fun col _ => if_neg fun h => hb ⟨_, h⟩

theorem linPt_pl (ρ : Fin N) (col : Fin 2) (i : Fin dd) :
    linPt Y (MS Y p pl) (pl (ρ, col), i) = rowOf ρ (linPt Y (uS Y p) (col, i)) := by
  simp only [linPt]
  rw [rowOf_eq, rename_subst_linS]
  congr 1
  funext j
  simp only [linS, map_sum, map_smul, MvPowerSeries.rename_X]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ]
  · simp only [colLin, MS_pl, if_true]
    rfl
  · intro ρ' _ hρ'
    simp [colLin, MS_pl, hρ']
  · simp

theorem linPt_off (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) : linPt Y (MS Y p pl) (b, i) = 0 := by
  have h0 : linS (colLin (MS Y p pl) b) = 0 := by
    funext j
    simp [linS, colLin, MS_off Y p pl _ b hb]
  have hc := cc_linPt Y (MS Y p pl) (b, i)
  simp only [linPt, h0, MvPowerSeries.subst_zero_eq_C_constantCoeff] at hc ⊢
  simp at hc
  simp [hc]

theorem cc_ptPl (ρ : Fin N) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  obtain ⟨c, i⟩ := q
  fin_cases c <;> simp [pt]

theorem pullS_plane (ρ : Fin N) (G : PS C 2 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] G) = rowOf ρ (pull2 Y p G) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_ptPl pl ρ q)
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hL2 : MvPowerSeries.HasSubst (linPt Y (uS Y p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hR : MvPowerSeries.HasSubst (fun w : WVO (IS I0) =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO (IS I0)) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  simp only [pullS, pull2, linPull, ev, rowOf]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL, MvPowerSeries.subst_comp_subst_apply hL2 hR]
  congr 1
  funext ⟨c, i⟩
  have hc : (![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) c i =
      MvPowerSeries.X (pl (ρ, c), i) := by
    fin_cases c <;> rfl
  rw [hc, MvPowerSeries.subst_X hL, linPt_pl]
  rfl

theorem pullS_col (ρ : Fin N) (col : Fin 2) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd (pl (ρ, col))] E) = rowOf ρ (pull2 Y p (ev (n := 2) ![pt C dd col] E)) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd (pl (ρ, col))] : Fin 1 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hA' : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hL2 : MvPowerSeries.HasSubst (linPt Y (uS Y p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hR : MvPowerSeries.HasSubst (fun w : WVO (IS I0) =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO (IS I0)) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hcol : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => linPt Y (uS Y p) (col, q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ _)
  have hin : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (linPt Y (uS Y p))
      ((![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2)) = fun q => linPt Y (uS Y p) (col, q.2) := by
    funext ⟨c, i⟩
    fin_cases c
    exact MvPowerSeries.subst_X hL2 (col, i)
  simp only [pullS, pull2, linPull, ev, rowOf]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL, MvPowerSeries.subst_comp_subst_apply hA' hL2, hin,
    MvPowerSeries.subst_comp_subst_apply hcol hR]
  congr 1
  funext ⟨c, i⟩
  have hc0 : c = 0 := Subsingleton.elim _ _
  subst hc0
  change MvPowerSeries.subst (linPt Y (MS Y p pl)) (MvPowerSeries.X (pl (ρ, col), i)) =
    MvPowerSeries.subst (fun w => MvPowerSeries.X (ρ, w)) (linPt Y (uS Y p) (col, i))
  rw [MvPowerSeries.subst_X hL, linPt_pl]
  rfl

theorem pullS_off (b : Fin n) (hb : b ∉ Set.range pl) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd b] E) = MvPowerSeries.C (MvPowerSeries.constantCoeff E) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  simp only [pullS, linPull, ev]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL]
  have h0 : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (linPt Y (MS Y p pl))
      ((![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2)) = 0 := by
    funext ⟨c, i⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    subst hc0
    change MvPowerSeries.subst (linPt Y (MS Y p pl)) (MvPowerSeries.X (b, i)) = 0
    rw [MvPowerSeries.subst_X hL, linPt_off Y p pl b hb i]
  rw [h0, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem hco_of_img {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (ℓ : ι)
    (co : Fin N × WVO (IS I0) → C)
    (h : ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : WVO (IS I0), co (ρ, w) • (Y.rawSelf (p w.1)).u w.2.1 w.2.2) (b : Fin n) (i : Fin dd) :
    ∑ x, co x * MS Y p pl x (b, i) = if b = cp ℓ then uv ℓ i else 0 := by
  obtain ⟨ρ, col, hpl, hco0, hvec⟩ := h
  have key : ∀ c : Fin 2, (∑ x : Fin N × WVO (IS I0),
      co x * (if pl (x.1, c) = b then uS Y p x.2 (c, i) else 0)) =
      if pl (ρ, c) = b then (if c = col then uv ℓ i else 0) else 0 := by
    intro c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ
      (fun ρ' _ hρ' => Finset.sum_eq_zero fun w _ => by simp [hco0 ρ' w hρ']) (by simp)]
    by_cases hb' : pl (ρ, c) = b
    · have h1 := congrFun hvec (c, i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [hb', if_true]
      rw [h1]
      rfl
    · simp [hb']
  simp only [MS, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single col (fun c _ hc => by simp [hc]) (by simp)]
  simp only [if_true]
  by_cases hb : b = cp ℓ
  · simp [hb, hpl]
  · have h2 : pl (ρ, col) ≠ b := fun h' => hb (h'.symm.trans hpl)
    simp [h2, hb]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

namespace VP

theorem cc_mvExp' {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp h) = 1 := by
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (h ^ k) / (k.factorial : C)) = 1
  simp

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem pullback_two_var_mul (F G : PS C 2 dd) : pull2 Y p (F * G) = pull2 Y p F * pull2 Y p G := by
  unfold pull2
  exact linPull_mul _ _ F G

theorem pullback_two_var_prod {ι : Type} (s : Finset ι) (F : ι → PS C 2 dd) :
    pull2 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull2 Y p (F i) := by
  unfold pull2
  exact linPull_prod _ _ s F

theorem pullback_two_var_one : pull2 Y p (1 : PS C 2 dd) = 1 := by
  have h := pullback_two_var_prod Y p (∅ : Finset Unit) (fun _ => (1 : PS C 2 dd))
  simpa using h

theorem pullS_exp {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (E : PS C 1 dd) (hE : MvPowerSeries.constantCoeff E = 1) :
    pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ ρ : Fin N, rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] E)) := by
  have hprod : pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ b : Fin n, pullS Y p pl (ev (n := n) ![pt C dd b] E) := by
    unfold pullS
    exact linPull_prod _ _ _ _
  rw [hprod]
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map pl →
      pullS Y p pl (ev (n := n) ![pt C dd b] E) = 1 := by
    intro b _ hb
    have hb' : b ∉ Set.range pl := by simpa using hb
    rw [pullS_off (b := b) (hb := hb'), hE, map_one]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map pl)) hoff, Finset.prod_map,
    Fintype.prod_prod_type]
  simp_rw [pullS_col]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [pullback_two_var_prod, rowOf_prod]

end VP

theorem valuation_eq_self_of_unit_germ (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (h2 : UnitSelfSt Y p) (h3 : GermLiftSelfSt Y p H) : ValEqSelfSt Y p H Ls n := by
  intro hs N pl P hP Po hQ kind hk S t ht gr hg
  obtain ⟨U, hUi, hU0, hU⟩ := h2 hs
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hUi hU0
  choose G hGi hG using fun (o : Orb) (ρ : Fin N) => h3 hs o (S o) (t o) (ht o) (gr o ρ) (hg o ρ)
  obtain ⟨co, hco, hQe⟩ := hQ
  refine ⟨∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ), ?_, ?_⟩
  · refine VP.IntS_prod _ fun ρ _ => ?_
    unfold ev
    refine IntS.subst (VP.cc_ptPl pl ρ) (fun q => ?_) (hU'i.mul (VP.IntS_prod _ fun o _ => hGi o ρ))
    obtain ⟨g, i⟩ := q
    fin_cases g <;> exact VP.IntS_X _
  · have hk0 : MvPowerSeries.constantCoeff ((Y.k : C) • Y.B.hL C Y.h Y.w0) = 0 := VP.cc_smul _ (VP.cc_hL Y)
    have hE1 : MvPowerSeries.constantCoeff (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) = 1 := by
      rw [VP.expS_eq _ hk0, VP.cc_mvExp']
    have hrow : ∀ ρ : Fin N,
        rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) *
          rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col]
            (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow)) := by
      intro ρ
      rw [← VP.rowOf_mul, hU, VP.pullback_two_var_mul, VP.pullback_two_var_prod]
      have e2 : (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
          (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) =
          ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
        have e3 : pull2 Y p U' * pull2 Y p U = 1 := by rw [← VP.pullback_two_var_mul, hUU, VP.pullback_two_var_one]
        calc (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
              (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow))
            = (pull2 Y p U' * pull2 Y p U) *
                ((∏ o, pull2 Y p (G o ρ)) * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) := by ring
          _ = ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
              rw [e3, one_mul, ← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun o _ => by rw [hG o ρ, VP.toAllS_mul]
      rw [e2, VP.rowOf_prod]
      exact Finset.prod_congr rfl fun o _ => by rw [VP.rowOf_toAllS, VP.rowCopy_mul_exp]
    have hser : pullS Y p pl ((∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) *
        FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow))) := by
      have hpl : ∀ ρ : Fin N, VP.linPull Y (MS Y p pl)
          (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) =
          rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) := fun ρ => VP.pullS_plane Y p pl ρ _
      rw [VP.expS_copies, show pullS Y p pl (_ * _) = _ from VP.linPull_mul Y _ _ _,
        show VP.linPull Y (MS Y p pl) (∏ b : Fin n, _) = _ from VP.pullS_exp Y p pl _ hE1,
        VP.linPull_prod, Finset.prod_congr rfl fun ρ _ => hpl ρ,
        ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun ρ _ => hrow ρ, Finset.prod_comm]
      exact Finset.prod_congr rfl fun o _ => (map_prod _ _ _).symm
    unfold FBChart.nab nabValN
    rw [VP.logCoordG Y (MS Y p pl) (Ls.cp n) (Ls.uv n) P co
      (fun ℓ hℓ b i => VP.hco_of_img Y p pl (Ls.cp n) (Ls.uv n) ℓ (co ℓ) (hco ℓ hℓ) b i), ← hQe]
    rw [show VP.linPull Y (MS Y p pl) _ = _ from hser, VP.jet_orb]
    exact Finset.prod_congr rfl fun o _ =>
      leaf_holds C V d (fun _ => I0 o) (Fin 2 × Fin dd) (Y.rawSelf (p o)) (H o) N (Po o) (kind o) (hk o) (gr o)

end Formalism.L2.FormalSeriesBounds

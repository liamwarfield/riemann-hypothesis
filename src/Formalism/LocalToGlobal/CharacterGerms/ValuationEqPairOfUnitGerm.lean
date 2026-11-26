module

public import Formalism.LocalToGlobal.CharacterGerms.SubstSubst

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.PullbackLogCoordsEvalZero
section -- merged from Formalism.LocalToGlobal.CharacterGerms.LogCoordOfDpull
section -- merged from Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfLogUnitGerm
section -- merged from Formalism.LocalToGlobal.CharacterGerms.IntSProd
section -- merged from Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Pull

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_X {σ : Type} (s : σ) : MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries σ C) = 0 := MvPowerSeries.constantCoeff_X s

end Pull

section Emb

variable {n : ℕ}

def eRow (b : Fin n) : WVO I ↪ Fin n × WVO I := ⟨fun w => (b, w), Prod.mk_right_injective b⟩

def eAll (n : ℕ) (o : Orb) : Fin n × WV (I o) ↪ Fin n × WVO I :=
  ⟨fun x => (x.1, (⟨o, x.2⟩ : WVO I)), fun x y h => by
    have h1 : x.1 = y.1 := (Prod.ext_iff.1 h).1
    have h2 : (⟨o, x.2⟩ : WVO I) = ⟨o, y.2⟩ := (Prod.ext_iff.1 h).2
    exact Prod.ext h1 (eq_of_heq (Sigma.mk.inj h2).2)⟩

theorem rowOf_eq (b : Fin n) (F : MvPowerSeries (WVO I) C) : rowOf b F = MvPowerSeries.rename (eRow b) F := by
  unfold rowOf
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem rowOf_toAllS (b : Fin n) (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    rowOf b (toAllS o F) = MvPowerSeries.rename (eAll n o) (rowCopy b F) := by
  have e1 : toAllS o F =
      MvPowerSeries.rename (Function.Embedding.sigmaMk (β := fun o => WV (I o)) o) F := by
    unfold toAllS
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  rw [rowOf_eq, e1, rtj_rowCopy_eq, MvPowerSeries.rename_rename, MvPowerSeries.rename_rename]
  exact rtj_rename_congr (by funext w; rfl) F

theorem rowOf_mul (b : Fin n) (F G : MvPowerSeries (WVO I) C) : rowOf b (F * G) = rowOf b F * rowOf b G := by
  unfold rowOf
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem rowOf_prod (b : Fin n) {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WVO I) C) :
    rowOf b (∏ i ∈ s, F i) = ∏ i ∈ s, rowOf b (F i) := by
  unfold rowOf
  exact VP.subst_prod (fun _ => MvPowerSeries.constantCoeff_X _) s F

theorem toAllS_mul (o : Orb) (F G : MvPowerSeries (WV (I o)) C) : toAllS o (F * G) = toAllS o F * toAllS o G := by
  unfold toAllS
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem jet_orb (Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C) (Φ : ∀ o, MvPowerSeries (Fin n × WV (I o)) C) :
    jetAt0 (∏ o, toAll o (Po o)) (∏ o, MvPowerSeries.rename (eAll n o) (Φ o)) = ∏ o, jetAt0 (Po o) (Φ o) := by
  have hA : ∀ o ∈ (Finset.univ : Finset Orb), ∀ o' ∈ (Finset.univ : Finset Orb), o ≠ o' →
      Disjoint (Set.range (eAll (I := I) n o)) (Set.range (eAll (I := I) n o')) := by
    intro o _ o' _ h
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact h (congrArg (fun z : Fin n × WVO I => z.2.1) hy).symm
  have hT : ∀ o, toAll o (Po o) = MvPolynomial.rename (eAll n o) (Po o) := fun o => rfl
  exact (rtj_jet_prod (fun o => Set.range (eAll (I := I) n o)) Finset.univ hA
    (fun o => toAll o (Po o)) (fun o => MvPowerSeries.rename (eAll n o) (Φ o))
    (fun o _ => by rw [hT]; exact rtj_rename_supported _ _)
    (fun o _ => rtj_serIn_rename _ _)).trans
    (Finset.prod_congr rfl fun o _ => by rw [hT]; exact rtj_jet_rename _ _ _)

end Emb

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

section Inv

variable {C : Type} [Field C] {V : VF C} {σ : Type}

theorem inv_int {c : C} (hc : V.v c = 0) : V.Ge 0 c⁻¹ := by
  simp [VF.Ge, AddValuation.map_inv, hc]

theorem intInv {U : MvPowerSeries σ C} (hU : IntS V U) (h0 : V.v (MvPowerSeries.constantCoeff U) = 0) :
    ∃ U' : MvPowerSeries σ C, IntS V U' ∧ U' * U = 1 := by
  have hc0 : MvPowerSeries.constantCoeff U ≠ 0 := by
    intro h
    simp [h] at h0
  refine ⟨U⁻¹, ?_, MvPowerSeries.inv_mul_cancel _ hc0⟩
  have hge0 : V.Ge 0 (0 : C) := by simp [VF.Ge]
  have hmul : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a * b) := by
    intro a b ha hb
    unfold VF.Ge at *
    rw [AddValuation.map_mul]
    simpa using add_le_add ha hb
  have hadd : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a + b) :=
    fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)
  have hneg : ∀ a : C, V.Ge 0 a → V.Ge 0 (-a) := by
    intro a ha
    unfold VF.Ge at *
    rwa [AddValuation.map_neg]
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hμ
    · exact inv_int h0
    · refine hmul _ _ (hneg _ (inv_int h0)) ?_
      refine Finset.sum_induction _ (V.Ge 0) hadd hge0 (fun x _ => ?_)
      split_ifs with hlt
      · exact hmul _ _ (hU x.1) (ih x.2 hlt)
      · exact hge0

theorem IntS_prod {ι : Type} (s : Finset ι) {F : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) := by
  classical
  have hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c := by
    rintro c (rfl | rfl)
    · simp [VF.Ge]
    · simp [VF.Ge]
  have hone : IntS V (1 : MvPowerSeries σ C) := by
    intro μ
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact hge 1 (Or.inr rfl)
    · exact hge 0 (Or.inl rfl)
  have hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G) := by
    intro F G hF hG μ
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)
    · exact le_trans (le_min ha hb) (V.v.map_add a b)
    · have h1 := add_le_add (hF q.1) (hG q.2)
      unfold VF.Ge
      rw [AddValuation.map_mul]
      simpa using h1
  induction s using Finset.induction_on with
  | empty => simpa using hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IntS_X (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · simp [VF.Ge]
  · simp [VF.Ge]

end Inv

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt C n dd)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS C m dd) :
    MvPowerSeries.constantCoeff (ev a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])
    rw [h0, smul_zero]

theorem cc_h (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff Y.h = 0 := by
  have hax := Y.gauge.ax0
  have e : MvPowerSeries.constantCoeff (ev (n := 1) ![0, pt C dd 0] Y.h) = MvPowerSeries.constantCoeff Y.h :=
    cc_ev_lemma _ (fun j i => by fin_cases j <;> simp [pt]) _
  rw [← e, hax, map_zero]

theorem cc_hL (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL
  rw [cc_ev_lemma _ ?_ _]
  · exact cc_h Y
  · intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0
      simp only [comp1]
      rw [cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]

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

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

theorem expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
  have ha : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hc : ∀ b : Fin n, MvPowerSeries.constantCoeff (ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) = 0 := fun b =>
    (ordGE_one_iff _).1 (ordGE_subst (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))
      ((ordGE_one_iff _).2 (VP.cc_hL Y)))
  have hs : ∀ b : Fin n, ev (n := n) ![pt C dd b] ((Y.k : C) • Y.B.hL C Y.h Y.w0) =
      (Y.k : C) • ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) := fun b =>
    MvPowerSeries.subst_smul (hasSubst_of_ordGE (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [VP.expS_eq _ (cc_smul _ (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hc b)), Finset.smul_sum,
    Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun b _ => cc_smul _ (hc b))]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [VP.expS_eq _ (cc_smul _ (VP.cc_hL Y))]
  show _ = MvPowerSeries.subst (fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (mvExp _)
  rw [VP.subst_exp (ha b) (cc_smul _ (VP.cc_hL Y))]
  exact congrArg mvExp (hs b).symm

theorem rowCopy_mul_exp {J : Fin 2 → Type} {n : ℕ} (b : Fin n) (F L : MvPowerSeries (WV J) C) :
    rowCopy b (F * mvExp L) = rowCopy b F * mvExp (rowCopy b L) := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, rtj_rowCopy_eq, map_mul]
  congr 1
  ext x
  rw [MvPowerSeries.coeff_rename]
  show _ = ∑ k ∈ Finset.range (x.degree + 1),
    MvPowerSeries.coeff x ((MvPowerSeries.rename (rtjR b) L) ^ k) / (k.factorial : C)
  simp_rw [← map_pow, MvPowerSeries.coeff_rename, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hdeg : y.degree = x.degree := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_preimage] at hy
    rw [← hy, Finsupp.degree_mapDomain]
  show ∑ k ∈ Finset.range (y.degree + 1), _ = _
  rw [hdeg]

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
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  set c := MvPowerSeries.constantCoeff f with hc
  have hg : MvPowerSeries.constantCoeff (f - algebraMap C (MvPowerSeries σ C) c) = 0 := by
    simp [hc, MvPowerSeries.algebraMap_apply]
  have hf : f = algebraMap C (MvPowerSeries σ C) c + (f - algebraMap C (MvPowerSeries σ C) c) := by
    ring
  have h1 : MvPowerSeries.subst a (algebraMap C (MvPowerSeries σ C) c) =
      algebraMap C (MvPowerSeries τ C) c := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact (MvPowerSeries.substAlgHom hs).commutes c
  rw [hf, MvPowerSeries.subst_add hs, map_add (f := _), h1, constantCoeff_subst_zero ha hg]
  simp [MvPowerSeries.algebraMap_apply]

private theorem jetAt0_zero_left' {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  simp [jetAt0]

private theorem jetAt0_finset_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left']
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

theorem jet_lin {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv (R := C) (e w) G) := by
  rw [Finset.mul_sum, jetAt0_finset_sum_left, jet_sum_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, jet_mul_X, jet_mul_C, jet_smul_right, dVar_eq_pderiv]

variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

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
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0

def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv (R := C) i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.FK C j))

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_exZero (q : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (exZero Y q) = 0 := by
  unfold exZero
  split_ifs
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex q.2) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Y.ex_const _
  · exact map_zero _

theorem subst_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (Formalism.L2.FormalSeriesBounds.VP.hs ha), map_zero]

theorem constantCoeff_two_points_zero {n : ℕ} (b : Fin n) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simp

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

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  ext e
  rw [MvPowerSeries.coeff_subst (hs (fun _ => MvPowerSeries.constantCoeff_zero)), finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [he, MvPowerSeries.coeff_C, MvPowerSeries.coeff_one]
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ n => (0 : MvPowerSeries τ C) ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (zero_pow hs')
    simp [h0]

variable (Y : FBChart C V O dd)

def l (m : Fin dd) : MvPowerSeries (Fin dd) C := un1 (Y.lg m)

def e (k : Fin dd) : MvPowerSeries (Fin dd) C := un1 (Y.ex k)

theorem cc_l (m : Fin dd) : MvPowerSeries.constantCoeff (l Y m) = 0 := by
  have h := Y.lg_lin m 0 (by simp)
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg m) = 0
  rw [Finsupp.mapDomain_zero, h]
  simp

theorem cc_e (k : Fin dd) : MvPowerSeries.constantCoeff (e Y k) = 0 := by
  have h := Y.ex_const k
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.ex k) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]

theorem exlg (n : Fin dd) : MvPowerSeries.subst (l Y) (e Y n) = MvPowerSeries.X n := by
  have ha : ∀ i, MvPowerSeries.constantCoeff (Y.lg i) = 0 := fun i => by
    rw [← constantCoeff_uncurry]; exact cc_l Y i
  show MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex n)) = _
  rw [uncurry_comp ha, Y.ex_lg]
  exact uncurry_X n

theorem lgex (m : Fin dd) : MvPowerSeries.subst (e Y) (l Y m) = MvPowerSeries.X m := by
  show MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 (Y.lg m)) = _
  rw [uncurry_comp Y.ex_const, Y.lg_ex]
  exact uncurry_X m

theorem cc_F (k : Fin dd) : MvPowerSeries.constantCoeff (Y.B.G.F k) = 0 := Y.B.G.const k

theorem ev_id (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  have h : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨i, k⟩; fin_cases i <;> rfl
  unfold ev
  rw [h, MvPowerSeries.subst_self]
  rfl

theorem l_add (m : Fin dd) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (l Y m) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (l Y m) +
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (l Y m) := by
  have hF : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = fun k => Y.B.G.F k :=
    funext fun k => ev_id (Y.B.G.F k)
  have h := Y.lg_add m
  rw [hF, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  show MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 (Y.lg m)) =
    MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 (Y.lg m)) +
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 (Y.lg m))
  rw [subst_singlePointUncurry (fun k => Y.B.G.const k), subst_singlePointUncurry (fun k => MvPowerSeries.constantCoeff_X _),
    subst_singlePointUncurry (fun k => MvPowerSeries.constantCoeff_X _)]
  exact h

theorem F_exZero (k : Fin dd) : MvPowerSeries.subst (exZero Y) (Y.B.G.F k) = e Y k := by

  set u : Fin 1 × Fin dd → MvPowerSeries (Fin dd) C := fun q => un1 (Y.ex q.2) with hu_def
  have hu : MvPowerSeries.HasSubst u := hs (fun q => cc_e Y q.2)
  have hz : MvPowerSeries.HasSubst (exZero Y) := hs (fun q => by
    unfold exZero
    split_ifs
    · exact cc_e Y q.2
    · simp)
  have hsw : MvPowerSeries.HasSubst
      (fun q : Fin 2 × Fin dd => (![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) q.1 q.2) :=
    hs (fun q => by
      rcases q with ⟨i, j⟩
      fin_cases i <;> exact MvPowerSeries.constantCoeff_X _)
  have hun : MvPowerSeries.HasSubst
      (fun q : Fin 2 × Fin dd => (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) q.1 q.2) :=
    hs (fun q => by
      rcases q with ⟨i, j⟩
      fin_cases i
      · simp
      · exact MvPowerSeries.constantCoeff_X _)
  have hu0 : MvPowerSeries.subst u (0 : MvPowerSeries (Fin 1 × Fin dd) C) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hu, map_zero]
  have hz0 : MvPowerSeries.subst (exZero Y) (0 : PS C 2 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hz, map_zero]
  have h1 := Y.B.G.comm k
  have h2 := congrArg (MvPowerSeries.subst u) (Y.B.G.unit k)
  unfold ev at h1 h2
  rw [← h1, MvPowerSeries.subst_comp_subst_apply hsw hz]
  rw [MvPowerSeries.subst_comp_subst_apply hun hu, MvPowerSeries.subst_X hu] at h2
  show _ = u (0, k)
  convert h2 using 2
  funext q
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [pt, MvPowerSeries.subst_X hz, exZero, hu0]
  · show MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((0 : Fin 2), j)) =
      MvPowerSeries.subst u (MvPowerSeries.X ((0 : Fin 1), j))
    rw [MvPowerSeries.subst_X hz, MvPowerSeries.subst_X hu]
    simp [exZero, u]

def J (m k : Fin dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (l Y m))

theorem pderiv_l_zero (m i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) i (l Y m)) = if m = i then 1 else 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add, Nat.cast_zero, Nat.cast_one, one_mul, mul_one]
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) (Finsupp.single i 1))
    (Y.lg m) = _
  rw [Finsupp.mapDomain_single, Y.lg_lin m _ (by simp), MvPowerSeries.coeff_X]
  by_cases hmi : m = i
  · subst hmi; simp
  · rw [if_neg hmi, if_neg]
    intro h
    have := Finsupp.single_left_injective (one_ne_zero) h
    exact hmi (congrArg Prod.snd this).symm

theorem eqA (m i : Fin dd) :
    ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) * J Y m k =
      if m = i then 1 else 0 := by

  have hF := fun w => (ordGE_one_iff (Y.B.G.F w)).2 (Y.B.G.const w)
  have hX := fun (b : Fin 2) (w : Fin dd) =>
    (ordGE_one_iff (MvPowerSeries.X (b, w) : PS C 2 dd)).2 (MvPowerSeries.constantCoeff_X _)
  have hz : MvPowerSeries.HasSubst (exZero Y) := hs (fun q => by
    unfold exZero
    split_ifs
    · exact cc_e Y q.2
    · simp)
  have hsF : MvPowerSeries.HasSubst (fun k => Y.B.G.F k) := hs (fun k => Y.B.G.const k)
  have hsX1 : MvPowerSeries.HasSubst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) :=
    hs (fun k => MvPowerSeries.constantCoeff_X _)
  have h := congrArg (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i)) (l_add Y m)
  rw [map_add (f := _), pderiv_subst hF, pderiv_subst (hX 0), pderiv_subst (hX 1)] at h
  beta_reduce at h
  have s0 : ∑ w : Fin dd, MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), w) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) w (l Y m)) = 0 :=
    Finset.sum_eq_zero (fun w _ => by rw [MvPowerSeries.pderiv_X_of_ne (by simp), zero_mul])
  have s1 : ∑ w : Fin dd, MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), w) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) w (l Y m)) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) i (l Y m)) := by
    rw [Finset.sum_eq_single i (fun w _ hw => by
        rw [MvPowerSeries.pderiv_X_of_ne (by simpa using hw), zero_mul]) (by simp),
      MvPowerSeries.pderiv_X_self, one_mul]
  rw [s0, s1, zero_add] at h
  have h2 := congrArg (MvPowerSeries.subst (exZero Y)) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hz, map_sum] at h2
  simp only [map_mul, MvPowerSeries.coe_substAlgHom] at h2
  rw [MvPowerSeries.subst_comp_subst_apply hsX1 hz] at h2
  simp only [MvPowerSeries.subst_comp_subst_apply hsF hz, F_exZero, MvPowerSeries.subst_X hz] at h2
  have hz1 : (fun s : Fin dd => exZero Y ((1 : Fin 2), s)) = fun _ => 0 := funext fun s => by simp [exZero]
  rw [hz1, subst_zeroPt, pderiv_l_zero] at h2
  refine h2.trans ?_
  split_ifs <;> simp

theorem eqK (n k : Fin dd) :
    ∑ m, J Y m k * MvPowerSeries.pderiv (R := C) m (e Y n) = if n = k then 1 else 0 := by

  have hl := fun w => (ordGE_one_iff (l Y w)).2 (cc_l Y w)
  have hsE : MvPowerSeries.HasSubst (e Y) := hs (cc_e Y)
  have hsL : MvPowerSeries.HasSubst (l Y) := hs (cc_l Y)
  have key : ∀ g, MvPowerSeries.subst (e Y) (MvPowerSeries.subst (l Y) g) = g := fun g => by
    rw [MvPowerSeries.subst_comp_subst_apply hsL hsE]
    simp_rw [lgex Y]
    rw [MvPowerSeries.subst_self]
    rfl
  have h := congrArg (MvPowerSeries.subst (e Y)) (congrArg (MvPowerSeries.pderiv (R := C) k) (exlg Y n))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pderiv_subst hl k, ← MvPowerSeries.coe_substAlgHom hsE, map_sum] at h
  simp only [map_mul, MvPowerSeries.coe_substAlgHom, key] at h
  refine h.trans ?_
  by_cases hnk : n = k
  · subst hnk
    rw [MvPowerSeries.pderiv_X_self, if_pos rfl, ← MvPowerSeries.coe_substAlgHom hsE, map_one]
  · rw [MvPowerSeries.pderiv_X_of_ne hnk, if_neg hnk, ← MvPowerSeries.coe_substAlgHom hsE, map_zero]

end VP

theorem expODE {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : ExpODESt Y := by
  intro i j
  have hFK : Y.B.FK C = Y.B.G.F := by
    funext q
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F q) = _
    simp
  rw [hFK]

  let A : Matrix (Fin dd) (Fin dd) (MvPowerSeries (Fin dd) C) := fun a k =>
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), a) (Y.B.G.F k))
  let Jt : Matrix (Fin dd) (Fin dd) (MvPowerSeries (Fin dd) C) := fun k m => VP.J Y m k
  let D : Matrix (Fin dd) (Fin dd) (MvPowerSeries (Fin dd) C) := fun m n =>
    MvPowerSeries.pderiv (R := C) m (VP.e Y n)
  have hAJ : A * Jt = 1 := by
    refine Matrix.ext fun a m => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (VP.eqA Y m a).trans ?_
    by_cases h : m = a
    · subst h; simp
    · simp [h, Ne.symm h]
  have hJD : Jt * D = 1 := by
    refine Matrix.ext fun k n => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (VP.eqK Y n k).trans ?_
    by_cases h : n = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have hDA : D = A := calc
    D = (A * Jt) * D := by rw [hAJ, Matrix.one_mul]
    _ = A * (Jt * D) := Matrix.mul_assoc A Jt D
    _ = A := by rw [hJD, Matrix.mul_one]
  exact congrFun (congrFun hDA i) j

end Formalism.L2.FormalSeriesBounds

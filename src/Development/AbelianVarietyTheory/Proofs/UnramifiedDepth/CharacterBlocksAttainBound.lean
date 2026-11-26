module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ActionConvergesLadicCauchyAndStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnit
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.CharBlock

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

variable {C : Type} [Field C]

def IsExp {σ : Type} (y : σ → C) (F : MvPowerSeries σ C) : Prop :=
  constantCoeff F = 1 ∧ ∀ w, pderiv w F = y w • F

theorem IsExp.one {σ : Type} : IsExp (fun _ : σ => (0 : C)) 1 := ⟨by simp, fun w => by simp⟩

theorem IsExp.mul {σ : Type} {y y' : σ → C} {F F' : MvPowerSeries σ C} (h : IsExp y F)
    (h' : IsExp y' F') : IsExp (fun w => y w + y' w) (F * F') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], fun w => ?_⟩
  rw [Derivation.leibniz, h.2, h'.2]
  simp only [smul_eq_mul, add_smul, mul_smul_comm]
  rw [add_comm, mul_comm F' F]

theorem IsExp.prod {σ α : Type} (s : Finset α) {y : α → σ → C} {F : α → MvPowerSeries σ C}
    (h : ∀ i, IsExp (y i) (F i)) : IsExp (fun w => ∑ i ∈ s, y i w) (∏ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using IsExp.one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a).mul ih

theorem IsExp.subst {σ τ : Type} [Fintype σ] [Finite τ] {y : σ → C} {F : MvPowerSeries σ C}
    (h : IsExp y F) (e : σ → τ) :
    IsExp (fun t => ∑ j, if e j = t then y j else 0)
      (F.subst fun j => (X (e j) : MvPowerSeries τ C)) := by
  have hs : HasSubst (fun j => (X (e j) : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  constructor
  · have := rename_eq_subst (R := C) (f := e) (p := F)
    have h2 := constantCoeff_rename (R := C) (f := e) F
    rw [this, h.1] at h2
    exact h2
  · intro w
    rw [Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h.2, subst_smul hs]
    by_cases hj : e j = w
    · subst hj; simp
    · simp [hj, pderiv_X_of_ne hj]

theorem IsExp.coeff {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F) :
    ∀ (n : ℕ) (m : σ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod fun s k => y s ^ k := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [Finsupp.degree_eq_zero_iff] at hm
    subst hm
    simp [mfact, h.1]
  | succ n ih =>
    intro m hm
    have hne : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
      refine ⟨m - Finsupp.single w 1, ?_⟩
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      simp at hw; omega
    have hd : m'.degree = n := by
      rw [map_add (f := _), Finsupp.degree_single] at hm; omega
    have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
    rw [coeff_pderiv, coeff_smul] at h1
    have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
      unfold mfact
      have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
      have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
      rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
      simp [Nat.factorial_succ, mul_assoc]
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
      Finsupp.prod_single_index (by simp)]
    push_cast
    linear_combination (mfact m' : C) * h1

theorem IsExp.jet {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F)
    (P : MvPolynomial σ C) : jetAt0 P F = MvPolynomial.eval y P := by
  unfold jetAt0
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, h.coeff _ m rfl]
  rfl

theorem coeff_mvExp {σ : Type} (h : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) := rfl

theorem mvExp_zero {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp, Finset.sum_range_succ']
  simp

theorem isExp_mvExp [CharZero C] {σ : Type} [Fintype σ] (y : σ → C) :
    IsExp y (mvExp (∑ x, y x • (X x : MvPowerSeries σ C))) := by
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mvExp]; simp
  · intro w
    ext m
    have hL : pderiv w (∑ x, y x • (X x : MvPowerSeries σ C)) = MvPowerSeries.C (y w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single w]
      · simp [smul_eq_C_mul]
      · intro b _ hb; simp [pderiv_X_of_ne hb]
      · simp
    rw [coeff_pderiv, coeff_smul, coeff_mvExp, coeff_mvExp, map_add (f := _), Finsupp.degree_single,
      Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
    have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
        ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ 0) = 0 := by
      rw [pow_zero, coeff_one, if_neg]
      intro h
      have := DFunLike.congr_fun h w
      simp at this
    rw [h0, zero_div, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := coeff_pderiv (i := w) ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ (k + 1)) m
    rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := σ) (R := C)),
      coeff_mul_C, coeff_C_mul] at h1
    have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
    push_cast at hk1 ⊢
    field_simp

variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def stdSys {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J) : Sys X where
  tan := fun c => Pi.single c 1
  cur := fun c => X.std c
  curve := fun c => X.std_spec c
  unimod := by
    have : (Matrix.of fun c : I => (Pi.single c 1 : I → C)) = 1 := by
      ext a b
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, AddValuation.map_one]

theorem val_eq [CharZero C] (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (g : Fin 2)
    {n r : ℕ} (hn : n ≤ r) (en : Fin r → I g) (y : Fin n → I g → C) (u : ℕ) :
    ValOf hL (MvPolynomial.rename (fun x : Fin n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin n × WV I))
        (minorK C n r n) ^ u) (fun _ => none)
      (fun ρ => upG g (mvExp (∑ x : I g, y ρ x • (X x : MvPowerSeries (I g) C)))) =
    (Matrix.of fun ρ c : Fin n => y ρ (en (Fin.castLE hn c))).det ^ u := by
  unfold ValOf
  have h0 : ∀ ρ : Fin n, mvExp (rowCopy ρ (0 : MvPowerSeries (WV I) C)) = 1 := by
    intro ρ
    have : rowCopy ρ (0 : MvPowerSeries (WV I) C) = 0 := by
      unfold rowCopy
      have hs : HasSubst (fun w : WV I => (X (ρ, w) : MvPowerSeries (Fin n × WV I) C)) :=
        hasSubst_of_constantCoeff_zero (by simp)
      rw [← coe_substAlgHom hs, map_zero]
    rw [this, mvExp_zero]
  simp only [h0, mul_one]
  have h1 := IsExp.prod Finset.univ fun ρ : Fin n =>
    ((isExp_mvExp (y ρ)).subst fun x : I g => (⟨g, x⟩ : WV I)).subst
      fun w : WV I => ((ρ, w) : Fin n × WV I)
  refine (h1.jet _).trans ?_
  rw [map_pow, MvPolynomial.eval_rename, minorK, dite_eq_left ⟨le_rfl, hn⟩, RingHom.map_det]
  congr 2
  ext ρ c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
    Function.comp_apply, Fin.castLE_refl, Prod.mk.injEq]
  rw [Finset.sum_eq_single ρ, Finset.sum_eq_single (⟨g, en (Fin.castLE hn c)⟩ : WV I),
    Finset.sum_eq_single (en (Fin.castLE hn c))]
  all_goals simp +contextual

theorem core (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (ha : X.big g a) {r : ℕ}
    (hn : X.n ≤ r) (en : Fin r → I g) (hinj : Function.Injective en)
    (hty : ∀ c, (X.G g).ty (Sum.inl (en c)) = a) (u : ℕ) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin X.n → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        (X.Alt → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.n * gam V.l + X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) ∧
        ((∀ a, X.big g a) → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) := by
  haveI := X.charZero
  choose t ht _ using fun g => tExistsUnique (X.G g) (stdSys (X.G g))
  have hint : ∀ (c x : I g), V.Ge 0 ((Pi.single c 1 : I g → C) x) := by
    intro c x
    rw [Pi.single_apply]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  obtain ⟨y, -, hy, h1, h2⟩ := X.CH g a ha (fun c => Pi.single (en (Fin.castLE hn c)) 1)
    ⟨fun c x => hint _ _, fun x c => (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x,
      fun x c => hint _ _, fun c c' => by
        simp [Pi.single_apply, hinj.eq_iff, (Fin.castLE_injective hn).eq_iff, eq_comm]⟩
    (fun c x hx => Pi.single_eq_of_ne (fun h => hx (by rw [h]; exact hty _)) _)
  have key : ∀ b : ℝ, V.v (Matrix.of fun ρ c : Fin X.n =>
        ∑ x, y ρ x * (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x).det ≤ (b : WithTop ℝ) →
      V.v ((Matrix.of fun ρ c : Fin X.n => y ρ (en (Fin.castLE hn c))).det ^ u) ≤
        (((u : ℝ) * b : ℝ) : WithTop ℝ) := by
    intro b hb
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hb
    rw [AddValuation.map_pow, ← nsmul_eq_mul, WithTop.coe_nsmul]
    exact nsmul_le_nsmul_right hb u
  refine ⟨fun g => stdSys (X.G g), t, ht, _, hy _ t ht, fun h => ?_, fun h => ?_⟩
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h1 h)
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h2 h)

theorem chSupply : CHSupply ∧ RF.CHSupply := by
  constructor
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rk g a := by
      unfold RowData.rk; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rkF g a := by
      unfold RowData.rkF; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩

end GlobalTheory.CharBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBoundStatement
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterBlocks_attain_bound : CHSupply ∧ RF.CHSupply := by
  first | exact @GlobalTheory.CharBlock.chSupply | exact GlobalTheory.CharBlock.chSupply | (intros; apply GlobalTheory.CharBlock.chSupply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

variable {C : Type} [Field C]

theorem eq_zero_of_forall_ge (V : VF C) (x : C) (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := (AddValuation.ne_top_iff V.v).2 hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt r
  have := h N
  rw [VF.Ge, ← hr, WithTop.coe_le_coe] at this
  exact absurd hN (not_lt.2 this)

theorem exists_nat_ge_neg (V : VF C) (x : C) : ∃ K : ℕ, V.Ge (-(K : ℝ)) x := by
  by_cases ht : V.v x = ⊤
  · exact ⟨0, by rw [VF.Ge, ht]; exact le_top⟩
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt (-r)
  refine ⟨N, ?_⟩
  rw [VF.Ge, ← hr, WithTop.coe_le_coe]
  linarith

theorem limit_unique (V : VF C) (s : ℕ → C) (x y : C) (hx : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (x - s n))
    (hy : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (y - s n)) : x = y := by
  refine sub_eq_zero.1 (eq_zero_of_forall_ge V _ fun N => ?_)
  obtain ⟨a, ha⟩ := hx N
  obtain ⟨b, hb⟩ := hy N
  have := (ha _ (le_max_left a b)).sub (hb _ (le_max_right a b))
  rwa [sub_sub_sub_cancel_right] at this

theorem linear_limit (V : VF C) {dd : ℕ} (e : Pt C 1 dd) (s : ℕ → Pt C 1 dd)
    (h : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (s n i)))
    (N : ℕ) (v : Fin dd → C) (i : Fin dd) :
    ∃ n0, ∀ n ≥ n0, V.Ge N ((dLin e).mulVec v i - linAct (s n) v i) := by
  choose K hK using fun j => exists_nat_ge_neg V (v j)
  choose m hm using fun j => h (N + K j) i (Finsupp.single ((0 : Fin 1), j) 1)
  refine ⟨Finset.univ.sup m, fun n hn => ?_⟩
  have e1 : (dLin e).mulVec v i - linAct (s n) v i =
      ∑ j, (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e i) -
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (s n i)) * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [e1]
  refine VF.Ge.sum fun j _ => ?_
  have := (hm j n (le_trans (Finset.le_sup (f := m) (Finset.mem_univ j)) hn)).mul (hK j)
  refine this.mono ?_
  push_cast
  linarith

theorem subst_singlePointUncurry {dd : ℕ} {τ : Type} (a : Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  let ι : Fin dd ≃ Fin 1 × Fin dd :=
    { toFun := fun x => (0, x)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl }
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.equivCongrLeft ι)]
  refine finsum_congr fun e => ?_
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain, Finsupp.equivMapDomain_eq_mapDomain]
  rfl

theorem germComp1_eq_subst {dd n : ℕ} (e : Pt C 1 dd) (a : Pt C n dd) (i : Fin dd) :
    comp1 e a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (![a] : Fin 1 → Pt C n dd) q.1 q.2) (e i) = _
  congr 1
  funext ⟨s, x⟩
  obtain rfl : s = 0 := Subsingleton.elim _ _
  rfl

theorem subst_exp_eq_mvExp [CharZero C] {σ : Type} (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (PowerSeries.exp C) = mvExp f := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    by_contra hc
    apply hk
    have hlt : m.degree < k := by simpa using hc
    have : MvPowerSeries.coeff m (f ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)
      exact_mod_cast hlt
    simp [this]

section Chart

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

theorem gp_lg : GP Y.lg := fun i => by
  have := Y.lg_lin i 0 (by simp)
  simpa using this

theorem dLin_lg : dLin Y.lg = 1 := by
  rw [← germLinearPart_coordinatePoint_zero]
  ext i j
  exact Y.lg_lin i _ (by simp)

theorem eq_exp_lin_log (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1))) :
    e = comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap (dLin e)) Y.lg) := by
  have h0 := gp_lg Y
  have hF := Y.B.G.const
  have hi : IsInvPair Y.lg Y.ex := ⟨h0, Y.ex_const, Y.lg_ex, Y.ex_lg⟩
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have hl : comp1 Y.lg (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      comp1 Y.lg (pt C (n := 2) dd 0) + comp1 Y.lg (pt C (n := 2) dd 1) := funext Y.lg_add
  have e1 := additive_eq_lin _ hF Y.lg Y.ex (comp1 Y.lg e) (dLin_lg Y) hl hi (gp_comp1 _ _ h0 he) (by
    rw [gt_comp1_comp1 _ _ he _ (gp_addOf _ hF _ _ p0 p1), hhom,
      additive_at _ hF _ hl _ _ (gp_comp1 _ _ he p0) (gp_comp1 _ _ he p1),
      gt_comp1_comp1 _ _ he _ p0, gt_comp1_comp1 _ _ he _ p1])
  rw [dLin_comp _ _ he, dLin_lg, one_mul] at e1
  rw [← e1, gt_comp_inv' hi _ he]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

omit [CharZero C] in
theorem subst_linMap (M : Matrix (Fin dd) (Fin dd) C) (L : Pt C 1 dd) (h0 : GP L)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (x : Fin dd) :
    ∑ y, M x y • MvPowerSeries.subst a (un1 (L y)) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 (LogExpAdaptedGauge.linMap M) L x) := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [germComp_matrixLinearMap_apply _ _ h0, ← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [subst_singlePointUncurry a ha, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_smul hs]

theorem matrixEnd_linearMap (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP (Y.raw p) M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := rfl
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

theorem matrixEnd_eq_subst (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap Y p _ a ha, ← eq_exp_lin_log Y e he hhom]

theorem matrixEnd_eq_comp (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP (Y.raw p) (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst Y p e he hhom a ha, germComp1_eq_subst]

theorem hAt_eq_ev {n : ℕ} (a b : Pt C n dd) : hAt (Y.raw p) a b = ev ![a, b] Y.h := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

theorem isEnd_of_hom (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd (Y.raw p) V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst Y p e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst Y p e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp Y p e he hhom _ (gp_pt 0), matrixEnd_eq_comp Y p e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev, hAt_eq_ev, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d _ I _ p a ha
  obtain ⟨c1, c2⟩ := GlobalTheory.T.actionConverges_ladic_cauchy_and_star C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom Y p fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom Y p f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimitStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  first | exact @GlobalTheory.ActionLimit.exists_isEnd_of_limit | exact GlobalTheory.ActionLimit.exists_isEnd_of_limit | (intros; apply GlobalTheory.ActionLimit.exists_isEnd_of_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem fibreDescent_transport {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m')
    (P : (X ⟶ X) → Prop)
    (H : ∀ (V : X.Opens) (a : Γ(X, m' ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m' ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m' ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m'.app V).hom a' = a) :
    ∀ (V : X.Opens) (a : Γ(X, m ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m.app V).hom a' = a := by
  subst e; exact H

theorem torsion_invariant_descends_fibre :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V)),
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V), ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) →
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a) := by
  intro S G _ _ K _ _ f N hN hsm hfin _ hsurj V a ha
  let A : Over (Spec (CommRingCat.of K)) := (Over.pullback f).obj G
  let ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t),
      (T ⟶ A) ≃* (Over.mk t ⟶ G) := fun T t ht => TorsionLift.ptsEquiv f G T t ht
  have hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f :=
    fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x
  have hA : A.hom ≫ f = (G ⊗ Over.mk f).hom := Limits.pullback.condition.symm
  have hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f) := Over.OverMorphism.ext (by
    rw [hρ]; exact Category.id_comp _)
  have ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f),
      v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left := by
    intro u v h1 h2
    apply Limits.pullback.hom_ext
    · exact (congrArg (·.left) h1).trans (hρ _ _ _ _)
    · exact (congrArg (·.left) h2).trans (Over.w u).symm
  have hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left := by
    refine ext _ _ ?_ (whiskerRight_snd _ _)
    rw [map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have hpb : IsPullback (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left (Limits.pullback.fst G.hom f)
      (Limits.pullback.fst G.hom f) ((𝟙 G) ^ N : G ⟶ G).left := by
    refine IsPullback.of_right (h₁₂ := Limits.pullback.snd G.hom f) (v₁₃ := f) (h₂₂ := G.hom) ?_ ?_
      (IsPullback.of_hasPullback G.hom f).flip
    · rw [Over.w]
      have : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ Limits.pullback.snd G.hom f =
        Limits.pullback.snd G.hom f := congrArg (·.left) (whiskerRight_snd ((𝟙 G) ^ N) (Over.mk f))
      rw [this]
      exact (IsPullback.of_hasPullback G.hom f).flip
    · exact congrArg (·.left) (whiskerRight_fst ((𝟙 G) ^ N) (Over.mk f))
  have hsmA : Smooth A.hom := inferInstanceAs (Smooth (Limits.pullback.snd G.hom f))
  have h1 : Etale ((𝟙 A) ^ N : A ⟶ A).left := GrpTangent.etale_id_pow A (by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have h2 : Surjective ((𝟙 A) ^ N : A ⟶ A).left :=
    hm ▸ MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have h3 : IsFinite ((𝟙 A) ^ N : A ⟶ A).left :=
    hm ▸ MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip hfin
  refine fibreDescent_transport hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧
    t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_
  · intro V a ha
    refine existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_
    refine ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩
    refine (ext _ _ ?_ (lift_snd _ _)).symm
    rw [lift_fst, map_mul, hid, _root_.mul_comm]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]
    rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ha y hy

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacter
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ResidueChar

theorem exists_pow_of_finite_field {K k : Type} [Field K] [Finite K] [CommRing k] [IsDomain k]
    (l : ℕ) [Fact l.Prime] [CharP K l] (f g : K →+* k) :
    ∃ j : ℕ, ∀ y, g y = f y ^ l ^ j := by
  classical
  have := Fintype.ofFinite K
  have hmem : ∀ y, g y ∈ f.range := fun y => by
    have h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) =
        ∏ a : K, (Polynomial.X - Polynomial.C a) := by
      have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
        Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
      have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [FiniteField.roots_X_pow_card_sub_X,
          Polynomial.natDegree_X_pow_sub_X (R := K) Fintype.one_lt_card]
        rfl)
      rw [← this, FiniteField.roots_X_pow_card_sub_X]
      rfl
    have h2 := congrArg (Polynomial.eval₂RingHom f (g y)) h1
    rw [map_prod] at h2
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    rw [← map_pow, FiniteField.pow_card, sub_self] at h2
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h2.symm
    exact ⟨a, (sub_eq_zero.1 ha).symm⟩
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let s : K →+* K := e.symm.toRingHom.comp (g.codRestrict f.range hmem)
  have hs : ∀ y, f (s y) = g y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))
  let := ZMod.algebra K l
  let s' : K →ₐ[ZMod l] K := { s with
    commutes' := fun r => DFunLike.congr_fun
      (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'
  refine ⟨j, fun y => ?_⟩
  have : s y = y ^ l ^ (j : ℕ) := by
    have h := DFunLike.congr_fun hj y
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  rw [← hs, this, map_pow]

theorem exists_eq_of_ker_le {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) [Fact l.Prime] [CharP k l] (φ : ZMod d → (O →+* k))
    (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (g : O →+* k) (hg : ∀ x, φ 0 x = 0 → g x = 0) :
    ∃ a, ∀ x, g x = φ a x := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← TeichSeq.frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  have : Finite (φ 0).range := hfin
  let : Field (φ 0).range := (Finite.isField_of_domain _).toField
  let g' : (φ 0).range →+* k :=
    (φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective
      ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩
  have hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨j, hj⟩ := exists_pow_of_finite_field l (φ 0).range.subtype g'
  refine ⟨0 + (j : ZMod d), fun x => ?_⟩
  rw [TeichSeq.frob_iter l φ h, ← hg', hj]
  rfl


open TeichSeq in
theorem main : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  intro C _ V O _ d _ em hint hfrob ψ hψ hker
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  let p : O →+* intRing V := ψ.codRestrict (intRing V) hψ
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hπ0 : ∀ u : intRing V, π u = 0 ↔ V.MM (u : C) := fun u => Ideal.Quotient.eq_zero_iff_mem
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have : CharP (intRing V ⧸ maxId V) V.l := by
    refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
    rw [← map_natCast π, hπ0]
    simpa using mm_of_ge_one V VF.ge_l
  obtain ⟨a, ha⟩ := exists_eq_of_ker_le V.l φ hφ (π.comp p) (fun x hx => by
    refine (hπ0 (p x)).2 (hker x fun a => (hπ0 (e a x)).1 ?_)
    have := frob_iter V.l φ hφ 0 x a.val
    rw [hx, zero_pow (pow_ne_zero _ V.l_prime.ne_zero)] at this
    show φ a x = 0
    simpa using this)
  exact ⟨a, fun x => (hπ (p x) (e a x)).1 (ha x)⟩

end GlobalTheory.ResidueChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacterStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_congr_integral_character : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  first | exact @GlobalTheory.ResidueChar.main | exact GlobalTheory.ResidueChar.main | (intros; apply GlobalTheory.ResidueChar.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairData
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairData
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLawPair

variable {C : Type} [Field C] {dd : ℕ} {τ : Type}

theorem subst_oneVarGerm_eq_substPointsPowerSeries {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (f : PS C 1 dd) :
    subst a (un1 f) = sb ![a] f := by
  rw [RowLawSquare.subst_singlePointUncurry ha]
  unfold sb
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem oneVarGerm_eq_substPoints_X (f : PS C 1 dd) : un1 f = sb ![(X : Fin dd → MvPowerSeries (Fin dd) C)] f := by
  rw [← subst_oneVarGerm_eq_substPointsPowerSeries (fun _ => constantCoeff_X _), subst_self]
  rfl

theorem zc_gp {n : ℕ} (j : Fin n) : Zc (gp C (Fin dd) j) := fun _ => constantCoeff_X _

theorem intS_gp (V : VF C) {n : ℕ} (j : Fin n) (i : Fin dd) : IntS V (gp C (Fin dd) j i) := intS_X V _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

theorem formalAdd_eq_law {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    addP (Y.raw p) a b = law Y a b := by
  funext i
  show subst (fun x => subst a (un1 (Y.lg x)) + subst b (un1 (Y.lg x))) (un1 (Y.ex i)) = _
  simp only [subst_oneVarGerm_eq_substPointsPowerSeries ha, subst_oneVarGerm_eq_substPointsPowerSeries hb, lg_law Y ha hb]
  rw [subst_oneVarGerm_eq_substPointsPowerSeries (fun x => cc_sb (zc1 (zc_law Y ha hb)) (zc_lg Y x)), ex_lg Y (zc_law Y ha hb)]

theorem hAt_eq_sb (a b : Fin dd → MvPowerSeries τ C) : hAt (Y.raw p) a b = sb ![a, b] Y.h := by
  show subst _ Y.h = subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

theorem cc_sb_h {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    constantCoeff (sb ![a, b] Y.h) = 0 :=
  cc_sb (zc2 ha hb) (cc_h Y)

theorem sb_gp_self (f : PS C 2 dd) : sb ![gp C (Fin dd) (0 : Fin 2), gp C (Fin dd) 1] f = f := by
  have e : (fun q : Fin 2 × Fin dd => ![gp C (Fin dd) (0 : Fin 2), gp C (Fin dd) 1] q.1 q.2) = X := by
    funext ⟨s, x⟩
    fin_cases s <;> rfl
  unfold sb
  rw [e, subst_self]
  rfl

theorem rLaw_raw : RLaw (Y.raw p) V := {
  charZero := inferInstance
  closed := Y.algClosed
  odd := Y.l_odd
  lin := fun i μ hμ => by
    classical
    show coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
    rw [Y.lg_lin i _ (by rwa [Finsupp.degree_mapDomain]), coeff_X, coeff_X]
    have hinj : Function.Injective fun x : Fin dd => ((0 : Fin 1), x) := fun _ _ h => congrArg Prod.snd h
    refine if_congr ?_ rfl rfl
    rw [← (Finsupp.mapDomain_injective (M := ℕ) hinj).eq_iff (a := μ), Finsupp.mapDomain_single]
  exc := fun i => (constantCoeff_uncurry _).trans (Y.ex_const i)
  lgex := fun i => by
    show subst (fun x => un1 (Y.ex x)) (un1 (Y.lg i)) = _
    rw [subst_oneVarGerm_eq_substPointsPowerSeries (fun x => (constantCoeff_uncurry _).trans (Y.ex_const x))]
    simp only [oneVarGerm_eq_substPoints_X]
    exact lg_ex Y (fun _ => constantCoeff_X _) i
  exlg := fun i => by
    show subst (fun x => un1 (Y.lg x)) (un1 (Y.ex i)) = _
    rw [subst_oneVarGerm_eq_substPointsPowerSeries (fun x => (constantCoeff_uncurry _).trans (zc_lg Y x))]
    simp only [oneVarGerm_eq_substPoints_X]
    exact ex_lg Y (fun _ => constantCoeff_X _) i
  axes := h_axes Y
  addInt := fun i => by
    rw [formalAdd_eq_law Y p (zc_gp 0) (zc_gp 1), law, sb_gp_self]
    exact Y.intF i
  ph1 := by
    rw [formalAdd_eq_law Y p (zc_gp 0) (zc_gp 1), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, mvExp_eq (by
      rw [map_sub, map_add (f := _), cc_sb_h Y (zc_gp _) (zc_gp _), cc_sb_h Y (zc_gp _) (zc_gp _),
        cc_sb_h Y (zc_law Y (zc_gp _) (zc_gp _)) (zc_gp _)]
      simp), exp_gauge_cocycle_first_variable Y (zc_gp _) (zc_gp _) (zc_gp _)]
    refine intS_sb V (zc3 (zc_gp _) (zc_gp _) (zc_gp _)) (fun j i => ?_) Y.intPh1
    fin_cases j <;> exact intS_gp V _ i
  ph2 := by
    rw [formalAdd_eq_law Y p (zc_gp 1) (zc_gp 2), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, mvExp_eq (by
      rw [map_sub, map_add (f := _), cc_sb_h Y (zc_gp _) (zc_gp _), cc_sb_h Y (zc_gp _) (zc_gp _),
        cc_sb_h Y (zc_gp _) (zc_law Y (zc_gp _) (zc_gp _))]
      simp), exp_gauge_cocycle_second_variable Y (zc_gp _) (zc_gp _) (zc_gp _)]
    refine intS_sb V (zc3 (zc_gp _) (zc_gp _) (zc_gp _)) (fun j i => ?_) Y.intPh2
    fin_cases j <;> exact intS_gp V _ i
  sy := by
    have e : (Y.raw p).h = sb ![gp C (Fin dd) (0 : Fin 2), gp C (Fin dd) 1] Y.h := (sb_gp_self Y.h).symm
    rw [hAt_eq_sb, e, mvExp_eq (by
      rw [map_sub, cc_sb_h Y (zc_gp _) (zc_gp _), cc_sb_h Y (zc_gp _) (zc_gp _), sub_zero]),
      exp_sy Y (zc_gp _) (zc_gp _), sb_gp_self]
    exact Y.intSy
  kunit := Y.k_unit
  uint := p.u_int
  sat := fun g => by
    obtain ⟨w, hw, h⟩ := p.u_sat g
    exact ⟨w, hw, fun c c' => ⟨fun e => (h c c').trans (ite_eq_left e),
      fun e => (h c c').trans (ite_eq_right e)⟩⟩ }

theorem rLaw_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    RLaw (Y.raw p) V :=
  fun _ _ _ _ _ _ _ _ Y _ _ _ _ p => rLaw_raw Y p

end GlobalTheory.RowLawPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), RLaw (Y.raw p) V := by
  first | exact @GlobalTheory.RowLawPair.rLaw_pairData | exact GlobalTheory.RowLawPair.rLaw_pairData | (intros; apply GlobalTheory.RowLawPair.rLaw_pairData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem intGerm_indep_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V →
    ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H := by
  intro C _ V d _ I _ κ _ X hX H S S₂ t t₂ ht ht₂
  rw [GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d I κ X hX H S t ht, GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d I κ X hX H S₂ t₂ ht₂]

end GlobalTheory.RowLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystemStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGerms_independent_of_curveSystem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H := by
  first | exact @GlobalTheory.RowLaw.intGerm_indep_of_rlaw | exact GlobalTheory.RowLaw.intGerm_indep_of_rlaw | (intros; apply GlobalTheory.RowLaw.intGerm_indep_of_rlaw <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntProdRename
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.CharBound

noncomputable section

variable {C : Type} [Field C]

theorem isIntV_add' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)

theorem isIntV_mul' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x * y) := by
  unfold IsIntV at *
  rw [v.map_mul]
  exact add_nonneg hx hy

theorem isIntV_zero' {v : AddValuation C (WithTop ℝ)} : IsIntV v 0 := by
  unfold IsIntV; rw [v.map_zero]; exact le_top

theorem isIntV_one' {v : AddValuation C (WithTop ℝ)} : IsIntV v 1 := by
  unfold IsIntV; rw [v.map_one]

theorem mvIsInt_mul' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F G : MvPowerSeries σ C}
    (hF : MvIsInt v F) (hG : MvIsInt v G) : MvIsInt v (F * G) := by
  classical
  intro α
  rw [coeff_mul]
  exact Finset.sum_induction _ (IsIntV v) (fun _ _ => isIntV_add') isIntV_zero'
    fun p _ => isIntV_mul' (hF _) (hG _)

theorem mvIsInt_one' {v : AddValuation C (WithTop ℝ)} {σ : Type} : MvIsInt v (1 : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_one]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_X' {v : AddValuation C (WithTop ℝ)} {σ : Type} (s : σ) :
    MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_X]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_pow' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F : MvPowerSeries σ C}
    (hF : MvIsInt v F) (n : ℕ) : MvIsInt v (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact mvIsInt_one'
  | succ n ih => rw [pow_succ]; exact mvIsInt_mul' ih hF

theorem mvIsInt_subst' {v : AddValuation C (WithTop ℝ)} {σ τ : Type} {a : σ → MvPowerSeries τ C}
    (ha : HasSubst a) (hai : ∀ s, MvIsInt v (a s)) {F : MvPowerSeries σ C} (hF : MvIsInt v F) :
    MvIsInt v (subst a F) := by
  intro β
  rw [coeff_subst ha]
  refine finsum_induction (IsIntV v) isIntV_zero' (fun _ _ => isIntV_add') fun e => ?_
  rw [smul_eq_mul]
  refine isIntV_mul' (hF e) ?_
  exact Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    (fun s _ => mvIsInt_pow' (hai s) _) β

theorem isInt_prod_rename (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (χ : Fin i → MvPowerSeries (Fin d) C) (h : ∀ b, MvIsInt v (χ b)) :
    MvIsInt v (∏ b, subst (fun e : Fin d =>
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) :=
  Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    fun b _ => mvIsInt_subst' (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => mvIsInt_X' _) (h b)

variable [CharZero C]

theorem coeff_mvExp_lin {σ : Type} [Fintype σ] (c : σ → C) (α : σ →₀ ℕ) :
    coeff α (Formalism.L2.Th1.C.mvExp (∑ s, c s • (X s : MvPowerSeries σ C))) =
      α.prod fun s n => c s ^ n / (n.factorial : C) := by
  classical
  set L : MvPowerSeries σ C := ∑ s, c s • (X s : MvPowerSeries σ C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  let g : MvPowerSeries σ C := fun β => β.prod fun s n => c s ^ n / (n.factorial : C)
  have hg : ∀ β, coeff β g = ∏ s, c s ^ β s / ((β s).factorial : C) := fun β => by
    show (β.prod fun s n => c s ^ n / (n.factorial : C)) = _
    exact Finsupp.prod_fintype _ _ (fun s => by simp)
  have hpL : ∀ i, pderiv i L = c i • (1 : MvPowerSeries σ C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have hpg : ∀ i, pderiv i g = c i • g := fun i => by
    ext β
    rw [coeff_pderiv, hg, coeff_smul, hg, Fintype.prod_eq_mul_prod_compl i,
      Fintype.prod_eq_mul_prod_compl i (fun s => c s ^ β s / ((β s).factorial : C))]
    have hrest : ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ (β + Finsupp.single i 1 : σ →₀ ℕ) s /
        (((β + Finsupp.single i 1 : σ →₀ ℕ) s).factorial : C) =
        ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ β s / ((β s).factorial : C) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' : s ≠ i := by simpa using hs
      simp [Finsupp.single_apply, Ne.symm hs']
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorial_succ]
    have h0 : ((β i).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h1 : ((β i : C) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    push_cast
    field_simp
    ring
  have hcg : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hg]
    simp
  have key : g * Formalism.L2.Th1.C.mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, Formalism.L2.Th1.C.pderiv_mvExp hnL, map_neg, hpL, hpg, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, hcg, Formalism.L2.Th1.C.constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : Formalism.L2.Th1.C.mvExp L = g := by
    calc Formalism.L2.Th1.C.mvExp L = (g * Formalism.L2.Th1.C.mvExp (-L)) * Formalism.L2.Th1.C.mvExp L := by
          rw [key, one_mul]
      _ = g := by rw [mul_assoc, Formalism.L2.Th1.C.mvExp_neg hL, mul_one]
  rw [hE]
  rfl

theorem derivAt0_eq_eval {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) (w : σ → C)
    (hg : ∀ α, coeff α g = α.prod fun s n => w s ^ n / (n.factorial : C)) :
    derivAt0 P g = MvPolynomial.eval w P := by
  rw [MvPolynomial.eval_eq, derivAt0]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hg, mfact, mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  have : (((α s).factorial : ℕ) : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem eval_detPow (i c : ℕ) (H : Matrix (Fin i) (Fin i) C) :
    MvPolynomial.eval (fun x : (Σ _ : Fin i, Fin i) => H x.2 x.1) (detPow C i c) = H.det ^ c := by
  rw [detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]


open Formalism.L2.Th1.C in
theorem subst_col (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C)
    (b : Fin i) (w : Fin d → C) (χ : MvPowerSeries (Fin d) C)
    (hχ : ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => w e ^ n / (n.factorial : C)) :
    subst (expAlong (fun _ : Fin i => G) (fun _ => u))
        (subst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) χ) =
      mvExp (∑ e, w e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
  have hexp := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G).1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hexp.1
  have hL : ∀ b' : Fin i, HasSubst (fun e : Fin d => ∑ a, u a e • (X (⟨b', a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
    fun b' => hasSubst_of_constantCoeff_zero fun e => by simp
  have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero (hL x.1) (fun e => by simp) (hexp.1 x.2)
  have hR : HasSubst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun e => by simp
  have h1 : subst (expOf G) χ = mvExp (∑ e, w e • (X e : MvPowerSeries (Fin d) C)) := by
    ext α; rw [hχ, coeff_mvExp_lin]
  rw [subst_comp_subst_apply hR hEA]
  have h2 : (fun e : Fin d => subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) =
      fun e => subst (fun e : Fin d => ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (expOf G e) := by
    funext e; rw [subst_X hEA]; rfl
  rw [h2, ← subst_comp_subst_apply hE (hL b), h1, mvSubst_mvExp (by simp) (hL b)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom (hL b), map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, coe_substAlgHom, subst_X (hL b)]

theorem lin_sum {i d : ℕ} (l : Fin i → Fin d → C) (u : Fin i → Fin d → C) :
    (∑ b, ∑ e, l b e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
      ∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_smul]

theorem detDepth_le_char : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (l : Fin i → Fin d → C), (∀ b, IsCharLog G (l b)) →
    detDepth G u c ≤ toE (v ((Matrix.det (Matrix.of fun a b => ∑ e, l b e * u a e)) ^ c)) := by
  intro C _ _ v i d c G u l hl
  choose χ hχi hχc using hl
  have hf := isInt_prod_rename v i d χ hχi
  have key : subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (∏ b, subst (fun e : Fin d =>
        (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) =
      Formalism.L2.Th1.C.mvExp (∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
    have hexp := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G).1
    have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
      hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun e => by simp) (fun e => by simp) (hexp.1 x.2)
    rw [← coe_substAlgHom hEA, map_prod, ← lin_sum, Formalism.L2.Th1.C.mvExp_sum _ _ (fun b _ => by simp)]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_substAlgHom, subst_col v G u b (l b) (χ b) (hχc b)]
  unfold detDepth depth
  refine le_trans (iInf_le _ ⟨_, hf⟩) (le_of_eq ?_)
  dsimp only
  rw [key, derivAt0_eq_eval _ _ (fun x : (Σ _ : Fin i, Fin i) => (Matrix.of fun a b => ∑ e, l b e * u a e) x.2 x.1)
    (fun α => by rw [coeff_mvExp_lin]; rfl), eval_detPow]

end

end GlobalTheory.FGDepth.CharBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithm
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharLogOfChar

section Series

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.FormalCalc

variable {C : Type} [Field C]

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem subst_zero_fun {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro D hD
    obtain ⟨s, hs'⟩ := Finsupp.support_nonempty_iff.mpr hD
    rw [Finsupp.prod, Finset.prod_eq_zero hs' (zero_pow (Finsupp.mem_support_iff.mp hs'))]
    simp

theorem coeff_single_subst {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : τ) :
    coeff (Finsupp.single i 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (a s) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← cc_pderiv, pderiv_subst hs, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, constantCoeff_subst_of_zero hs ha, cc_pderiv, cc_pderiv]
  rfl

variable {d : ℕ}

theorem pderiv_of_mul (g : MvPowerSeries (Fin d) C)
    (h : subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g =
      subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g) (i : Fin d) :
    pderiv i g = coeff (Finsupp.single i 1) g • g := by
  classical
  have hS : HasSubst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hL : HasSubst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  let Z : Fin d ⊕ Fin d → MvPowerSeries (Fin d) C := Sum.elim X fun _ => 0
  have hZ : HasSubst Z := hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [Z]
  have hd := congrArg (fun f => subst Z (pderiv (Sum.inr i) f)) h
  simp only [Derivation.leibniz, pderiv_subst hS, pderiv_subst hL, pderiv_subst hR, map_add (f := _), pderiv_X,
    Pi.single_apply, reduceCtorEq, if_false, Sum.inr.injEq, zero_add, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, smul_zero, add_zero,
    smul_eq_mul] at hd
  rw [subst_mul hZ, subst_comp_subst_apply hS hZ, subst_comp_subst_apply hL hZ,
    subst_comp_subst_apply hR hZ] at hd
  simp only [subst_add hZ, subst_X hZ, Z, Sum.elim_inl, Sum.elim_inr, add_zero] at hd
  rw [subst_zero_fun, cc_pderiv] at hd
  have e : (fun s : Fin d => (X s : MvPowerSeries (Fin d) C)) = X := rfl
  rw [e, subst_self] at hd
  rw [show pderiv i g = id (pderiv i g) from rfl, hd, id, mul_comm, smul_eq_C_mul]

variable [CharZero C]


open Formalism.L2.Th1.C in
theorem coeff_of_pderiv (g : MvPowerSeries (Fin d) C) (c : Fin d → C) (h0 : constantCoeff g = 1)
    (h : ∀ i, pderiv i g = c i • g) (α : Fin d →₀ ℕ) :
    coeff α g = α.prod fun e n => c e ^ n / (n.factorial : C) := by
  classical
  rw [← CharBound.coeff_mvExp_lin]
  set L : MvPowerSeries (Fin d) C := ∑ s, c s • (X s : MvPowerSeries (Fin d) C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  have hpL : ∀ i, pderiv i L = c i • (1 : MvPowerSeries (Fin d) C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have key : g * mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, pderiv_mvExp hnL, map_neg, hpL, h, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, h0, constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : mvExp L = g := by
    calc mvExp L = (g * mvExp (-L)) * mvExp L := by rw [key, one_mul]
      _ = g := by rw [mul_assoc, mvExp_neg hL, mul_one]
  rw [hE]

variable {v : AddValuation C (WithTop ℝ)}

theorem coeff_single_expOf (G : LogFGL v d) (a i : Fin d) :
    coeff (Finsupp.single i 1) (expOf G a) = if a = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single i 1)) ((expOf_twoSided_unique C v d G).2.1 a)
  rw [coeff_single_subst G.lg_const] at h
  simp only [G.lg_lin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, ← cc_pderiv, pderiv_X, Pi.single_apply]
  split_ifs <;> simp

theorem mul_of_char (G : LogFGL v d) (χ : MvPowerSeries (Fin d) C)
    (h : subst G.F χ = subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ) :
    subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C))
        (subst (expOf G) χ) =
      subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) χ) *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) χ) := by
  obtain ⟨⟨hE0, hE1⟩, hE2, -⟩ := expOf_twoSided_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  have hS : HasSubst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hL : HasSubst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  let P : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) C :=
    Sum.elim (fun b => subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b))
      (fun b => subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b))
  have hP0 : ∀ s, constantCoeff (P s) = 0 := fun s => by
    cases s with
    | inl b => exact constantCoeff_subst_eq_zero hL (fun _ => by simp) (hE0 b)
    | inr b => exact constantCoeff_subst_eq_zero hR (fun _ => by simp) (hE0 b)
  have hP : HasSubst P := hasSubst_of_constantCoeff_zero hP0
  have eL : ∀ f : MvPowerSeries (Fin d) C,
      subst P (subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) f) =
        subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) f) := by
    intro f
    rw [subst_comp_subst_apply hL hP, subst_comp_subst_apply hE hL]
    simp only [subst_X hP, P, Sum.elim_inl]
  have eR : ∀ f : MvPowerSeries (Fin d) C,
      subst P (subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) f) =
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) f) := by
    intro f
    rw [subst_comp_subst_apply hR hP, subst_comp_subst_apply hE hR]
    simp only [subst_X hP, P, Sum.elim_inr]
  have hQ : HasSubst (fun a => (subst P (G.F a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero hP hP0 (G.F_const a)
  have e1 : (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
      fun a => subst (fun b => (subst P (G.F b) : MvPowerSeries (Fin d ⊕ Fin d) C)) (G.lg a) := by
    funext a
    rw [← subst_comp_subst_apply hF hP, G.lg_F, subst_add hP, eL, eR, hE1, subst_X hL, subst_X hR]
  have e2 : (fun b => (subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) :
      MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
      fun b => subst P (G.F b) := by
    funext b
    rw [e1, ← subst_comp_subst_apply hlg hQ, hE2, subst_X hQ]
  rw [subst_comp_subst_apply hE hS, e2, ← subst_comp_subst_apply hF hP, h, subst_mul hP, eL, eR]

theorem isCharLog_of_char (G : LogFGL v d) (χ : MvPowerSeries (Fin d) C) (hi : MvIsInt v χ)
    (h0 : constantCoeff χ = 1)
    (h : subst G.F χ = subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ) :
    IsCharLog G fun j => coeff (Finsupp.single j 1) χ := by
  classical
  have hE0 := (expOf_twoSided_unique C v d G).1.1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  refine ⟨χ, hi, coeff_of_pderiv _ _ ?_ fun i => ?_⟩
  · rw [constantCoeff_subst_of_zero hE hE0, h0, map_one]
  · rw [pderiv_of_mul _ (mul_of_char G χ h), coeff_single_subst hE0]
    simp [coeff_single_expOf]

end Series

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem isCharLog_dl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ χ : PS X.O 1 (chD Ch.ch), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) χ → IsCharLog (fgl Ch X) (fun j => algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl χ j)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X χ hχ
  obtain ⟨h0, hm⟩ := hχ
  set φ := algebraMap X.O X.C with hφ
  have hj : φ.comp X.ι = jX X := RingHom.ext fun r => (X.comp r).symm
  have hFe : ∀ i, MvPowerSeries.map φ (MvPowerSeries.map X.ι (Ch.FT i)) = (lawX Ch X).F i := fun i => by
    rw [lawX_F, ← hj, MvPowerSeries.map_comp]; rfl
  have hinj : Function.Injective φ := X.ints.hom_inj
  have hF0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map X.ι (Ch.FT i)) = 0 := fun i => hinj (by
    have h := (lawX Ch X).const i
    rw [← hFe, MvPowerSeries.constantCoeff_map] at h
    rw [h, map_zero])
  have hadd : addOf (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (pt X.O (n := 2) _ 0) (pt X.O (n := 2) _ 1) =
      fun i => MvPowerSeries.map X.ι (Ch.FT i) := by
    funext i
    have e : (fun q : Fin 2 × Fin (chD Ch.ch) =>
        (![pt X.O (n := 2) _ 0, pt X.O _ 1] : Fin 2 → Pt X.O 2 _) q.1 q.2) = MvPowerSeries.X := by
      funext q
      obtain ⟨j, i⟩ := q
      fin_cases j <;> rfl
    unfold addOf ev
    rw [e, MvPowerSeries.subst_self]
    rfl
  have hmap : ∀ a : Pt X.O 2 (chD Ch.ch), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      MvPowerSeries.map φ (ev ![a] χ) = ev ![fun i => MvPowerSeries.map φ (a i)] (MvPowerSeries.map φ χ) := by
    intro a ha
    unfold ev
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨j, i⟩ := q
      fin_cases j; exact ha i)]
    congr 1
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j; rfl
  have hp : ∀ (k : Type) [CommRing k] (j : Fin 2) i,
      MvPowerSeries.constantCoeff (pt k (n := 2) (chD Ch.ch) j i) = 0 := fun k _ j i => by simp [pt]
  have hpm : ∀ j : Fin 2, (fun i => MvPowerSeries.map φ (pt X.O (n := 2) (chD Ch.ch) j i)) = pt X.C _ j :=
    fun j => funext fun i => by simp [pt]
  have hm' := congrArg (MvPowerSeries.map φ) hm
  rw [hadd, map_mul, hmap _ hF0, hmap _ (hp _ 0), hmap _ (hp _ 1), hpm, hpm, funext hFe] at hm'
  have key := isCharLog_of_char (fgl Ch X)
    (MvPowerSeries.subst (GlobalTheory.LawLog.oneVar X.C _) (MvPowerSeries.map φ χ)) ?_ ?_ ?_
  · simp only [GlobalTheory.LawLog.coeff_single_oneVar, MvPowerSeries.coeff_map] at key
    exact key
  · refine CharBound.mvIsInt_subst' GlobalTheory.LawLog.hs_oneVar (fun q => CharBound.mvIsInt_X' _) fun α => ?_
    rw [MvPowerSeries.coeff_map, isIntV_iff]
    exact X.ints.map_le_one _
  · rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero GlobalTheory.LawLog.hs_oneVar GlobalTheory.LawLog.cc_oneVar]
    simp [h0]
  · have e0 : (fun b => (MvPowerSeries.X (Sum.inl b) : MvPowerSeries (Fin (chD Ch.ch) ⊕ Fin (chD Ch.ch)) X.C)) =
        fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) (pt X.C (n := 2) _ 0 i) := by
      funext i; rw [pt, MvPowerSeries.subst_X GlobalTheory.LawLog.hs_twoVars]; simp [GlobalTheory.LawLog.twoVars]
    have e1 : (fun b => (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (Fin (chD Ch.ch) ⊕ Fin (chD Ch.ch)) X.C)) =
        fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) (pt X.C (n := 2) _ 1 i) := by
      funext i; rw [pt, MvPowerSeries.subst_X GlobalTheory.LawLog.hs_twoVars]; simp [GlobalTheory.LawLog.twoVars]
    have eF : (fgl Ch X).F = fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) ((lawX Ch X).F i) := rfl
    rw [e0, e1, eF, GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (lawX Ch X).const,
      GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (hp _ 0),
      GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (hp _ 1), ← MvPowerSeries.subst_mul GlobalTheory.LawLog.hs_twoVars, hm']

end GlobalTheory.CharLogOfChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithmStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_character_is_logarithm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ χ : PS X.O 1 (chD Ch.ch), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) χ → IsCharLog (fgl Ch X) (fun j => algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl χ j)) := by
  first | exact @GlobalTheory.CharLogOfChar.isCharLog_dl | exact GlobalTheory.CharLogOfChar.isCharLog_dl | (intros; apply GlobalTheory.CharLogOfChar.isCharLog_dl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColength
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (pairDet hasChars_iff)

theorem hasChars_frame_of_hasAF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ (f : Lt1 Dw) (xs : NNReal) (r : ℝ), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult f.1)) j => X.ι (Ch.uvecT ⟨f.1, i⟩ j)) xs → (X.v (p : X.C) : ℝ) ^ r ≤ xs → HasChars (fgl Ch X) (frame Ch X f) (r : EReal) ∧ ∀ k : ℕ, nuFac p y f k ≤ ((k * r : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X f xs r hAF hr
  have hp0 : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
    have : X.v (p : X.C) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hxs0 : (0 : ℝ) < (xs : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 r) hr
  have hxs : xs ≠ 0 := fun h => by rw [h] at hxs0; simp at hxs0
  obtain ⟨-, χ, hχ, hmin⟩ := exists_flag_characters X.C X.v X.O X.ints _ _ _ _ xs hAF hxs
  let lf : Fin (rk f) → Fin (chD Ch.ch) → X.C := fun b j =>
    algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ (Fin.castLE (rk_le f) b)) j)
  have hl : ∀ b, IsCharLog (fgl Ch X) (lf b) := fun b =>
    GlobalTheory.T.chart_character_is_logarithm E H Dw l Xo c p T io y Ch X _ (hχ _)
  have hdet : pairDet lf (frame Ch X f) = algebraMap X.O X.C (Matrix.of fun a b : Fin (f.2.val + 1) =>
      ∑ j, X.ι (Ch.uvecT ⟨f.1, Fin.castLE f.2.isLt a⟩ j) *
        ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ (Fin.castLE f.2.isLt b)) j).det := by
    rw [RingHom.map_det]
    unfold pairDet
    congr 1
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul, frame, lieVec, jX,
      RingHom.comp_apply, X.comp, lf]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hm := hmin f.2
  rw [← hdet] at hm
  set D := pairDet lf (frame Ch X f) with hD
  have hDpos : (0 : ℝ) < (X.v D : ℝ) := lt_of_lt_of_le hxs0 (by exact_mod_cast hm)
  have hD0 : D ≠ 0 := fun h => by rw [h, map_zero] at hDpos; simp at hDpos
  have hlog := log_v_p_neg X
  have hval : ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ)) ≤ r := by
    have h1 : r * Real.log (X.v (p : X.C) : ℝ) ≤ Real.log (X.v D : ℝ) := by
      rw [← Real.log_rpow hp0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hp0 r) (hr.trans (by exact_mod_cast hm))
    have h2 := mul_le_mul_of_nonpos_left h1 (inv_lt_zero.2 hlog).le
    rwa [← mul_assoc, mul_comm _ r, mul_assoc, inv_mul_cancel₀ hlog.ne, mul_one] at h2
  have hvD : vX_vp X D = (((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ) : ℝ) : WithTop ℝ) :=
    vX_vp_apply X hD0
  refine ⟨(hasChars_iff (isSatFrame_frame Ch X f) _).2 ⟨lf, hl, ?_⟩, fun k => ?_⟩
  · rw [← hD, hvD]
    exact EReal.coe_le_coe_iff.2 hval
  · refine (nuFac_le Ch X f k).trans ?_
    refine (GlobalTheory.FGDepth.CharBound.detDepth_le_char X.C (vX_vp X) (rk f) _ k (fgl Ch X) (frame Ch X f) lf hl).trans ?_
    have e : Matrix.det (Matrix.of fun a b => ∑ e, lf b e * frame Ch X f a e) = D := rfl
    rw [e, AddValuation.map_pow, hvD, ← WithTop.coe_nsmul, nsmul_eq_mul]
    show ((k * ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ)) : ℝ) : EReal) ≤ _
    exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left hval (Nat.cast_nonneg k))

end GlobalTheory.RefSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColengthStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStep_characters_of_colength : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ (f : Lt1 Dw) (xs : NNReal) (r : ℝ), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult f.1)) j => X.ι (Ch.uvecT ⟨f.1, i⟩ j)) xs → (X.v (p : X.C) : ℝ) ^ r ≤ xs → HasChars (fgl Ch X) (frame Ch X f) (r : EReal) ∧ ∀ k : ℕ, nuFac p y f k ≤ ((k * r : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefSum.hasChars_frame_of_hasAF | exact GlobalTheory.RefSum.hasChars_frame_of_hasAF | (intros; apply GlobalTheory.RefSum.hasChars_frame_of_hasAF <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLinePotentialHessianDetOwnRow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormMulFibreVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormMulFibreVolume
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2.BaseVol

open GlobalTheory.LocFub.TopDens (dens_smul dens_add dens_zero)

variable {n d : ℕ} {J : Type}

theorem pull_bsL_dz (ε : Fin n ≃ Fin d ⊕ J) (a : Fin d) :
    pull (bsL ε) (dz a) = dz (ε.symm (.inl a)) ∧ pull (bsL ε) (dzb a) = dzb (ε.symm (.inl a)) := by
  rw [(pull_dz _ a).1, (pull_dz _ a).2]
  simp [bsL_apply, coordVec, PiLp.single_apply]

theorem pull_bsL_prod (ε : Fin n ≃ Fin d ⊕ J) (s : Finset (Fin d)) :
    pull (bsL ε) ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev d) : Alt d) =
      ((∏ a ∈ s, (Complex.I / 2) • sym (ε.symm (.inl a), ε.symm (.inl a)) : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih]
    congr 1
    simp [sym, (pull_bsL_dz ε a).1, (pull_bsL_dz ε a).2]

theorem prod_mem (g : J → Fin n) (s : Finset J) :
    ((∏ j ∈ s, (Complex.I / 2) • sym (g j, g j) : Ev n) : Alt n) ∈ ⋀[ℂ]^(2 * s.card) (Fin n ⊕ Fin n → ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Subalgebra.coe_mul, Finset.card_insert_of_notMem ha,
      show 2 * (s.card + 1) = 1 + 1 + 2 * s.card by ring]
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ih
    rw [Subalgebra.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    change dz (g a) * dzb (g a) ∈ _
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ?_
    · simp [dz, ExteriorAlgebra.exteriorPower]
    · simp [dzb, ExteriorAlgebra.exteriorPower]

theorem dens_pull_bas [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) {T : Finset (Fin (d + d))} (hT : T ≠ Finset.univ) :
    dens (pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = 0 := by
  have hc : T.card < d + d := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)
  have hn : n = d + Fintype.card J := by simpa using Fintype.card_congr ε
  have hm : pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) ∈
      ⋀[ℂ]^(T.card + 2 * (Finset.univ : Finset J).card) (Fin n ⊕ Fin n → ℂ) := by
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ (prod_mem _ _)
    rw [bas, ExteriorAlgebra.basis_apply _ T, CxForm.pull, ExteriorAlgebra.map_apply_ιMulti,
      ← exteriorPower.ιMulti_apply_coe]
    exact Subtype.property _
  have := GlobalTheory.PullTop.repr_eq_zero_of_card_ne
    ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) ⟨_, hm⟩ (S := Finset.univ)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  rw [dens]
  exact div_eq_zero_iff.2 (Or.inl this)

theorem pull_vol_mul [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) :
    pull (bsL ε) (vol d : Alt d) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) = (vol n : Alt n) := by
  rw [vol, pull_bsL_prod, ← Subalgebra.coe_mul, vol, ← ε.symm.prod_comp, Fintype.prod_sum_type]

theorem dens_pull_mul_vol : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  intro n d J _ ε α
  have hα : α ∈ Submodule.span ℂ (Set.range (bas d)) := by rw [(bas d).span_eq]; trivial
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    by_cases hT : T = Finset.univ
    · obtain ⟨c, hc, e⟩ := vol_eq d
      have e' : bas d T = c⁻¹ • (vol d : Alt d) := by rw [e, hT, inv_smul_smul₀ hc]
      rw [e', map_smul, smul_mul_assoc, dens_smul, dens_smul, dens_vol, pull_vol_mul, dens_vol]
    · rw [dens_pull_bas ε hT]
      simp [dens, hT]
  | zero => simp [dens_zero]
  | add x y _ _ hx hy => rw [map_add (f := _), add_mul, dens_add, dens_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, dens_smul, dens_smul, hx]

end GlobalTheory.FlagCell2.BaseVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormMulFibreVolumeStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_baseForm_mul_fibreVolume : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  first | exact @GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol | exact GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol | (intros; apply GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBlockTriangularDiagonalBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBlockTriangularDiagonalBlocks
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagTri

theorem eval_zero_of_const {A : Type} [CommRing A] [Algebra ℂ A] (l : A →ₗ[ℂ] ℂ) (Q : Polynomial A) (c : ℂ)
    (h : ∀ x : ℂ, x ≠ 0 → l (Q.eval (algebraMap ℂ A x)) = c) : l (Q.eval (algebraMap ℂ A 0)) = c := by
  have hc : Continuous fun x : ℂ => l (Q.eval (algebraMap ℂ A x)) := by
    clear h
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval_add, map_add (f := _)]; exact hp.add hq
    | monomial k a =>
      have : (fun x : ℂ => l ((Polynomial.monomial k a).eval (algebraMap ℂ A x))) = fun x => x ^ k * l a := by
        funext x
        rw [Polynomial.eval_monomial, ← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [this]
      fun_prop
  have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc (continuous_const (y := c)) (fun x hx => h x hx)
  exact congrFun this 0

variable {n : ℕ}

def scale (c : Fin n → ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.diagonal (Sum.elim c c)))

theorem dens_scale (c : Fin n → ℂ) (β : Alt n) : dens (scale c β) = (∏ a, c a) ^ 2 * dens β := by
  simp only [dens, scale, bas]
  rw [exterior_repr_univ_map, LinearMap.det_toLin', Matrix.det_diagonal, Fintype.prod_sum_type, mul_div_assoc, sq]
  rfl

theorem scale_dz (c : Fin n → ℂ) (a : Fin n) : scale c (dz a) = c a • dz a ∧ scale c (dzb a) = c a • dzb a := by
  simp only [dz, dzb, ← map_smul]
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    by_cases h : b = a <;> simp [Matrix.mulVec_diagonal, Pi.single_apply, h]

theorem scale_sym (c : Fin n → ℂ) (a b : Fin n) :
    scale c (sym (a, b) : Ev n) = (c a * c b) • ((sym (a, b) : Ev n) : Alt n) := by
  change scale c (dz a * dzb b) = (c a * c b) • (dz a * dzb b)
  rw [map_mul, (scale_dz c a).1, (scale_dz c b).2, smul_mul_smul_comm]

theorem scale_pull {d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (c : Fin n → ℂ) (hc : ∀ a, c (ε.symm (.inl a)) = 1)
    (α : Alt d) : scale c (pull (bsL ε) α) = pull (bsL ε) α := by
  have key (a : Fin d) (b : Fin n) : c b * bsL ε (coordVec b) a = bsL ε (coordVec b) a ∧
      c b * (starRingEnd ℂ) (bsL ε (coordVec b) a) = (starRingEnd ℂ) (bsL ε (coordVec b) a) := by
    rw [bsL_apply]
    by_cases h : ε.symm (.inl a) = b
    · subst h
      simp [hc]
    · simp [coordVec, h]
  rw [scale, pull, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul]
  congr 3
  ext (i | i) (j | j) <;> simp [Matrix.diagonal_mul, key]

theorem map_prod_pow {T : Type} (φ : Alt n →ₐ[ℂ] Alt n) (x y : T → Ev n) (r : T → ℕ)
    (h : ∀ t, φ (x t) = y t) (s : Finset T) :
    φ ((∏ t ∈ s, x t ^ r t : Ev n) : Alt n) = ((∏ t ∈ s, y t ^ r t : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih,
      Subalgebra.coe_pow, Subalgebra.coe_pow, map_pow, h]

theorem dens_blockTri : ∀ (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ) (K : T → Fin n → Fin n → ℂ) (r : T → ℕ), (∀ t, r t = Fintype.card {j // lev j = t}) → (∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0) → ∀ α : Alt d, dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n)) = dens (pull (bsL ε) α * ((∏ t, (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t}, K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1))) ^ r t : Ev n) : Alt n)) := by
  intro n d J T _ _ ε lev ρ K r hr hK α
  let wt : Fin n → ℕ := fun a => (ε a).elim (fun _ => 0) fun j => ρ (lev j) + 1
  have w0 (a) : wt (ε.symm (.inl a)) = 0 := by simp [wt]
  have w1 (j) : wt (ε.symm (.inr j)) = ρ (lev j) + 1 := by simp [wt]
  have hw (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) :
      wt a < ρ t + 1 ∨ ∃ j : {j // lev j = t}, ε.symm (.inr j.1) = a := by
    obtain ⟨a | j, rfl⟩ := ε.symm.surjective a
    · left; rw [w0]; omega
    · by_cases e : lev j = t
      · exact .inr ⟨⟨j, e⟩, rfl⟩
      · left
        rw [w1]
        by_contra hn
        obtain ⟨b, hb⟩ := h
        have := hK t j e (by omega) b
        tauto
  have hw' (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) : wt a ≤ ρ t + 1 := by
    rcases hw t a h with h | ⟨j, rfl⟩
    · omega
    · rw [w1, j.2]
  let l : Ev n →ₗ[ℂ] ℂ :=
    { toFun := fun x => dens (pull (bsL ε) α * (x : Alt n))
      map_add' := fun x y => by simp [dens, mul_add, add_div]
      map_smul' := fun c x => by simp [dens, mul_div_assoc] }
  have hl (x : Ev n) : l x = dens (pull (bsL ε) α * (x : Alt n)) := rfl
  let e : T → Fin n → Fin n → ℕ := fun t a b => (ρ t + 1 - wt a) + (ρ t + 1 - wt b)
  let Q : Polynomial (Ev n) := ∏ t, (∑ a, ∑ b, Polynomial.monomial (e t a b) (K t a b • sym (a, b))) ^ r t
  have hQ (x : ℂ) : Q.eval (algebraMap ℂ (Ev n) x) =
      ∏ t, (∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) ^ r t := by
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    refine Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← map_pow, mul_comm, ← Algebra.smul_def, smul_smul]
  rw [← hl, ← hl, ← eval_zero_of_const l Q (l (∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n)) ?_]
  · rw [hQ]
    refine congrArg l (Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_)
    have inj : Function.Injective fun j : {j // lev j = t} => ε.symm (.inr j.1) :=
      fun i j h => Subtype.ext (Sum.inr_injective (ε.symm.injective h))
    symm
    refine Fintype.sum_of_injective _ inj _ _ (fun a ha => Finset.sum_eq_zero fun b _ => ?_) fun a => ?_
    · by_cases h : K t a b = 0
      · simp [h]
      · rcases hw t a ⟨b, .inl h⟩ with h' | h'
        · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
        · exact absurd h' ha
    · refine Fintype.sum_of_injective _ inj _ _ (fun b hb => ?_) fun b => ?_
      · by_cases h : K t (ε.symm (.inr a.1)) b = 0
        · simp [h]
        · rcases hw t b ⟨_, .inr h⟩ with h' | h'
          · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
          · exact absurd h' hb
      · simp [e, w1, a.2, b.2]
  · intro x hx
    have h1 := dens_scale (fun a => x⁻¹ ^ wt a)
      (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n))
    rw [map_mul, scale_pull ε _ (fun a => by simp [w0]),
      map_prod_pow _ _ (fun t => (x⁻¹ ^ (ρ t + 1)) ^ 2 • ∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) r ?_,
      ← hl, ← hl] at h1
    · have h2 : ∏ a, x⁻¹ ^ wt a = ∏ t, (x⁻¹ ^ (ρ t + 1)) ^ r t := by
        rw [← ε.symm.prod_comp, Fintype.prod_sum_type]
        simp only [w0, w1, pow_zero, Finset.prod_const_one, one_mul]
        rw [← Fintype.prod_fiberwise lev]
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [Finset.prod_congr rfl (g := fun _ => x⁻¹ ^ (ρ t + 1)) fun j _ => by rw [j.2], Finset.prod_const, hr]
        simp
      simp only [smul_pow, Finset.prod_smul] at h1
      rw [map_smul, ← hQ, h2, ← Finset.prod_pow, smul_eq_mul] at h1
      simp only [← pow_mul, mul_right_comm _ (r _) 2] at h1
      refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (inv_ne_zero hx)) h1
    · intro t
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, map_sum, map_smul, scale_sym, Finset.smul_sum,
        smul_smul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      by_cases h : K t a b = 0
      · simp [h]
      · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le (hw' t a ⟨b, .inl h⟩)
        obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hw' t b ⟨a, .inr h⟩)
        have : e t a b = p + q := by simp only [e]; omega
        rw [this, sq]
        nth_rw 1 [hp]
        rw [hq]
        simp only [inv_pow]
        field_simp
        ring

end GlobalTheory.FlagTri
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBlockTriangularDiagonalBlocksStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_blockTriangular_diagonalBlocks : ∀ (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ) (K : T → Fin n → Fin n → ℂ) (r : T → ℕ), (∀ t, r t = Fintype.card {j // lev j = t}) → (∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0) → ∀ α : Alt d, dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n)) = dens (pull (bsL ε) α * ((∏ t, (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t}, K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1))) ^ r t : Ev n) : Alt n)) := by
  first | exact @GlobalTheory.FlagTri.dens_blockTri | exact GlobalTheory.FlagTri.dens_blockTri | (intros; apply GlobalTheory.FlagTri.dens_blockTri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSquaredLengthUpperUnitriangularGramEqOfAgr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSquaredLengthUpperUnitriangularGramEqOfAgr
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_row_eq {s : ℕ} (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a : Fin s) (ha : a ≤ i) (k : Fin s) :
    upU y' a k = upU y a k := by
  simp only [upU, Matrix.of_apply]
  split_ifs with hk
  · exact h ⟨(k, a), hk⟩ ha
  · rfl
  · rfl

theorem upU_gram_entry_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a c : Fin s) (ha : a ≤ i) (hc : c ≤ i) :
    (upU y' * G * (upU y')ᴴ) a c = (upU y * G * (upU y)ᴴ) a c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha,
    upU_row_eq y y' i h c hc]

theorem leadMinor_upU_gram_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (j : ℕ) (hj : j ≤ (i : ℕ) + 1) :
    leadMinor (upU y' * G * (upU y')ᴴ) j = leadMinor (upU y * G * (upU y)ᴴ) j := by
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  apply upU_gram_entry_eq G y y' i h
  · rw [Fin.le_def]; have := a.2; omega
  · rw [Fin.le_def]; have := b.2; omega

theorem grD_upU_gram_eq : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  intro s G y y' i h
  unfold grD
  rw [leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSquaredLengthUpperUnitriangularGramEqOfAgrStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedSquaredLength_upperUnitriangular_gram_eq_of_agree : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  first | exact @GlobalTheory.FlagCell2.grD_upU_gram_eq | exact GlobalTheory.FlagCell2.grD_upU_gram_eq | (intros; apply GlobalTheory.FlagCell2.grD_upU_gram_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLeviFormEqZeroOfComplexLineInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLeviFormEqZeroOfComplexLineInvariant
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory

theorem fderiv_smul_eq_zero_of_invariant {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (ξ : E) (hf : ∀ (x : E) (c : ℂ), f (x + c • ξ) = f x) (x : E) (c : ℂ) :
    fderiv ℝ f x (c • ξ) = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hl : HasDerivAt (fun t : ℝ => x + t • (c • ξ)) (c • ξ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • ξ)).const_add x
    have hx : x + (0 : ℝ) • (c • ξ) = x := by simp
    have hd' : DifferentiableAt ℝ f (x + (0 : ℝ) • (c • ξ)) := by rw [hx]; exact hd
    have h1 := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [hx] at h1
    have hconst : (fun t : ℝ => f (x + t • (c • ξ))) = fun _ => f x := by
      funext t
      rw [← smul_assoc]
      exact hf x _
    have h2 : HasDerivAt (fun t : ℝ => f (x + t • (c • ξ))) 0 0 := by
      rw [hconst]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

end GlobalTheory

namespace GlobalTheory

theorem ddc_eq_zero_of_invariant : ∀ (n : ℕ) (u : V n → ℝ) (z ξ η : V n), ContDiffAt ℝ 2 u z → (∀ (x : V n) (c : ℂ), u (x + c • ξ) = u x) → ddc u z ξ η = 0 ∧ ddc u z η ξ = 0 := by
  intro n u z ξ η hu hinv
  have hinv' : ∀ (x : V n) (c : ℂ), (fun y => ((u y : ℝ) : ℂ)) (x + c • ξ) = (fun y => ((u y : ℝ) : ℂ)) x := by
    intro x c; simp only [hinv x c]
  have hdbar : (fun x => dbar (fun y => ((u y : ℝ) : ℂ)) x ξ) = fun _ => 0 := by
    funext x
    rw [dbar_apply]
    have h1 := fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x 1
    have h2 := fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x Complex.I
    rw [one_smul] at h1
    rw [h1, h2]; simp
  have hL1 : leviForm u z η ξ = 0 := by
    rw [leviForm_eq_del_dbar hu, hdbar, del_const]; rfl
  have hL2 : leviForm u z ξ η = 0 := by
    rw [← leviForm_conj_symm hu, hL1, map_zero]
  have e : ∀ a b, ddc u z a b = kappa * leviForm u z a b := fun a b => rfl
  exact ⟨by rw [e, hL2, mul_zero], by rw [e, hL1, mul_zero]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLeviFormEqZeroOfComplexLineInvariantStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddcLeviForm_eq_zero_of_complexLine_invariant : ∀ (n : ℕ) (u : V n → ℝ) (z ξ η : V n), ContDiffAt ℝ 2 u z → (∀ (x : V n) (c : ℂ), u (x + c • ξ) = u x) → ddc u z ξ η = 0 ∧ ddc u z η ξ = 0 := by
  first | exact @GlobalTheory.ddc_eq_zero_of_invariant | exact GlobalTheory.ddc_eq_zero_of_invariant | (intros; apply GlobalTheory.ddc_eq_zero_of_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DzWedgeDzbarSumPowCardEqFactorialDetProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DzWedgeDzbarSumPowCardEqFactorialDetProd
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2.TopPow

variable {R : Type} [CommRing R] [Algebra ℂ R]

theorem eq_zero_of_eq_neg_self {x : R} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel x
  have h3 := congrArg (fun y : R => (1 / 2 : ℂ) • y) h2
  simp only [smul_smul, smul_zero] at h3
  norm_num at h3
  exact h3

theorem prod_eq_zero_of_pair {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → R) {i j : ι} (hij : i ≠ j)
    (h : f i * f j = 0) : ∏ k, f k = 0 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc, h, zero_mul]

theorem pow_card_sum_of_sq {B : Type} [Fintype B] [DecidableEq B] (w : B → R) (hw : ∀ a, w a * w a = 0) :
    (∑ a, w a) ^ Fintype.card B = (Fintype.card B).factorial • ∏ a, w a := by
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  have key : ∀ g : Fin (Fintype.card B) → B,
      ∏ i, w (g i) = if Function.Injective g then ∏ a, w a else 0 := by
    intro g
    split_ifs with hg
    · exact Fintype.prod_bijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp⟩) _ _
        (fun _ => rfl)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
        by_contra h
        push_neg at h
        exact hg h
      exact prod_eq_zero_of_pair (fun k => w (g k)) hne (by simp only [hij]; exact hw _)
  simp only [key, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]

theorem prod_perm {B : Type} [Fintype B] [DecidableEq B] (s : B → B → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (σ : Equiv.Perm B) :
    ∏ a, s a (σ a) = Equiv.Perm.sign σ • ∏ a, s a a := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap f x y hxy ih =>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy, mul_neg_one, Units.neg_smul, ← ih]
    have split : ∀ F : B → R, ∏ a, F a = F x * F y * ∏ a ∈ (Finset.univ.erase x).erase y, F a := fun F => by
      rw [mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ y⟩),
        Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
    rw [split (fun a => s a ((f * Equiv.swap x y) a)), split (fun a => s a (f a))]
    have hrest : ∏ a ∈ (Finset.univ.erase x).erase y, s a ((f * Equiv.swap x y) a) =
        ∏ a ∈ (Finset.univ.erase x).erase y, s a (f a) := Finset.prod_congr rfl fun a ha => by
      have hay : a ≠ y := (Finset.mem_erase.1 ha).1
      have hax : a ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 ha).2).1
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hay]
    rw [hrest]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [hs, neg_mul]

theorem ι_three_swap {W : Type} [AddCommGroup W] [Module ℂ W] (v w x : W) :
    ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) =
      -(ExteriorAlgebra.ι ℂ x * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
  have h : ∀ p q : W, ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q =
      -(ExteriorAlgebra.ι ℂ q * ExteriorAlgebra.ι ℂ p) :=
    fun p q => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap p q)
  calc ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x)
      = (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ x := (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ x)) := by
      rw [h v w, neg_mul, mul_assoc]
    _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) * ExteriorAlgebra.ι ℂ v := by
      rw [h v x, mul_neg, neg_neg, mul_assoc]
    _ = _ := by rw [h w x, neg_mul, mul_assoc]

theorem prod_smul_eq {ι : Type} [Fintype ι] (c : ι → ℂ) (x : ι → R) :
    ∏ a, c a • x a = (∏ a, c a) • ∏ a, x a := by
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

theorem sum_pow_card {B : Type} [Fintype B] [DecidableEq B] (s : B → B → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (K : Matrix B B ℂ) :
    (∑ a, ∑ b, K a b • s a b) ^ Fintype.card B = ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, s a a := by
  have hzero : ∀ a b c, s a b * s c b = 0 := fun a b c => eq_zero_of_eq_neg_self (hs a b c b)
  have hzero' : ∀ a b d, s a b * s a d = 0 := fun a b d =>
    eq_zero_of_eq_neg_self ((hs a b a d).trans (by rw [mul_comm]))
  have hw : ∀ a, (∑ b, K a b • s a b) * (∑ b, K a b • s a b) = 0 := fun a => by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
    rw [smul_mul_smul_comm, hzero', smul_zero]
  rw [pow_card_sum_of_sq _ hw, Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [prod_smul_eq]
  have hnon : ∀ g : B → B, ¬ Function.Injective g → (∏ a, K a (g a)) • ∏ a, s a (g a) = 0 := by
    intro g hg
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hg h
    rw [prod_eq_zero_of_pair (fun k => s k (g k)) hne (by simp only [hij]; exact hzero _ _ _), smul_zero]
  have hsum : ∑ g : B → B, (∏ a, K a (g a)) • ∏ a, s a (g a) =
      ∑ σ : Equiv.Perm B, (∏ a, K a (σ a)) • ∏ a, s a (σ a) := by
    have hm := Finset.sum_map (Finset.univ : Finset (Equiv.Perm B))
      ⟨fun σ : Equiv.Perm B => (σ : B → B), DFunLike.coe_injective⟩
      (fun g : B → B => (∏ a, K a (g a)) • ∏ a, s a (g a))
    simp only [Function.Embedding.coeFn_mk] at hm
    rw [← hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun g _ hg => hnon g fun hi => hg ?_).symm
    exact Finset.mem_map.2 ⟨Equiv.ofBijective g hi.bijective_of_finite, Finset.mem_univ _, rfl⟩
  rw [hsum]
  simp only [prod_perm s hs, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  rw [← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Matrix.det_transpose, Matrix.det_apply]
  congr 2
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm]

end GlobalTheory.FlagCell2.TopPow

namespace GlobalTheory.FlagCell2

theorem pow_card_sum_sym : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e →
    ∀ K : Matrix B B ℂ, (∑ a, ∑ b, K a b • sym (e a, e b) : Ev n) ^ Fintype.card B =
      ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, sym (e a, e a) := by
  intro n B _ _ e _ K
  refine TopPow.sum_pow_card (fun a b => sym (e a, e b)) (fun a b c d => ?_) K
  apply Subtype.ext
  change dz (e a) * dzb (e b) * (dz (e c) * dzb (e d)) = -(dz (e a) * dzb (e d) * (dz (e c) * dzb (e b)))
  simp only [dz, dzb, mul_assoc]
  rw [← mul_neg]
  congr 1
  exact TopPow.ι_three_swap _ _ _

end GlobalTheory.FlagCell2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DzWedgeDzbarSumPowCardEqFactorialDetProdStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dzWedgeDzbar_sum_pow_card_eq_factorial_det_prod : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ K : Matrix B B ℂ, (∑ a, ∑ b, K a b • sym (e a, e b) : Ev n) ^ Fintype.card B = ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, sym (e a, e a) := by
  first | exact @GlobalTheory.FlagCell2.pow_card_sum_sym | exact GlobalTheory.FlagCell2.pow_card_sum_sym | (intros; apply GlobalTheory.FlagCell2.pow_card_sum_sym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFubiniStudyDensitiesEqFlagCellInvariantDensi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFubiniStudyDensitiesEqFlagCellInvariantDensi
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCellDens

theorem telesc (s : ℕ) (Δ : ℕ → ℝ) (h0 : Δ 0 = 1) (hp : ∀ k, k ≤ s → Δ k ≠ 0) :
    ∏ i ∈ Finset.range s, (Δ (i + 1) / Δ i) ^ (s - i) = ∏ i ∈ Finset.range s, Δ (i + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih' := ih fun k hk => hp k (by omega)
    have e1 : ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) ^ (s + 1 - i) =
        (∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) ^ (s - i)) *
          ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show s + 1 - i = (s - i) + 1 by omega, pow_succ]
    have e2 : ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) = Δ (s + 1) := by
      rw [Finset.prod_div_distrib]
      have a1 := Finset.prod_range_succ' Δ (s + 1)
      have a2 := Finset.prod_range_succ Δ (s + 1)
      have hne : ∏ i ∈ Finset.range (s + 1), Δ i ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i hi => hp i (by rw [Finset.mem_range] at hi; omega)
      rw [h0, mul_one] at a1
      rw [a1] at a2
      field_simp
      linarith [a2]
    rw [e1, e2, Finset.prod_range_succ, ih', Nat.sub_self, pow_zero, mul_one, Finset.prod_range_succ]

theorem key (s : ℕ) (Δ : ℕ → ℝ) (h0 : Δ 0 = 1) (hp : ∀ k, k ≤ s → 0 < Δ k) :
    ∏ i : Fin s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) =
      Δ s ^ ((s : ℤ) - 1) * ∏ i : Fin s, Δ i ^ (-2 : ℤ) := by
  have hne : ∀ k, k ≤ s → Δ k ≠ 0 := fun k hk => (hp k hk).ne'
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) s,
    Fin.prod_univ_eq_prod_range (fun i : ℕ => Δ i ^ (-2 : ℤ)) s]
  have e1 : ∏ i ∈ Finset.range s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) =
      ∏ i ∈ Finset.range s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ (s - i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show s - 1 - i + 1 = s - i by omega]
  rw [e1, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    telesc s Δ h0 hne, Finset.prod_zpow]
  have a1 := Finset.prod_range_succ' Δ s
  have a2 := Finset.prod_range_succ Δ s
  rw [h0, mul_one] at a1
  rw [a1] at a2
  rw [a2]
  have hP : ∏ i ∈ Finset.range s, Δ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => hne i (by rw [Finset.mem_range] at hi; omega)
  have hs := hne s le_rfl
  rw [zpow_sub₀ hs, zpow_natCast, zpow_one, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
  field_simp

end GlobalTheory.FlagCellDens

namespace GlobalTheory.FlagCellDens

theorem leadMinor_pos {s : ℕ} {M : Matrix (Fin s) (Fin s) ℂ} (hM : M.PosDef) (k : ℕ) :
    0 < (leadMinor M k).re ∧ (leadMinor M k).im = 0 := by
  have h := (hM.submatrix (e := (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)) Subtype.val_injective).det_pos
  have := Complex.pos_iff.1 h
  exact ⟨this.1, this.2.symm⟩

theorem leadMinor_self {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) : leadMinor M s = M.det := by
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin s => (a : ℕ) < s)
    fun a => a.2) M
  exact this

def lowEquiv {s k : ℕ} (hk : k ≤ s) : Fin k ≃ {a : Fin s // (a : ℕ) < k} where
  toFun j := ⟨Fin.castLE hk j, j.2⟩
  invFun a := ⟨a.1.1, a.2⟩
  left_inv j := rfl
  right_inv a := rfl

theorem lminor_transpose {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i : Fin (s + 1)) :
    ReciprocityTheory.ChartRestriction.G.FD.lminor Mᵀ i = leadMinor M i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor leadMinor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have := Matrix.det_submatrix_equiv_self (lowEquiv (Nat.le_of_lt_succ i.isLt))
    (M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < i} → Fin s) Subtype.val)
  rw [← this, Matrix.submatrix_submatrix]
  rfl

end GlobalTheory.FlagCellDens


open GlobalTheory.FlagCellDens in
theorem GlobalTheory.FlagCellDens.main : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ), ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ) * (G.det.re / (leadMinor (upU y * G * (upU y)ᴴ) i).re / grD (upU y * G * (upU y)ᴴ) i ^ ((s - 1 - i : ℕ) + 1))) = GlobalTheory.TrueCx.flagConst s * G.det.re ^ ((s : ℤ) - 1) * GlobalTheory.FlagFibre.dens Gᵀ y := by
  intro s G hG y
  set M := upU y * G * (upU y)ᴴ with hMdef
  have hU : (upU y).det = 1 := by rw [upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  have hM : M.PosDef := hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [hU]; exact isUnit_one)))
  have hdet : M.det = G.det := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hU]; simp
  have hT : (GlobalTheory.FlagFibre.uni y)ᴴ * Gᵀ * GlobalTheory.FlagFibre.uni y = Mᵀ := by
    rw [hMdef, upU_eq]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    congr 1
  set Δ : ℕ → ℝ := fun k => (leadMinor M k).re with hΔ
  have hGs : G.det.re = Δ s := by rw [hΔ]; simp only [leadMinor_self, hdet]
  have hnorm : ∀ i : Fin s, ‖ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni y)ᴴ * Gᵀ * GlobalTheory.FlagFibre.uni y) i.castSucc‖ = Δ i := by
    intro i
    rw [hT, lminor_transpose]
    obtain ⟨h1, h2⟩ := leadMinor_pos hM i
    have : leadMinor M (i.castSucc : ℕ) = ((leadMinor M i).re : ℂ) := Complex.ext (by simp) (by simp [h2])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
  have h0 : Δ 0 = 1 := by
    simp only [hΔ, leadMinor]
    haveI : IsEmpty {a : Fin s // (a : ℕ) < 0} := ⟨fun a => Nat.not_lt_zero _ a.2⟩
    rw [Matrix.det_isEmpty]; simp
  have hp : ∀ k, k ≤ s → 0 < Δ k := fun k _ => (leadMinor_pos hM k).1
  rw [Finset.prod_mul_distrib, GlobalTheory.FlagFibre.dens]
  simp only [hnorm]
  have hc : ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ)) = GlobalTheory.TrueCx.flagConst s := by
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ))) s,
      Finset.prod_range_reflect (fun i : ℕ => ((i.factorial : ℝ) / Real.pi ^ i)) s]
    rfl
  rw [hc, mul_assoc]
  congr 1
  rw [hGs]
  exact key s Δ h0 hp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFubiniStudyDensitiesEqFlagCellInvariantDensiStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_fubiniStudy_densities_eq_flagCell_invariant_density : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ), ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ) * (G.det.re / (leadMinor (upU y * G * (upU y)ᴴ) i).re / grD (upU y * G * (upU y)ᴴ) i ^ ((s - 1 - i : ℕ) + 1))) = GlobalTheory.TrueCx.flagConst s * G.det.re ^ ((s : ℤ) - 1) * GlobalTheory.FlagFibre.dens Gᵀ y := by
  first | exact @GlobalTheory.FlagCellDens.main | exact GlobalTheory.FlagCellDens.main | (intros; apply GlobalTheory.FlagCellDens.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClass
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.CellDens

theorem dens_smul {n : ℕ} (c : ℂ) (β : Alt n) : dens (c • β) = c * dens β := by
  simp [dens, mul_div_assoc]

theorem dens_blocks (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ)
    (K : T → Fin n → Fin n → ℂ) (r : T → ℕ) (hr : ∀ t, r t = Fintype.card {j // lev j = t})
    (hK : ∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0)
    (α : Alt d) :
    dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, (kappa * K t a b) • sym (a, b)) ^ r t : Ev n) : Alt n)) =
      dens α * ∏ t, ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) := by
  rw [GlobalTheory.T.topDegreeDensity_blockTriangular_diagonalBlocks n d J T ε lev ρ (fun t a b => kappa * K t a b) r hr
    (fun t j h1 h2 b => by simp [(hK t j h1 h2 b).1, (hK t j h1 h2 b).2]) α]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 (t : T) : (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t},
      (kappa * K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1)) : Ev n) ^ r t =
      ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) •
        ∏ a : {j // lev j = t}, (Complex.I / 2) • sym (ε.symm (.inr a.1), ε.symm (.inr a.1)) := by
    have h := GlobalTheory.T.dzWedgeDzbar_sum_pow_card_eq_factorial_det_prod n {j // lev j = t} (fun a => ε.symm (.inr a.1))
      (fun a b hab => Subtype.ext (Sum.inr_injective (ε.symm.injective hab)))
      (kappa • Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)))
    rw [Matrix.det_smul, ← hr t] at h
    refine Eq.trans h ?_
    rw [Finset.prod_smul, Finset.prod_const, Finset.card_univ, ← hr t, smul_smul]
    congr 1
    have hk : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2) := by
      rw [kappa]; field_simp
    rw [hk, mul_pow, inv_pow]
    ring
  simp only [h1]
  rw [Finset.prod_smul, Fintype.prod_fiberwise lev
    (fun j => (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j))), Subalgebra.coe_smul, mul_smul_comm, dens_smul,
    GlobalTheory.T.topDegreeDensity_baseForm_mul_fibreVolume n d J ε α, mul_comm]

theorem cellPot_add {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m)
    (j : Cell m) (h1 : j.root ≠ x) (h2 : x.2.val ≤ j.root.2.val) (z : V n) (c : ℂ) :
    cellPot ε G x (z + c • coordVec (ε.symm (.inr j))) = cellPot ε G x z := by
  have hb : bsL ε (z + c • coordVec (ε.symm (.inr j))) = bsL ε z := by
    ext a
    simp [bsL_apply, coordVec]
  have hf (j' : Cell m) (h : j' ≠ j) : fb ε (z + c • coordVec (ε.symm (.inr j))) j' = fb ε z j' := by
    simp [fb, coordVec, h]
  unfold cellPot
  rw [hb]
  congr 2
  refine GlobalTheory.T.gradedSquaredLength_upperUnitriangular_gram_eq_of_agree _ _ _ _ _ fun s hs => hf _ ?_
  rintro rfl
  exact h1 (Sigma.ext rfl (heq_of_eq (le_antisymm hs h2)))

theorem dens_cellForm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  intro ι _ m n d ε G a w hG hC
  have e : cellFib ε G w = ∏ x : Root m, (∑ p, ∑ q,
      (kappa * -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) • sym (p, q)) ^ (m x.1 - 1 - x.2 : ℕ) := by
    simp only [cellFib, fibrePoint, map_prod, map_pow, map_neg, map_X, aeval_X, ofValues, ddc, mul_neg, neg_smul,
      Finset.sum_neg_distrib]
  have hk : kappa ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [kappa, hπ]
  rw [cellForm, e, dens_blocks n d (Cell m) (Root m) ε Cell.root (fun x => x.2.val)
    (fun x p q => -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) (fun x => m x.1 - 1 - x.2)
    (fun x => by convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w x (hG _) (hC _)).1.symm) ?_]
  · congr 1
    rw [fibDens, Fintype.prod_sigma, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.T.prod_fubiniStudy_densities_eq_flagCell_invariant_density _ _ (hG τ), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]
    congr 1
    · push_cast
      rfl
    · convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w ⟨τ, i⟩ (hG _) (hC _)).2 <;> rfl
  · intro x j h1 h2 b
    have h := GlobalTheory.T.ddcLeviForm_eq_zero_of_complexLine_invariant n (cellPot ε G x) w (coordVec (ε.symm (.inr j))) (coordVec b)
      (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m n d ε G w x (hG _) (hC _)).1 (cellPot_add ε G x j h1 h2)
    simp only [ddc, mul_eq_zero, hk, false_or] at h
    simp [h.1, h.2]

end GlobalTheory.FlagCell2.CellDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClassStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_base_form_times_fibre_class : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  first | exact @GlobalTheory.FlagCell2.CellDens.dens_cellForm | exact GlobalTheory.FlagCell2.CellDens.dens_cellForm | (intros; apply GlobalTheory.FlagCell2.CellDens.dens_cellForm <;> assumption)
end

module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AevalSingleZero
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem UpperTheory.ConvolutionTheory.FX.aeval_single_zero {ι ι' : Type} (q : ι → MvPolynomial ι' ℂ)
    (p : MvPolynomial ι ℂ) :
    aeval (fun i => (AddMonoidAlgebra.single 0 (q i) : EP ι')) p
      = (AddMonoidAlgebra.single 0 (aeval q p) : EP ι') := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, aeval_C]
    rfl
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr, AddMonoidAlgebra.single_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]

private theorem UpperTheory.ConvolutionTheory.FX.lin_delta {ι ι' : Type} [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (i : ι) :
    lin (fun j => if δ i = j then (1 : ℝ) else 0) = (X (δ i) : MvPolynomial ι' ℂ) := by
  unfold lin
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.lin_push {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) :
    lin (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0)) = rename δ (lin v) := by
  unfold lin
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, rename_C, rename_X,
    Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.ren_single {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    ren δ (AddMonoidAlgebra.single v p : EP ι) =
      (AddMonoidAlgebra.single (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0))
        (rename δ p) : EP ι') := by
  have h1 : (fun i => (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i) :
      MvPolynomial ι' ℂ)) = X ∘ δ := by
    funext i
    have := UpperTheory.ConvolutionTheory.FX.lin_delta δ i
    simp only [Pi.zero_apply, map_zero, zero_add, Function.comp]
    exact this
  unfold ren aff lift
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change aeval (fun i => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) +
      lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i)) : EP ι')) p *
    (AddMonoidAlgebra.single (Matrix.vecMul v _) (C (expChar 0 (Multiplicative.ofAdd v))) : EP ι') = _
  rw [UpperTheory.ConvolutionTheory.FX.aeval_single_zero, h1, AddMonoidAlgebra.single_mul_single, zero_add]
  have h2 : expChar (0 : ι → ℂ) (Multiplicative.ofAdd v) = 1 := by simp [expChar]
  rw [h2, map_one, mul_one, rename_eq_aeval]

theorem UpperTheory.ConvolutionTheory.FX.piece_ren :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (k : ℕ), piece k (ren δ f) = rename δ (piece k f) := by
  intro ι _ f ι' _ _ δ k
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  obtain ⟨ha', h0', hs'⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι' k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, h0, h0', map_zero]
  | add f g hf hg => rw [map_add (f := _), ha, ha', map_add (f := _), hf, hg]
  | single v p =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [UpperTheory.ConvolutionTheory.FX.ren_single, hs, hs', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_pow, rename_C, UpperTheory.ConvolutionTheory.FX.lin_push, rename_homogeneousComponent]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SubEqZeroIff
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ShiftPow
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private lemma shift_pow (c : ℂ) (k : ℕ) : ∀ (q : ℂ → ℂ),
    ((LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) - Complex.exp c • (1 : Module.End ℂ (ℂ → ℂ))) ^ k)
      (fun t => q t * Complex.exp (c * t)) =
      fun t => Complex.exp c ^ k * ((fwdDiff (1 : ℂ))^[k] q t * Complex.exp (c * t)) := by
  induction k with
  | zero => intro q; funext t; simp
  | succ k ih =>
    intro q
    have h1 : (LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) - Complex.exp c • (1 : Module.End ℂ (ℂ → ℂ)))
        (fun t => q t * Complex.exp (c * t)) =
        Complex.exp c • fun t => fwdDiff (1 : ℂ) q t * Complex.exp (c * t) := by
      funext t
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
        Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, fwdDiff, mul_add, mul_one, Complex.exp_add]
      ring
    rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih]
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, Function.iterate_succ_apply]
    ring

private lemma one_var {α : Type} [Fintype α] (c : α → ℝ) (hc : Function.Injective c)
    (q : α → Polynomial ℂ) (h : ∀ t : ℂ, ∑ a, (q a).eval t * Complex.exp (c a * t) = 0) (a : α) :
    (q a).eval 0 = 0 := by
  have hinj : Function.Injective fun a => Complex.exp (c a) := by
    intro a b hab
    apply hc
    apply Real.exp_injective
    simp only [← Complex.ofReal_exp] at hab
    exact_mod_cast hab
  have hind := (Module.End.independent_maxGenEigenspace
    (LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) : Module.End ℂ (ℂ → ℂ))).comp hinj
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hind
  have := hind Finset.univ (fun a t => (q a).eval t * Complex.exp (c a * t)) ?_ ?_ a (Finset.mem_univ a)
  · simpa using congrFun this 0
  · intro b _
    rw [Function.comp_apply, Module.End.mem_maxGenEigenspace]
    refine ⟨(q b).natDegree + 1, ?_⟩
    rw [shift_pow (c b) _ (fun t => (q b).eval t),
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (Nat.lt_succ_self _)]
    funext t
    simp
  · funext t
    simpa [Finset.sum_apply] using h t

private lemma ev_eq {ι : Type} [Fintype ι] (f : EP ι) (Λ : ι → ℂ) :
    ev Λ f = ∑ v ∈ f.coeff.support, eval Λ (f.coeff v) * Complex.exp (∑ i, (v i : ℂ) * Λ i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  change AddMonoidAlgebra.liftNC _ _ (AddMonoidAlgebra.single v _) = _
  rw [AddMonoidAlgebra.liftNC_single]
  rfl

private lemma generic {ι : Type} [Fintype ι] (s : Finset (ι → ℝ)) :
    ∃ u : ι → ℝ, Function.Injective fun v : s => ∑ i, v.1 i * u i := by
  classical
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (K := ℝ) (M := ι → ℝ)
    (ι := {p : s × s // p.1 ≠ p.2})
    (fun p => ∑ i, (p.1.1.1 i - p.1.2.1 i) • LinearMap.proj i) (by
      rintro ⟨⟨v, w⟩, hvw⟩
      obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ w.1 i := by
        by_contra hh
        push Not at hh
        exact hvw (Subtype.ext (funext hh))
      refine ⟨Pi.single i 1, ?_⟩
      simp [LinearMap.sum_apply, Pi.single_apply, sub_eq_zero, hi])
  refine ⟨u, fun v w hvw => ?_⟩
  by_contra hne
  apply hu ⟨(v, w), hne⟩
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hvw

theorem UpperTheory.ConvolutionTheory.FX.ev_inj :
    ∀ (ι : Type) [Fintype ι] (f : EP ι), (∀ Λ : ι → ℂ, ev Λ f = 0) → f = 0 := by
  intro ι _ f hf
  obtain ⟨u, hu⟩ := generic f.coeff.support
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  ext1 v
  by_contra hv
  apply hv
  have hv' : v ∈ f.coeff.support := Finsupp.mem_support_iff.2 hv
  refine MvPolynomial.funext fun Λ => ?_
  have hev : ∀ (p : MvPolynomial ι ℂ) (t : ℂ),
      Polynomial.eval t (aeval (fun i => Polynomial.C (Λ i) + Polynomial.C (u i : ℂ) * Polynomial.X) p) =
        eval (fun i => Λ i + (u i : ℂ) * t) p := by
    intro p t
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have key := one_var _ hu (fun w : f.coeff.support =>
    Polynomial.C (Complex.exp (∑ i, (w.1 i : ℂ) * Λ i)) *
      aeval (fun i => Polynomial.C (Λ i) + Polynomial.C (u i : ℂ) * Polynomial.X) (f.coeff w.1)) ?_ ⟨v, hv'⟩
  · rw [Polynomial.eval_mul, hev, Polynomial.eval_C] at key
    simpa using key
  · intro t
    have := hf (fun i => Λ i + (u i : ℂ) * t)
    rw [ev_eq, ← Finset.sum_coe_sort] at this
    rw [← this]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Polynomial.eval_mul, hev, Polynomial.eval_C]
    have : ∑ i, (w.1 i : ℂ) * (Λ i + (u i : ℂ) * t) =
        ∑ i, (w.1 i : ℂ) * Λ i + ((∑ i, w.1 i * u i : ℝ) : ℂ) * t := by
      push_cast
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    rw [this, Complex.exp_add]
    ring
end

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff :
    ∀ (ι κ : Type) [Fintype ι] (b : Fam ι κ) (F : KF ι κ), b.sub F = 0 ↔ ∀ Λ h, b.Mem Λ h → evK Λ h F = 0 := by
  intro ι κ _ b F
  have key : ∀ lam : Fin b.r → ℂ, ev lam (b.sub F) =
      evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) F := fun lam => by
    have : (ev lam).comp b.sub = evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) :=
      MvPolynomial.ringHom_ext (fun f => by
        simpa [Fam.sub, evK] using (UpperTheory.ConvolutionTheory.FX.subst ι _ b.Λ b.emb f).1 lam) (fun k => by simp [Fam.sub, evK])
    exact RingHom.congr_fun this F
  refine ⟨fun h0 Λ h ⟨lam, h1, h2⟩ => ?_, fun h => UpperTheory.ConvolutionTheory.FX.ev_inj _ _ fun lam => ?_⟩
  · rw [funext h1, funext h2, ← key, h0, map_zero]
  · rw [key]
    exact h _ _ ⟨lam, fun _ => rfl, fun _ => rfl⟩
end

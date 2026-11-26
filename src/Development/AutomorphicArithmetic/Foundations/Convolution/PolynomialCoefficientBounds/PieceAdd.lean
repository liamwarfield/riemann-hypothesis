module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebClosed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.piece_add :
    ∀ (ι : Type) [Fintype ι] (k : ℕ), (∀ f g : EP ι, piece k (f + g) = piece k f + piece k g) ∧ piece k (0 : EP ι) = 0 ∧ ∀ (v : ι → ℝ) (p : MvPolynomial ι ℂ), piece k (AddMonoidAlgebra.single v p : EP ι) = ∑ b ∈ Finset.range (k + 1), homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) := by
  intro ι _ k
  refine ⟨fun f g => ?_, ?_, fun v p => ?_⟩
  · unfold piece
    rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro a; simp
    · intro a b c; simp [add_mul, Finset.sum_add_distrib]
  · unfold piece
    simp
  · unfold piece
    rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx
open scoped ContDiff

theorem UpperTheory.ConvolutionTheory.FX.cheb_bound :
    ∀ (η : ℝ) (m : ℕ), 0 < η → η ≤ 1 → (∀ a ∈ Set.Icc 0 η, |cheb η m a| ≤ 1) ∧ (∀ a ∈ Set.Icc (0 : ℝ) 1, |cheb η m a| ≤ (4 / η) ^ m) ∧ ∃ q : Polynomial ℝ, q.natDegree ≤ m ∧ ∀ a, q.eval a = cheb η m a := by
  intro η m hη hη1
  have hA : ∀ a ∈ Set.Icc 0 η, |cheb η m a| ≤ 1 := by
    intro a ha
    unfold cheb
    refine (UpperTheory.ConvolutionTheory.FX.cheb_facts m _).1 ?_
    have h0 : 0 ≤ 2 * a / η := div_nonneg (by linarith [ha.1]) hη.le
    have h2 : 2 * a / η ≤ 2 := by
      rw [div_le_iff₀ hη]; linarith [ha.2]
    rw [abs_le]; constructor <;> linarith
  refine ⟨hA, ?_, ?_⟩
  · intro a ha
    by_cases h : a ≤ η
    · refine (hA a ⟨ha.1, h⟩).trans (one_le_pow₀ ?_)
      rw [le_div_iff₀ hη]; linarith
    · have h : η < a := lt_of_not_ge h
      have h2 : 2 ≤ 2 * a / η := by
        rw [le_div_iff₀ hη]; linarith
      have h3 : 2 * (2 * a / η) ≤ 4 / η := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith [ha.2]) hη.le
      unfold cheb
      refine ((UpperTheory.ConvolutionTheory.FX.cheb_facts m _).2 (by linarith)).2.trans ?_
      exact pow_le_pow_left₀ (by linarith) (by linarith) m
  · refine ⟨(Polynomial.Chebyshev.T ℝ (m : ℤ)).comp
      (Polynomial.C (2 / η) * Polynomial.X + Polynomial.C (-1)), ?_, ?_⟩
    · refine Polynomial.natDegree_comp_le.trans ?_
      rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
      calc m * _ ≤ m * 1 := Nat.mul_le_mul_left m Polynomial.natDegree_linear_le
        _ = m := Nat.mul_one m
    · intro a
      unfold cheb
      rw [Polynomial.eval_comp]
      congr 1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ExistsFinMap
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem exists_fin_map {α : Type} (s : Multiset α) (n : ℕ) (h : Multiset.card s = n) :
    ∃ x : Fin n → α, Finset.univ.val.map x = s := by
  induction s using Quotient.inductionOn with
  | h l =>
    have h' : l.length = n := by simpa using h
    subst h'
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

private theorem esymm_surj (n : ℕ) (y : Fin n → ℂ) :
    ∃ x : Fin n → ℂ, ∀ i : Fin n, aeval x (esymm (Fin n) ℂ (i + 1)) = y i := by
  set q : Polynomial ℂ :=
    ∑ j : Fin n, Polynomial.C ((-1) ^ (n - j) * y j.rev) * Polynomial.X ^ (j : ℕ) with hq
  have hqd : q.degree < n := Polynomial.degree_sum_fin_lt _
  set p : Polynomial ℂ := Polynomial.X ^ n + q with hp
  have hm : p.Monic := Polynomial.monic_X_pow_add hqd
  have hd : p.natDegree = n := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rwa [Polynomial.degree_X_pow]
  have hc : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨x, hx⟩ := exists_fin_map p.roots n (hc.trans hd)
  refine ⟨x, fun i => ?_⟩
  rw [aeval_esymm_eq_multiset_esymm, hx]
  have hi := i.2
  have h1 := Polynomial.coeff_eq_esymm_roots_of_card hc (k := (i.rev : ℕ)) (by rw [hd]; exact i.rev.2.le)
  have e : n - (i.rev : ℕ) = i + 1 := by rw [Fin.val_rev]; omega
  have h2 : p.coeff (i.rev : ℕ) = (-1) ^ ((i : ℕ) + 1) * y i := by
    rw [hp, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg i.rev.2.ne, zero_add, hq,
      Polynomial.finsetSum_coeff, Finset.sum_eq_single i.rev]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, e, Fin.rev_rev]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun h => hb (Fin.ext h.symm))]
    · simp
  rw [hd, e, hm.leadingCoeff, one_mul, h2] at h1
  exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h1).symm

theorem UpperTheory.ConvolutionTheory.FX.blockE_inj :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), Function.Injective (aeval (blockE (τ := τ) (n := n)) : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ) := by
  intro τ _ _ n G H hGH
  apply MvPolynomial.funext
  intro y
  choose x hx using fun t : τ => esymm_surj n (fun i => y (t, i))
  have key : ∀ P : MvPolynomial (τ × Fin n) ℂ,
      aeval (fun ti : τ × Fin n => x ti.1 ti.2) (aeval (blockE (τ := τ) (n := n)) P) = eval y P := by
    intro P
    have hf : (fun ti : τ × Fin n => aeval (fun ti : τ × Fin n => x ti.1 ti.2) (blockE ti)) = y := by
      funext ⟨t, i⟩
      rw [blockE, aeval_rename]
      exact hx t i
    rw [← AlgHom.comp_apply, comp_aeval, hf]
    rfl
  rw [← key, ← key, hGH]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem hom_ext {ι A : Type} [CommRing A] (f g : EP ι →+* A)
    (h1 : ∀ c : ℂ, f (AddMonoidAlgebra.single 0 (C c)) = g (AddMonoidAlgebra.single 0 (C c)))
    (h2 : ∀ i, f (AddMonoidAlgebra.single 0 (X i)) = g (AddMonoidAlgebra.single 0 (X i)))
    (h3 : ∀ v, f (AddMonoidAlgebra.single v 1) = g (AddMonoidAlgebra.single v 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun p => ?_) h3
  have : f.comp (AddMonoidAlgebra.singleZeroRingHom) = g.comp AddMonoidAlgebra.singleZeroRingHom :=
    MvPolynomial.ringHom_ext (fun c => h1 c) (fun i => h2 i)
  exact RingHom.congr_fun this p

theorem UpperTheory.ConvolutionTheory.FX.subst :
    PositivityTheory.Rg.Fx.Subst := by
  intro ι ι' _ _ Λ₀ M f
  refine ⟨fun lam => ?_, fun ι'' _ Λ₁ N => ?_⟩
  · refine RingHom.congr_fun (hom_ext ((ev lam).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, ev, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      simp [aff, ev, lift_single, lin]
    · intro v
      simp only [aff, ev, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ← Complex.exp_add]
      congr 1
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
  · refine RingHom.congr_fun (hom_ext ((aff Λ₁ N).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      have e : ∀ p : MvPolynomial ι' ℂ, aeval (fun j => (AddMonoidAlgebra.single 0 (C (Λ₁ j) + lin (N j)) : EP ι'')) p =
          AddMonoidAlgebra.single 0 (aeval (fun j => (C (Λ₁ j) + lin (N j) : MvPolynomial ι'' ℂ)) p) := fun p => by
        induction p using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap]
        | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, AddMonoidAlgebra.single_add]
        | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
      simp only [aff, lift_single, RingHom.comp_apply, aeval_X, ofAdd_zero, map_one, mul_one, e]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lin, map_add (f := _), map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, add_assoc]
      rw [Finset.sum_comm (s := (Finset.univ : Finset ι''))]
    · intro v
      simp only [aff, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add,
        algebraMap_eq, ← C_mul, ← Complex.exp_add, Matrix.vecMul_vecMul]
      congr 3
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Reduce
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private noncomputable def nrm {ι : Type} (p : MvPolynomial ι ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖p.coeff α‖

private theorem nrm_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ nrm p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem nrm_add {ι : Type} (p q : MvPolynomial ι ℂ) : nrm (p + q) ≤ nrm p + nrm q :=
  (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).1

private theorem nrm_mul {ι : Type} (p q : MvPolynomial ι ℂ) : nrm (p * q) ≤ nrm p * nrm q :=
  (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem nrm_monomial {ι : Type} (a : ι →₀ ℕ) (c : ℂ) :
    nrm (monomial a c : MvPolynomial ι ℂ) = ‖c‖ :=
  (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι 0 0).2.2.2.1 a c

private def FXRep {ι B : Type} [Fintype B] (φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ)
    (m : B → MvPolynomial ι ℂ) (p : MvPolynomial ι ℂ) (d : ℕ) (c : ℝ) : Prop :=
  ∃ G : B → MvPolynomial ι ℂ, p = ∑ β, φ (G β) * m β ∧ ∑ β, nrm (G β) ≤ c ∧ ∀ β, (G β).totalDegree ≤ d

section
variable {ι B : Type} [Fintype B] {φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ}
  {m : B → MvPolynomial ι ℂ}

private theorem FXRep.mono {p c d e e'} (h : FXRep φ m p e c) (hcd : c ≤ d) (he : e ≤ e') : FXRep φ m p e' d := by
  obtain ⟨G, h1, h2, h3⟩ := h
  exact ⟨G, h1, h2.trans hcd, fun β => (h3 β).trans he⟩

private theorem FXRep.add {p q c d e} (h : FXRep φ m p e c) (h' : FXRep φ m q e d) :
    FXRep φ m (p + q) e (c + d) := by
  obtain ⟨G, h1, h2, h3⟩ := h
  obtain ⟨G', h1', h2', h3'⟩ := h'
  refine ⟨fun β => G β + G' β, ?_, ?_, fun β => (totalDegree_add _ _).trans (max_le (h3 β) (h3' β))⟩
  · rw [h1, h1', ← Finset.sum_add_distrib]
    simp only [map_add (f := _), add_mul]
  · refine (Finset.sum_le_sum fun β _ => nrm_add _ _).trans ?_
    rw [Finset.sum_add_distrib]
    linarith

private theorem FXRep.sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) (c : κ → ℝ) {e : ℕ}
    (h : ∀ i ∈ s, FXRep φ m (f i) e (c i)) : FXRep φ m (∑ i ∈ s, f i) e (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp [nrm], by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem FXRep.smul {p c e e'} (g : MvPolynomial ι ℂ) (hg : g.totalDegree ≤ e') (h : FXRep φ m p e c) :
    FXRep φ m (φ g * p) (e' + e) (nrm g * c) := by
  obtain ⟨G, h1, h2, h3⟩ := h
  refine ⟨fun β => g * G β, ?_, ?_, fun β => (totalDegree_mul _ _).trans (add_le_add hg (h3 β))⟩
  · rw [h1, Finset.mul_sum]
    simp only [map_mul, mul_assoc]
  · refine (Finset.sum_le_sum fun β _ => nrm_mul _ _).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h2 (nrm_nonneg g)

private theorem FXRep.basis (β : B) : FXRep φ m (m β) 0 1 := by
  classical
  refine ⟨fun γ => if γ = β then 1 else 0, ?_, ?_, fun γ => by dsimp only; split_ifs <;> simp⟩
  · rw [Finset.sum_eq_single β] <;> simp +contextual
  · rw [Finset.sum_eq_single β]
    · have := nrm_monomial (0 : ι →₀ ℕ) 1
      simp only [monomial_zero', C_1, norm_one] at this
      simp [this]
    · intro b _ hb
      simp [hb, nrm]
    · simp

private theorem FXRep.mul_left {p c e} (x : MvPolynomial ι ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hx : ∀ β, FXRep φ m (x * m β) 1 K) (h : FXRep φ m p e c) : FXRep φ m (x * p) (e + 1) (K * c) := by
  obtain ⟨G, h1, h2, hd⟩ := h
  have h3 := FXRep.sum Finset.univ _ _ fun β _ => (hx β).smul (G β) (hd β)
  have h4 : x * p = ∑ β, φ (G β) * (x * m β) := by
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  rw [h4]
  refine h3.mono ?_ le_rfl
  rw [← Finset.sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h2 hK

end

private theorem vieta (n : ℕ) (j : Fin n) :
    (X j : MvPolynomial (Fin n) ℂ) ^ n =
      ∑ i : Fin n, C (-(-1) ^ n * (-1) ^ (n - (i + 1)) : ℂ) * esymm (Fin n) ℂ (i + 1) *
        X j ^ (n - (i + 1)) := by
  have h := congrArg (Polynomial.eval (-(X j : MvPolynomial (Fin n) ℂ)))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp),
    Polynomial.eval_finsetSum, Fintype.card_fin, Finset.sum_range_succ',
    Finset.sum_range] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    esymm_zero, one_mul, Nat.sub_zero] at h
  have h2 : (X j : MvPolynomial (Fin n) ℂ) ^ n = (-1) ^ n * (-X j) ^ n := by
    rw [← mul_pow]; simp
  have h3 := eq_neg_of_add_eq_zero_right h.symm
  rw [h2, h3, mul_neg, ← neg_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow (X j : MvPolynomial (Fin n) ℂ)]
  simp only [map_mul, map_neg, map_pow, map_one]
  ring

private theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (β : ι → Fin n)
    (u : ι) (k : Fin n) :
    (∏ v, (X v : MvPolynomial ι ℂ) ^ (Function.update β u k v : ℕ)) =
      X u ^ (k : ℕ) * ∏ v ∈ Finset.univ.erase u, X v ^ (β v : ℕ) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

private theorem step (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (u : τ × Fin n)
    (β : τ × Fin n → Fin n) :
    FXRep (aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
      (fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
      (X u * ∏ v, X v ^ (β v : ℕ)) 1 ((n : ℝ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u), ← mul_assoc, ← pow_succ']
  by_cases h : (β u : ℕ) + 1 < n
  · have := prod_update β u ⟨_, h⟩
    simp only at this
    rw [← this]
    exact (FXRep.basis _).mono (by linarith [Nat.cast_nonneg (α := ℝ) n]) (Nat.zero_le _)
  · have hn : (β u : ℕ) + 1 = n := by have := (β u).2; omega
    have hv := congrArg (rename (fun j => (u.1, j))) (vieta n u.2)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_pow, rename_X, map_sum, map_mul, Prod.mk.eta, rename_C] at hv
    rw [hn, hv, Finset.sum_mul]
    have key := FXRep.sum (φ := aeval (fun ti : τ × Fin n =>
        rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
      (m := fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
      (Finset.univ : Finset (Fin n)) _ _ fun i _ =>
        (FXRep.basis (Function.update β u i.rev)).smul
          (e' := 1) (monomial (Finsupp.single (u.1, i) 1) (-(-1) ^ n * (-1) ^ (n - (i + 1)) : ℂ))
          ((totalDegree_monomial_le _ _).trans (by simp))
    refine FXRep.mono (c := ∑ i : Fin n, _) (Eq.mpr (congrArg (FXRep _ _ · _ _) ?_) key) ?_ le_rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [prod_update, Fin.val_rev]
      rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, algebraMap_eq]
      simp only [mul_assoc, map_mul, map_pow]
    · simp only [nrm_monomial]
      simp

theorem UpperTheory.ConvolutionTheory.FX.reduce :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), ∃ K : ℝ, 1 ≤ K ∧ ∀ α : τ × Fin n →₀ ℕ, ∃ G : (τ × Fin n → Fin n) → MvPolynomial (τ × Fin n) ℂ, (monomial α (1 : ℂ) = ∑ β, aeval blockE (G β) * ∏ u, X u ^ (β u : ℕ)) ∧ ∑ β, l1 (G β) ≤ K ^ α.degree ∧ ∀ β, (G β).totalDegree ≤ α.degree := by
  intro τ _ _ n
  have hK : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨(n : ℝ) + 1, by linarith, fun α => ?_⟩
  change FXRep (aeval (fun ti : τ × Fin n =>
      rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
    (fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
    (monomial α 1) α.degree (((n : ℝ) + 1) ^ α.degree)
  induction α using Finsupp.induction with
  | zero =>
    have := FXRep.basis (φ := aeval (fun ti : τ × Fin n =>
        rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
      (m := fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
      (fun u => ⟨0, u.2.pos⟩)
    simpa using this
  | single_add a b f _ _ ih =>
    rw [monomial_single_add, map_add (f := _), Finsupp.degree_single, pow_add]
    clear * - ih hK
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      rw [pow_succ', pow_succ', mul_assoc, mul_assoc]
      exact (ihb.mul_left _ _ (by linarith) (step τ n a)).mono le_rfl (by omega)
end

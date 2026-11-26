module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem sum_words_eq_sum_multinomial {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [AddCommGroup D] [Module ℂ D] (k : ℕ) (G : (I →₀ ℕ) → D) :
    ∑ s : Fin k → I, G (∑ a, Finsupp.single (s a) 1) =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • G m := by
  let ℓ : MvPolynomial I ℂ →ₗ[ℂ] D := (MvPolynomial.basisMonomials I ℂ).constr ℂ G
  have hℓ : ∀ m, ℓ (MvPolynomial.monomial m 1) = G m := fun m => by
    have := (MvPolynomial.basisMonomials I ℂ).constr_basis ℂ G m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h1 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ s : Fin k → I, MvPolynomial.monomial (∑ a, Finsupp.single (s a) 1) 1 := by
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.monomial_sum_one]
    rfl
  have h2 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • MvPolynomial.monomial m 1 := by
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    symm
    refine Finset.sum_nbij' (fun m => (m : I → ℕ)) (fun m => Finsupp.equivFunOnFinite.symm m)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simpa using hm
    · intro m hm
      simpa using hm
    · intro m _
      simp
    · intro m _
      simp
    · intro m _
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Nat.cast_smul_eq_nsmul,
        nsmul_eq_mul]
      simp
  have h := congrArg ℓ (h1.symm.trans h2)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_smul, hℓ] using h

theorem iteratedFDeriv_word_eq_coeff {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (s : Fin k → I) :
    iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) =
      ((∏ i, ((∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i).factorial : ℕ) : ℂ) *
        MvPowerSeries.coeff (∑ a, Finsupp.single (s a) 1) (GlobalTheory.taylor f) := by
  have hl : ((List.ofFn s : List I) : Multiset I) =
      Finsupp.toMultiset (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map s _),
      Multiset.map_map]
    rfl
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, List.map_ofFn,
    GlobalTheory.lineDerivList_ofFn hf, mul_inv_cancel_left₀ (GlobalTheory.cast_prod_factorial_ne_zero _)]
  rfl

theorem taylor_eq_sum_coeff_taylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 →
    GlobalTheory.PeriodFamily.taylor N t f = ∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m (GlobalTheory.taylor f) • ∏ i, t i ^ m i := by
  intro I _ _ D _ _ N t f hf
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp : ∀ s : Fin k → I, ∏ a, t (s a) =
      ∏ i, t i ^ (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i := fun s => by
    simp only [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Finsupp.single_apply]
  simp only [iteratedFDeriv_word_eq_coeff hf, hp]
  rw [sum_words_eq_sum_multinomial k fun m : I →₀ ℕ =>
    ((k.factorial : ℂ)⁻¹ * (((∏ i, (m i).factorial : ℕ) : ℂ) *
      MvPowerSeries.coeff m (GlobalTheory.taylor f))) • ∏ i, t i ^ m i]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hk : ∑ i, m i = k := (Finset.mem_finsuppAntidiag.1 hm).1
  have hs : ((∏ i, (m i).factorial : ℕ) : ℂ) * (Nat.multinomial Finset.univ m : ℂ) =
      (k.factorial : ℂ) := by
    rw [← Nat.cast_mul, Nat.multinomial_spec, hk]
  have h0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, ← mul_assoc, mul_right_comm _ _ ((∏ i, (m i).factorial : ℕ) : ℂ),
    mul_comm (Nat.multinomial _ _ : ℂ), hs, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfComap
open Filter Topology

namespace GlobalTheory
namespace SquareZeroSum

open TrivSqZeroExt

theorem isNilpotent_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B)
    (hI : IsNilpotent I) (hf : ∀ x y, f x = 0 → f y = 0 → x * y = 0) :
    IsNilpotent (I.comap f) := by
  obtain ⟨m, hm⟩ := hI
  have h1 : (I.comap f) ^ m ≤ RingHom.ker f := by
    have := Ideal.le_comap_pow f (K := I) m
    rw [hm] at this
    exact this
  refine ⟨m + m, ?_⟩
  rw [pow_add, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  exact (Submodule.mem_bot _).2 (hf r s (h1 hr) (h1 hs))

theorem isNilpotent_of_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal B) (hI : IsNilpotent (I.comap f)) :
    IsNilpotent I := by
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, ?_⟩
  rw [← Ideal.map_comap_of_surjective f hf I, ← Ideal.map_pow, hm]
  simp

section
variable {K : Type} [Fintype K] [DecidableEq K] {D : Type} [CommRing D] (δ : K → D)

theorem prod_fst_snd {ι : Type} [DecidableEq ι] (s : ι → K) (t : Finset ι) :
    (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))).fst
        = ∏ a ∈ t, δ (s a) ∧
      ∑ k, (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
          - inr (Pi.single (s a) 1))).snd k * δ k = -(t.card : D) * ∏ a ∈ t, δ (s a) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    generalize (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
      - inr (Pi.single (s a) 1))) = P at h1 h2 ⊢
    refine ⟨by simp [h1], ?_⟩
    have h3 : ∀ k, ((((inl (δ (s a)) : TrivSqZeroExt D (K → D))
        - inr (Pi.single (s a) 1))) * P).snd k * δ k
        = δ (s a) * (P.snd k * δ k) - P.fst * ((Pi.single (s a) 1 : K → D) k * δ k) := by
      intro k
      simp [snd_mul]
      ring
    simp only [h3, Finset.sum_sub_distrib, ← Finset.mul_sum, h2, h1]
    simp [Pi.single_apply]
    ring

end

theorem step (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (δ : K → D) (hπ : IsNilpotent (RingHom.ker π)) (hδ : ∀ a, π (δ a) = 0)
    (hs : ∀ s : Fin (N + 1 + 1) → K, ∏ a, δ (s a) = 0) :
    ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ)
      (ν : K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ a, π' (ν a) = 0) ∧ (∀ a b, ν a * ν b = 0) ∧
      ∀ s : Fin (N + 1) → K, ∏ a, (ι (δ (s a)) - ν (s a)) = 0 := by
  classical
  let g : (Fin (N + 1) → K) → TrivSqZeroExt D (K → D) := fun s =>
    ∏ a, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))
  let Q : Ideal (TrivSqZeroExt D (K → D)) := Ideal.span (Set.range g)
  let E : TrivSqZeroExt D (K → D) → D := fun x => ((N + 1 : ℕ) : D) * x.fst + ∑ k, x.snd k * δ k
  have hEadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    simp only [E, fst_add, snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  have hg : ∀ s c, E (c * g s) = 0 := by
    intro s c
    obtain ⟨h1, h2⟩ := prod_fst_snd δ s Finset.univ
    change (g s).fst = _ at h1
    change ∑ k, (g s).snd k * δ k = _ at h2
    have h3 : ∀ k, (c * g s).snd k * δ k
        = c.fst * ((g s).snd k * δ k) + c.snd k * (δ k * ∏ a, δ (s a)) := by
      intro k
      simp [snd_mul, h1]
      ring
    have h4 : ∀ k, δ k * ∏ a, δ (s a) = 0 := by
      intro k
      have := hs (Fin.cons k s)
      rw [Fin.prod_univ_succ] at this
      simpa using this
    simp only [E, h3, h4, mul_zero, add_zero, ← Finset.mul_sum, h2, fst_mul, h1,
      Finset.card_univ, Fintype.card_fin]
    ring
  have hQ : ∀ x ∈ Q, ∀ c, E (c * x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hg s
    | zero => intro c; simp [E]
    | add x y _ _ hx hy => intro c; rw [mul_add, hEadd, hx, hy, add_zero]
    | smul a x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  let p : TrivSqZeroExt D (K → D) →ₐ[ℂ] ℂ := π.comp (fstHom ℂ D (K → D))
  have hp : ∀ x ∈ Q, p x = 0 := by
    have : Q ≤ RingHom.ker p := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      have h1 : (g s).fst = _ := (prod_fst_snd δ s Finset.univ).1
      simp [p, h1, hδ, map_prod]
    exact this
  refine ⟨TrivSqZeroExt D (K → D) ⧸ Q, inferInstance, inferInstance,
    (Ideal.Quotient.mkₐ ℂ Q).comp (inlAlgHom ℂ D (K → D)), Ideal.Quotient.liftₐ Q p hp,
    fun a => Ideal.Quotient.mk Q (inr (Pi.single a 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro d hd
    have hd' : (inl d : TrivSqZeroExt D (K → D)) ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 hd
    have h := hQ _ hd' 1
    simp only [E, one_mul, fst_inl, snd_inl, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero] at h
    have hu : IsUnit ((N + 1 : ℕ) : D) := by
      rw [← map_natCast (algebraMap ℂ D)]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N))).map _
    exact hu.mul_right_eq_zero.1 h
  · intro d
    rfl
  · refine isNilpotent_of_comap (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective _ ?_
    have := isNilpotent_comap (fstHom ℂ D (K → D)).toRingHom _ hπ (by
      intro x y hx hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      ext1 <;> simp [snd_mul, hx', hy'])
    exact this
  · intro a
    change p (inr _) = 0
    simp [p]
  · intro a b
    rw [← map_mul, inr_mul_inr, map_zero]
  · intro s
    have : Ideal.Quotient.mk Q (g s) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨s, rfl⟩)
    rw [← this]
    simp only [g, map_prod, map_sub]
    rfl

theorem exists_sum_sq_zero : ∀ (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (δ : K → D), IsNilpotent (RingHom.ker π) → (∀ a, π (δ a) = 0) → (∀ s : Fin (N + 1) → K, ∏ a, δ (s a) = 0) → ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ) (n : Fin N → K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧ IsNilpotent (RingHom.ker π') ∧ (∀ j a, π' (n j a) = 0) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, ι (δ a) = ∑ j, n j a := by
  intro N
  induction N with
  | zero =>
    intro K _ D _ _ π δ hπ hδ hs
    refine ⟨D, inferInstance, inferInstance, AlgHom.id ℂ D, π, fun j => j.elim0,
      Function.injective_id, fun _ => rfl, hπ, fun j => j.elim0, fun j => j.elim0, ?_⟩
    intro a
    simpa using hs (fun _ => a)
  | succ N ih =>
    intro K _ D _ _ π δ hπ hδ hs
    obtain ⟨D₁, _, _, ι₁, π₁, ν, hi₁, hc₁, hn₁, hν, hνν, hs₁⟩ := step N D π δ hπ hδ hs
    obtain ⟨D₂, _, _, ι₂, π₂, n, hi₂, hc₂, hn₂, hn, hnn, hsum⟩ :=
      ih D₁ π₁ (fun a => ι₁ (δ a) - ν a) hn₁ (fun a => by simp [hc₁, hδ, hν]) hs₁
    refine ⟨D₂, inferInstance, inferInstance, ι₂.comp ι₁, π₂,
      Fin.cons (fun a => ι₂ (ν a)) n, hi₂.comp hi₁, fun d => by simp [hc₂, hc₁], hn₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases (fun a => ?_) (fun j a => ?_) j
      · simp [hc₂, hν]
      · simp [hn]
    · intro j
      refine Fin.cases (fun a b => ?_) (fun j a b => ?_) j
      · simp [← map_mul, hνν]
      · simp [hnn]
    · intro a
      rw [Fin.sum_univ_succ]
      simp [← hsum]

end SquareZeroSum
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.CechDescHInv

theorem yoneda_spec_widePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) :=
  GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda A B T a k ι hι hu

theorem tensor_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem poly_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (Polynomial B →+* R))
    (hg : ∀ j, (g j).comp (Polynomial.mapRingHom a) = (g 0).comp (Polynomial.mapRingHom a)) :
    ∃! φ : Polynomial T →+* R, ∀ j, φ.comp (Polynomial.mapRingHom (ι j)) = g j := by
  have hX : ∀ j, g j Polynomial.X = g 0 Polynomial.X := fun j => by
    have := RingHom.congr_fun (hg j) Polynomial.X
    simpa using this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp Polynomial.C) (fun j => by
    ext x
    have := RingHom.congr_fun (hg j) (Polynomial.C x)
    simpa using this)
  refine ⟨Polynomial.eval₂RingHom ψ (g 0 Polynomial.X), fun j => ?_, fun φ hφ => ?_⟩
  · apply Polynomial.ringHom_ext
    · intro b
      simpa using RingHom.congr_fun (hψ j) b
    · simp [hX j]
  · have hC : φ.comp Polynomial.C = ψ := hψu _ (fun j => by
      ext b
      simpa using RingHom.congr_fun (hφ j) (Polynomial.C b))
    apply Polynomial.ringHom_ext
    · intro t
      simpa using RingHom.congr_fun hC t
    · simpa using RingHom.congr_fun (hφ 0) Polynomial.X

theorem spec_integral_surj (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral)
    (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩
  exact this

theorem poly_isIntegral (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral) :
    (Polynomial.mapRingHom φ).IsIntegral := by
  letI := (Polynomial.mapRingHom φ).toAlgebra
  have hC : ∀ b : B, IsIntegral (Polynomial A) (Polynomial.C b) := by
    intro b
    obtain ⟨f, hf, hfb⟩ := hi b
    refine ⟨f.map Polynomial.C, hf.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (Polynomial A) (Polynomial B)).comp Polynomial.C = Polynomial.C.comp φ := by
      ext x <;> simp [RingHom.algebraMap_toAlgebra]
    rw [e, ← Polynomial.hom_eval₂, hfb, map_zero]
  have hXi : IsIntegral (Polynomial A) (Polynomial.X : Polynomial B) := by
    have : (Polynomial.X : Polynomial B) = algebraMap (Polynomial A) (Polynomial B) Polynomial.X := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [this]; exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C b => exact hC b
  | add p r hp hr => exact hp.add hr
  | monomial n b _ => exact (hC b).mul (hXi.pow _)

theorem poly_ker (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hk : RingHom.ker φ ≤ nilradical A) :
    RingHom.ker (Polynomial.mapRingHom φ) ≤ nilradical (Polynomial A) := by
  intro p hp
  rw [mem_nilradical, Polynomial.isNilpotent_iff]
  intro n
  rw [← mem_nilradical]
  apply hk
  rw [RingHom.mem_ker] at hp ⊢
  have := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r n) hp
  simpa using this

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem hInv_of_integral (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) →
    (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  intro hint hker hq hT i
  have hi : (algebraMap A B).IsIntegral := fun x => hint.isIntegral x
  obtain ⟨hf1, hf2⟩ := spec_integral_surj A B (algebraMap A B) hi hker
  obtain ⟨hf1', hf2'⟩ := spec_integral_surj _ _ (Polynomial.mapRingHom (algebraMap A B))
    (poly_isIntegral A B _ hi) (poly_ker A B _ hker)
  have hq' : IsUnit (q : Polynomial A) := by simpa using hq.map (Polynomial.C : A →+* Polynomial A)
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (algebraMap A B))) (isUnit_gamma q A hq) i
  have h1' := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))
    (isUnit_gamma q _ hq') i
  let F : Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
    Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
      (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))) (by
        simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext x <;> simp)
  let m : cech (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ⟶
      cech (Spec.map (CommRingCat.ofHom (algebraMap A B))) := Arrow.mapCechNerve F
  have hsq : m ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
        spMap (Polynomial.C : A →+* Polynomial A) := by
    clear E h1 h1' hT hf1 hf2 hf1' hf2' hint hker hq hq' hi
    refine NatTrans.ext (funext fun n => ?_)
    change WidePullback.lift _ _ _ ≫ WidePullback.base _ = WidePullback.base _ ≫ yoneda.map (Spec.map _)
    apply WidePullback.lift_base
  have hm : Eqv _ m (tw q i) := by
    refine GlobalTheory.T.levelwiseEquivalence_isEquivalence _ m _ (fun n => ?_)
    clear h1 h1' hf1 hf2 hf1' hf2' hint hker hq hq' hi hsq
    set k := n.unop.len
    let T := PiTensorProduct A (fun _ : Fin (k + 1) => B)
    let ι : Fin (k + 1) → (B →+* T) := fun j =>
      (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom
    have hι : ∀ j, (ι j).comp (algebraMap A B) = (ι 0).comp (algebraMap A B) := by
      intro j; ext x; simp [ι]
    have hu := tensor_univ A B k
    obtain ⟨e, he⟩ := yoneda_spec_widePullback A B T (algebraMap A B) k ι hι hu
    have hι' : ∀ j, (Polynomial.mapRingHom (ι j)).comp (Polynomial.mapRingHom (algebraMap A B)) =
        (Polynomial.mapRingHom (ι 0)).comp (Polynomial.mapRingHom (algebraMap A B)) := by
      intro j; rw [Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp, hι j]
    obtain ⟨e', he'⟩ := yoneda_spec_widePullback (Polynomial A) (Polynomial B) (Polynomial T)
      (Polynomial.mapRingHom (algebraMap A B)) k (fun j => Polynomial.mapRingHom (ι j)) hι'
      (poly_univ A B T (algebraMap A B) k ι (fun R _ g hg => hu R g hg))
    let mn : widePullback (yoneda.obj (Spec (CommRingCat.of (Polynomial A))))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of (Polynomial B))))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
        widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
      WidePullback.lift (WidePullback.base _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))))
        (fun j => WidePullback.π _ j ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
        (fun j => by
          rw [Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← WidePullback.π_arrow _ j, Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 4
          ext x <;> simp)
    have hmn : m.app n = mn := rfl
    have hπ : ∀ j, (e'.hom ≫ mn) ≫ WidePullback.π _ j =
        (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom) ≫ WidePullback.π _ j := by
      intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, he' j, Category.assoc, he j,
        ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Functor.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
      ext x <;> simp
    have key : e'.hom ≫ mn = yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom := by
      apply WidePullback.hom_ext
      · exact hπ
      · rw [← WidePullback.π_arrow _ 0, ← Category.assoc, ← Category.assoc, hπ 0]
    have h3 : Eqv _ (disc.map e'.hom ≫ disc.map mn) (tw q i) := by
      rw [← Functor.map_comp, key, Functor.map_comp]
      exact (E.2.1 _ _ _ _ _).1 (hT k i) (E.1 _ _ _ (disc.mapIso e).isIso_hom)
    rw [hmn]
    exact (E.2.1 _ _ _ _ _).2.1 (E.1 _ _ _ (disc.mapIso e').isIso_hom) h3
  have h2 : Eqv _ (cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
      spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
    rw [← hsq]; exact (E.2.1 _ _ _ _ _).1 hm h1
  exact (E.2.1 _ _ _ _ _).2.1 h1' h2

end GlobalTheory.EtC.CechDescHInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) → (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  first | (exact @GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (exact GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (intros; apply GlobalTheory.EtC.CechDescHInv.hInv_of_integral  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAutCentre
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.ThmAMove

section Val

variable {K : Type} [Field K] (A : ValuationSubring K)

theorem exists_ext {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [IsAlgClosed K] (jk : FractionRing R →+* K) :
    ∃ je : FractionRing S →+* K, ∀ x, je (IsFractionRing.map (j := algebraMap R S) hinj x) = jk x := by
  let k : FractionRing R →+* FractionRing S := IsFractionRing.map (j := algebraMap R S) hinj
  letI : Algebra (FractionRing R) (FractionRing S) := k.toAlgebra
  letI : Algebra (FractionRing R) K := jk.toAlgebra
  have hi : ∀ a : S, IsIntegral (FractionRing R) (algebraMap S (FractionRing S) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap R (FractionRing R)) (algebraMap S (FractionRing S))
      (RingHom.ext fun r => by
        show k (algebraMap R _ r) = _
        simp [k, IsFractionRing.map]) (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    rw [div_eq_mul_inv]
    exact ((hi a).mul (hi b).inv).isAlgebraic⟩
  let j : FractionRing S →ₐ[FractionRing R] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨j.toRingHom, fun x => j.commutes x⟩

theorem exists_unit {S : Type} [CommRing S] [IsDomain S] [ValuationRing S] (je : FractionRing S →+* K)
    (hA : ∀ a : S, je (algebraMap S _ a) ∈ A) (hu : ∀ a : S, A.valuation (je (algebraMap S _ a)) = 1 → IsUnit a)
    {x y : FractionRing S} (h : A.valuation (je x) = A.valuation (je y)) : ∃ u : Sˣ, x = algebraMap S _ (u : S) * y := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨1, ?_⟩
    simpa using h
  have hy' : A.valuation (je y) ≠ 0 := by simpa using hy
  have h1 : A.valuation (je (x / y)) = 1 := by rw [map_div₀, map_div₀, h, div_self hy']
  rcases ValuationRing.isInteger_or_isInteger S (x / y) with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, h1])
    exact ⟨u, by rw [ha, div_mul_cancel₀ _ hy]⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, map_inv₀, map_inv₀, h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, ha, inv_inv, div_mul_cancel₀ _ hy]

theorem mem_max_iff {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : R →+* K) (hf : ∀ r, f r ∈ A) {l : ℕ}
    (hl0 : (l : K) ≠ 0) (hl : A.valuation (l : K) < 1) (a : R) :
    a ∈ IsLocalRing.maximalIdeal R ↔ A.valuation (f a) < 1 := by
  have hle : ∀ r, A.valuation (f r) ≤ 1 := fun r => (A.valuation_le_one_iff _).2 (hf r)
  constructor
  · intro ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have h0 : (l : R) ≠ 0 := fun h => hl0 (by rw [← map_natCast f, h, map_zero])
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    have hd : (l : R) ∣ a ^ n := by
      rw [hn, Units.mul_left_dvd]
      exact pow_dvd_pow_of_dvd ha n
    obtain ⟨c, hc⟩ := hd
    refine lt_of_le_of_ne (hle a) fun h1 => ?_
    have h2 := congrArg (fun r => A.valuation (f r)) hc
    simp only [map_pow, map_mul, map_natCast, h1, one_pow] at h2
    exact absurd h2 (mul_lt_one_of_lt_of_le hl (hle c)).ne'
  · intro h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h2 : A.valuation (f u) * A.valuation (f (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_lt_of_le h (hle _)).ne

variable {L : Type} [Field L] [NumberField L]

theorem int_le_one (β : L →+* K) (x : 𝓞 L) : A.valuation (β x) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  have h : IsIntegral A (β x) := IsIntegral.map_of_comp_eq (Int.castRingHom A) β (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact hy ▸ y.2

theorem unit_of_centre (β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) (h : ∀ x : 𝓞 L, A.valuation (β x) < 1 ↔ x ∈ P.asIdeal)
    (y : L) (hy : P.valuation L y = 1) : A.valuation (β y) = 1 := by
  obtain ⟨n, d, e⟩ := P.exists_primeCompl_mul_eq_of_integer y hy.le
  have h1 : ∀ x : 𝓞 L, x ∉ P.asIdeal → A.valuation (β x) = 1 := fun x hx =>
    le_antisymm (int_le_one A β x) (not_lt.1 fun h' => hx ((h x).1 h'))
  have hd : P.valuation L (algebraMap (𝓞 L) L d) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 d.2
  have hn : n ∉ P.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    show P.valuation L (algebraMap (𝓞 L) L n) = 1
    rw [← e, map_mul, hy, hd, one_mul]
  have h2 := congrArg (fun r => A.valuation (β r)) e
  simp only [map_mul] at h2
  rw [show A.valuation (β (algebraMap (𝓞 L) L d)) = 1 from h1 _ d.2, show A.valuation (β (algebraMap (𝓞 L) L n)) = 1 from h1 _ hn,
    mul_one] at h2
  exact h2

theorem val_eq_of_unit (α β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) {l : ℕ} (hl0 : l ≠ 0) (hl : P.valuation L (l : L) ≠ 1)
    (hα : ∀ y, P.valuation L y = 1 → A.valuation (α y) = 1) (hβ : ∀ y, P.valuation L y = 1 → A.valuation (β y) = 1) (x : L) :
    A.valuation (α x) = A.valuation (β x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hl1 : (l : L) ≠ 0 := Nat.cast_ne_zero.2 hl0
  have e1 : P.valuation L x = WithZero.exp (WithZero.log (P.valuation L x)) := (WithZero.exp_log (by simpa using hx)).symm
  have e2 : P.valuation L (l : L) = WithZero.exp (WithZero.log (P.valuation L (l : L))) :=
    (WithZero.exp_log (by simpa using hl1)).symm
  generalize WithZero.log (P.valuation L x) = n at e1
  generalize WithZero.log (P.valuation L (l : L)) = e at e2
  have he : e ≠ 0 := by
    rintro rfl
    exact hl e2
  have hy : P.valuation L (x ^ e * (l : L) ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, map_zpow₀, e1, e2, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [mul_comm]
  have h1 := (hα _ hy).trans (hβ _ hy).symm
  simp only [map_mul, map_zpow₀, map_natCast] at h1
  have h0 : A.valuation (l : K) ^ (-n) ≠ 0 := zpow_ne_zero _ (by
    rw [← map_natCast α, map_ne_zero, map_ne_zero]; exact hl1)
  exact (zpow_left_inj₀ zero_le' zero_le' he).1 (mul_right_cancel₀ h0 h1)

theorem exists_aut_centre [IsGalois ℚ L] (L0 : IntermediateField ℚ L) (β : L →+* K) (P : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L0, A.valuation (β ((x : L0) : L)) < 1 ↔ algebraMap (𝓞 L0) (𝓞 L) x ∈ P.asIdeal) :
    ∃ σ : L ≃ₐ[L0] L, ∀ x : 𝓞 L, A.valuation (β (σ x)) < 1 ↔ x ∈ P.asIdeal := by
  let f : 𝓞 L →+* A := (β.comp (algebraMap (𝓞 L) L)).codRestrict A fun x => (A.valuation_le_one_iff _).1 (int_le_one A β x)
  let P' : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP' : ∀ x : 𝓞 L, x ∈ P' ↔ A.valuation (β x) < 1 := fun x => A.valuation_lt_one_iff (f x)
  haveI : P'.IsPrime := Ideal.comap_isPrime _ _
  haveI := P.isPrime
  haveI : P'.LiesOver (P.asIdeal.under (𝓞 L0)) := ⟨Ideal.ext fun x => ((hP' (algebraMap (𝓞 L0) (𝓞 L) x)).trans (h x)).symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.asIdeal.under (𝓞 L0)) P.asIdeal P' (L ≃ₐ[L0] L)
  refine ⟨σ, fun x => ?_⟩
  rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), hσ, hP']
  rfl

end Val

theorem exists_symbol {K Ω : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (σ : Formalism.ConjugateSelfDual.G K Ω) :
    ∃ t, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ := by
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb K Ω σ)⁻¹
  let t : (Af K)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing K) (Af K)) x
  let y : (InfiniteAdeleRing K)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing K) (Af K)) x
  have hy : y ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ := by
    let T : Set (InfiniteAdeleRing K) := Set.univ.pi fun w => {0}ᶜ
    have hS : ∀ w : InfinitePlace K, IsPreconnected ({0}ᶜ : Set w.Completion) := fun w => by
      have hw := IsTotallyComplex.isComplex w
      have := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2
        (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 0).isPreconnected
      convert this using 1
      ext z
      exact (map_ne_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)).symm
    have hp : IsPreconnected ((Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T) := by
      rw [← (isOpenEmbedding_val_inf K).isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]
      · exact isPreconnected_univ_pi hS
      · intro y hy
        have : IsUnit y := Pi.isUnit_iff.2 fun w => IsUnit.mk0 _ (hy w trivial)
        exact this
    have hm : ∀ u : (InfiniteAdeleRing K)ˣ, u ∈ (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T :=
      fun u w _ => (Pi.isUnit_iff.1 u.isUnit w).ne_zero
    exact hp.subset_connectedComponent (hm 1) (hm y)
  let y' : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (Af K)) y
  have h1 : art y' = 1 := by
    rw [← MonoidHom.mem_ker, ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)
  have e : x = y' * finIdele K t := by
    ext : 1
    apply Prod.ext
    · show _ = _ * 1
      rw [mul_one]; rfl
    · show _ = 1 * _
      rw [one_mul]; rfl
  refine ⟨t, ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol, inv_eq_iff_eq_inv, ← hx]
  conv_rhs => rw [e, map_mul, h1, one_mul]

theorem exists_exponent {G : Type} [CommGroup G] (ψ : G →* ℂˣ) {l n : ℕ} (hl : l.Prime) (h : ∀ q, ψ q ^ l ^ n = 1) (g : ℂ ≃+* ℂ)
    {c : ℤ} (hc : IsCoprime c (l : ℤ)) :
    ∃ a : ℤ, IsCoprime a (l : ℤ) ∧ (Units.map g.toRingHom.toMonoidHom).comp ψ = ψ ^ (c * a) := by
  have hN : l ^ (n + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨hN⟩
  have hζ := Complex.isPrimitiveRoot_exp _ hN
  generalize Complex.exp _ = ζ at hζ
  have hg : IsPrimitiveRoot (g ζ) (l ^ (n + 1)) := hζ.map_of_injective g.injective
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hec : e.Coprime (l ^ (n + 1)) := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero hN) e).1 (he ▸ hg)
  have hel : IsCoprime (e : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff n.succ_pos _ _).1 hec)
  obtain ⟨u, v, huv⟩ : IsCoprime c ((l : ℤ) ^ (n + 1)) := hc.pow_right
  have hu : IsCoprime u (l : ℤ) := ⟨c, v * l ^ n, by rw [← huv]; ring⟩
  refine ⟨u * e, hu.mul_left hel, MonoidHom.ext fun q => ?_⟩
  have h1 : ψ q ^ l ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, h, one_pow]
  have h2 : ψ q ^ (c * (u * e)) = ψ q ^ e := by
    rw [show c * (u * e) = e + ((l ^ (n + 1) : ℕ) : ℤ) * (-(v * e)) by push_cast; linear_combination (e : ℤ) * huv, zpow_add,
      zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow, mul_one]
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (ψ q : ℂ)) (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  refine Eq.trans (Units.ext ?_) h2.symm
  show g (ψ q : ℂ) = _
  rw [Units.val_pow_eq_pow_val, ← hk, map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]


open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols in
theorem ratio_conj (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : ToricRatioConjugates)
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (K : Type) [Field K] [NumberField K] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (I : Type) [Fintype I] [Nonempty I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (h1 : UnramFin E) (h2 : Module.finrank ℚ K = 2) (h3 : 0 < d) (h4 : δ ^ 2 = -(d : K))
    (h5 : IsCMType φ) (h6 : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (h7 : 1 ≤ s) (h8 : ∀ i, 1 ≤ κ i) (h9 : IsBaseCond 𝔣) (h10 : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h11 : IsValChar φ s κ 𝔣 ∅ χ)
    {T₀ : ℂ} {T : (PicO (condQ 𝔣 Q) →* ℂˣ) → ℂ} (hT₀ : IsToricSum φ s κ 𝔣 χ T₀)
    (hT : ∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ (T ψ)) (g : ℂ ≃+* ℂ)
    (hφ : ∀ i x, g (φ i x) = φ i x) (hχ : ∀ y, g (lamF χ s y) = lamF χ s y) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) :
    ∃ ζ : ℂˣ, IsOfFinOrder ζ ∧ g (T ψ / T₀) = (ζ : ℂ)⁻¹ * (T (conjChar g ψ) / T₀) := by
  obtain ⟨T₀', T', a1, -, a2, -, a3⟩ := hG E K d δ ι I φ s κ 𝔣 Q χ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain rfl : T₀' = T₀ := a1.unique hT₀
  obtain rfl : T' = T := funext fun ψ => (a2 ψ).unique (hT ψ)
  haveI : IsTotallyComplex K := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => by
    have h := congrArg (InfinitePlace.embedding_of_isReal hw) h4
    rw [map_pow, map_neg, map_natCast] at h
    have : (0 : ℝ) < d := by exact_mod_cast h3
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw δ)]⟩
  let Ω := AlgebraicClosure K
  letI : Algebra K ℂ := ι.toAlgebra
  let j : Ω →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← h6 (Classical.arbitrary I)]
    exact hφ _ _
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨art, ha⟩ := hA K Ω
  obtain ⟨t, ht⟩ := exists_symbol ha (gK.restrictNormal Ω)
  obtain ⟨b1, b2⟩ := a3 Ω j.toRingHom art (RingHom.ext j.commutes) ha g _ t hφ hχ (gK.restrictNormal_commutes Ω) ht ψ
  exact ⟨_, b2, b1⟩

end GlobalTheory.ThmAMove
end
end

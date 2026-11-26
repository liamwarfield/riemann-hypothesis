module

public import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ThInvVal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ReflectCpInv
noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

private lemma reflect_cp_inv {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (g : GL (Fin n) R) :
    reflect n (cp g⁻¹) = C ((cp g⁻¹).coeff 0) * cp g := by
  have h1 : reflect n (cp g⁻¹) = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev := by
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, cp]
  have h2 := Matrix.charpoly_inv ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Units.isUnit _)
  have h3 := Matrix.det_eq_sign_charpoly_coeff ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.coe_units_inv, inv_inv] at h2
  have h4 : IsUnit ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := Ring.mul_inverse_cancel _ h4
  rw [h1, cp, cp, h2]
  nth_rewrite 1 [h3] at h5
  have h6 := congrArg (C : R → R[X]) h5
  simp only [map_mul, map_pow, map_neg, map_one] at h6
  linear_combination (-((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev) * h6

private lemma ct_mul {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : ct c (A * B) = ct c B * ct c A := by
  rw [ct, ct, ct, ← Matrix.transpose_mul, Matrix.map_mul]

private lemma ct_ct {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : ct c (ct c A) = A := by
  ext i j
  have := congrArg (fun f : R ≃ₐ[k] R => f (A i j)) hc
  simpa [ct, pow_two] using this

private lemma csr_of_cong {k R : Type} [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R] (c : R ≃ₐ[k] R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (g : GL (Fin n) R) (hJ : IsUnit J.det) (h : cong c g J = J) :
    IsCsr c n (cp g) := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have h1 : ct c (g : Matrix (Fin n) (Fin n) R) =
      u.val * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (u⁻¹).val := by
    rw [cong] at h
    nth_rewrite 1 [← h]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have h2 : (cp g).map (c : R →+* R) = cp g⁻¹ := by
    have h3 := congrArg Matrix.charpoly h1
    rw [Matrix.coe_units_inv u, Matrix.charpoly_units_conj, ct, Matrix.charpoly_transpose] at h3
    rw [cp, cp, ← h3, ← Matrix.charpoly_map]
    rfl
  refine ⟨Matrix.charpoly_monic _, ?_, ?_, ?_⟩
  · rw [cp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · have h4 : IsUnit (g : Matrix (Fin n) (Fin n) R).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    rw [Matrix.det_eq_sign_charpoly_coeff] at h4
    exact isUnit_of_mul_isUnit_right h4
  · have h5 : c ((cp g).coeff 0) = (cp g⁻¹).coeff 0 := by
      rw [← h2, Polynomial.coeff_map]
      rfl
    rw [h2, h5, reflect_cp_inv]

theorem csrOf : CsrOf := by
  intro k R _ _ _ _ c hc n
  refine ⟨fun J g hJ h => csr_of_cong c J g hJ h, fun d => ?_⟩
  refine csr_of_cong c ((d⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) ?_
  have h1 : (th c d).val = ct c (d⁻¹ : GL (Fin n) R).val := rfl
  have h2 : ct c d.val * (th c d).val = 1 := (th c d).inv_val
  rw [cong, Units.val_mul, ct_mul]
  nth_rewrite 1 [h1]
  rw [ct_ct c hc]
  simp only [mul_assoc, Units.inv_mul_cancel_left, h2, mul_one]

end UpperTheory.ConvolutionTheory.D
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.TBase
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.tBase :
    UpperTheory.ConvolutionTheory.D.TBase := by
  intro k R _ _ _ _ A _ _ n b c hc g hg
  haveI : Module.Finite k A := Module.Finite.of_basis b
  let e : A ⊗[k] R ≃ₐ[k] R ⊗[k] A := Algebra.TensorProduct.comm k A R
  let τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl c
  have hτ : UpperTheory.ConvolutionTheory.D.IsGal τ 2 := (UpperTheory.ConvolutionTheory.D.galBase k R A c 2 hc).2.2.2
  have he : ∀ z, e (τ z) = UpperTheory.ConvolutionTheory.D.io c A (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [e, τ, UpperTheory.ConvolutionTheory.D.io]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) *
      UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
    have h2 : UpperTheory.ConvolutionTheory.D.io c A (g : R ⊗[k] A) *
        UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [Units.inv_eq_of_mul_eq_one_right hg.1] at h2 ⊢
    exact h2
  let a : (A ⊗[k] R)ˣ := Units.map (e.symm : R ⊗[k] A →* A ⊗[k] R) g⁻¹
  have ha : e (a : A ⊗[k] R) = ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) := e.apply_symm_apply _
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 k k A (A ⊗[k] R) τ 2 hτ a (by
    apply e.injective
    rw [Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one, AlgEquiv.one_apply,
      map_mul, he, ha, h1, map_one])
  refine ⟨Units.map (e : A ⊗[k] R →* R ⊗[k] A) z, ?_⟩
  have h3 := congrArg e hz
  rw [map_mul, he, ha] at h3
  change UpperTheory.ConvolutionTheory.D.io c A (e z) = g * e z
  calc UpperTheory.ConvolutionTheory.D.io c A (e z)
      = g * (((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) * UpperTheory.ConvolutionTheory.D.io c A (e z)) := by
        rw [Units.mul_inv_cancel_left]
    _ = g * e z := by rw [h3]
end

section -- merged from Development.AutomorphicArithmetic.UnitaryInvolutions.ExistsLocalQuadraticGaloisDataAtNonsplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace UpperTheory.G3.FixRing

section Abstract

variable {O : Type} [CommRing O]

private abbrev S (c : O →+* O) : Subring O := c.eqLocus (RingHom.id O)

private noncomputable def cE (c : O →+* O) (hc : ∀ x, c (c x) = x) : O ≃ₐ[S c] O :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom c c (RingHom.ext hc) (RingHom.ext hc)) (fun r => r.2)

private theorem cE_apply (c : O →+* O) (hc : ∀ x, c (c x) = x) (x : O) : cE c hc x = c x := rfl

private theorem isGal_cE (c : O →+* O) (hc : ∀ x, c (c x) = x) (ω u : O) (hu : (ω - c ω) * u = 1) :
    UpperTheory.ConvolutionTheory.D.IsGal (cE c hc) 2 := by
  refine ⟨by norm_num, ?_, Subtype.val_injective, (fun r hr => ⟨⟨r, hr⟩, rfl⟩), ?_⟩
  · ext x
    rw [pow_two, AlgEquiv.mul_apply, cE_apply, cE_apply, hc, AlgEquiv.one_apply]
  · refine ⟨2, ![-(c ω) * u, u], ![1, ω], fun j hj => ?_⟩
    interval_cases j
    · simp only [Fin.sum_univ_two, pow_zero, AlgEquiv.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, if_true]
      linear_combination hu
    · simp only [Fin.sum_univ_two, pow_one, cE_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
      simp
      ring

private theorem isUnit_S (c : O →+* O) (a : S c) (h : IsUnit (a : O)) : IsUnit a := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
  have ha : c (a : O) = a := a.2
  have h1 : (a : O) * c b = 1 := by
    have := congrArg c hb
    rwa [map_mul, ha, map_one] at this
  have hcb : c b = b := by
    calc c b = (b * a) * c b := by rw [mul_comm b, hb, one_mul]
      _ = b * (a * c b) := by ring
      _ = b := by rw [h1, mul_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨b, hcb⟩, Subtype.ext hb⟩

private theorem isLocal_S [Nontrivial O] (c : O →+* O) (h : ∀ x : O, IsUnit x ∨ IsUnit (1 - x)) :
    IsLocalRing (S c) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases h a with h | h
  · exact Or.inl (isUnit_S c a h)
  · exact Or.inr (isUnit_S c (1 - a) (by simpa using h))

end Abstract

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

private theorem le_iff_mul_inv {x b : L} (hb : b ≠ 0) :
    Valued.v (x * b⁻¹) ≤ 1 ↔ Valued.v x ≤ Valued.v b := by
  rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb))]

private theorem sub_le {g : ℕ → L} {a : L} (ha : Valued.v a ≤ 1)
    (hg : ∀ m, Valued.v (g (m + 1) - g m) ≤ Valued.v a ^ m) (m n : ℕ) (hmn : m ≤ n) :
    Valued.v (g n - g m) ≤ Valued.v a ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have e : g (n + 1) - g m = (g (n + 1) - g n) + (g n - g m) := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le ((hg n).trans (pow_le_pow_right_of_le_one' ha hmn)) ih)

private theorem exists_limit [CompleteSpace L] {a : L} (ha0 : a ≠ 0) (ha : Valued.v a < 1) {g : ℕ → L}
    (hg : ∀ m, Valued.v (g (m + 1) - g m) ≤ Valued.v a ^ m) :
    ∃ l, ∀ m, Valued.v (g m - l) ≤ Valued.v a ^ m := by
  have hc : CauchySeq g := by
    rw [(Valued.hasBasis_uniformity L _).cauchySeq_iff]
    intro γ _
    have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    obtain ⟨N, hN⟩ := exists_pow_lt₀ ha (Units.mk0 _ hne)
    have key : ∀ p r, N ≤ p → p ≤ r → Valued.v (g r - g p) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
      fun p r hp hpr => lt_of_le_of_lt ((sub_le ha.le hg p r hpr).trans
        (pow_le_pow_right_of_le_one' ha.le hp)) hN
    refine ⟨N, fun m hm n hn => ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_lt_iff_lt_embedding]
    rcases le_total m n with h | h
    · exact key m n hm h
    · rw [Valuation.map_sub_swap]
      exact key n m hn h
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨l, fun m => ?_⟩
  have hb : a ^ m ≠ 0 := pow_ne_zero _ ha0
  have hcl : IsClosed {y : L | Valued.v ((g m - y) * (a ^ m)⁻¹) ≤ 1} :=
    (Valued.isClosed_integer (R := L)).preimage
      (f := fun y : L => (g m - y) * (a ^ m)⁻¹) (by fun_prop)
  have hmem : Valued.v ((g m - l) * (a ^ m)⁻¹) ≤ 1 := by
    refine hcl.mem_of_tendsto hl ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    show Valued.v ((g m - g n) * (a ^ m)⁻¹) ≤ 1
    rw [le_iff_mul_inv hb, Valuation.map_sub_swap, map_pow]
    exact sub_le ha.le hg m n hn
  rw [le_iff_mul_inv hb, map_pow] at hmem
  exact hmem

private theorem isUnit_int_iff (x : intL L) : IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have h1 : Valued.v (x : L) * Valued.v (b : L) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hb]
      simp
    have hx : Valued.v (x : L) ≤ 1 := x.2
    have hb' : Valued.v (b : L) ≤ 1 := b.2
    by_contra hne
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx hne
    exact absurd h1 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hb') hlt))
  · intro h
    have hne : (x : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : L)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v (x : L)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    · simp [hne]

private theorem isUnit_or (x : intL L) : IsUnit x ∨ IsUnit (1 - x) := by
  by_cases h : Valued.v (x : L) = 1
  · exact Or.inl ((isUnit_int_iff x).2 h)
  · have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne x.2 h
    refine Or.inr ((isUnit_int_iff _).2 ?_)
    have : (((1 - x : intL L)) : L) = 1 - (x : L) := by simp
    rw [this]
    exact Valuation.map_one_sub_of_lt _ hlt

private theorem t_lt_one :
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  norm_num

private theorem valuation_lt_one_le_uniformiser {a : WithZero (Multiplicative ℤ)} (h : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le'
  · obtain ⟨b, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd b < 0 := h
    show Multiplicative.toAdd b ≤ -1
    omega

end Val

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

private theorem span_eq {ϖ : L} (hv : Valued.v ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (p : intL L) (hp : (p : L) = ϖ) :
    Ideal.span {p} = (IsLocalRing.maximalIdeal
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring : Ideal (intL L)) := by
  have hp1 : Valued.v (p : L) < 1 := by rw [hp, hv]; exact t_lt_one
  have hp0 : (p : L) ≠ 0 := by
    intro h0
    rw [hp] at h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  ext x
  rw [Ideal.mem_span_singleton]
  change _ ↔ x ∈ nonunits _
  constructor
  · rintro ⟨e, rfl⟩ hu
    have hu' : IsUnit (p * e) := hu
    have := (isUnit_int_iff _).1 (isUnit_of_mul_isUnit_left hu')
    exact absurd this (ne_of_lt hp1)
  · intro hx
    have hx' : ¬ IsUnit x := hx
    have hlt : Valued.v (x : L) < 1 :=
      lt_of_le_of_ne x.2 (fun h => hx' ((isUnit_int_iff x).2 h))
    have hle : Valued.v (x : L) ≤ Valued.v (p : L) := by
      rw [hp, hv]
      exact valuation_lt_one_le_uniformiser hlt
    refine ⟨⟨(x : L) * (p : L)⁻¹, (le_iff_mul_inv hp0).2 hle⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul]
    field_simp

theorem fixed_ring_data [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    ∃ (k : Type) (_ : CommRing k) (_ : IsLocalRing k) (_ : Algebra k (intL L))
      (c : intL L ≃ₐ[k] intL L) (p ω : intL L),
      UpperTheory.ConvolutionTheory.D.IsGal c 2 ∧ (∀ x : intL L, ((c x : intL L) : L) = σ x) ∧ c p = p ∧ p ≠ 0 ∧
      (∀ f : ℕ → intL L, (∀ m, ∃ e, f (m + 1) - f m = p ^ m * e) → ∃ l, ∀ m, ∃ e, f m - l = p ^ m * e) ∧
      (∀ x : intL L, (∀ m : ℕ, ∃ e, x = p ^ m * e) → x = 0) ∧
      Finite (intL L ⧸ Ideal.span {p}) ∧ IsUnit (ω - c ω) := by
  obtain ⟨hinv, hval, hfix, hv, ⟨x0, hx0, hx1⟩, hq, hcard⟩ := h
  have hlt : Valued.v ϖ < 1 := by rw [hv]; exact t_lt_one
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  let c0 : intL L →+* intL L := σ.restrict (intL L) (intL L) (fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [hval]
    exact hx)
  have hc0 : ∀ x : intL L, ((c0 x : intL L) : L) = σ x := fun _ => rfl
  have hc : ∀ x, c0 (c0 x) = x := fun x => Subtype.ext (by rw [hc0, hc0, hinv])
  let p : intL L := ⟨ϖ, hlt.le⟩
  let ω : intL L := ⟨x0, hx0⟩
  have hω : IsUnit (ω - c0 ω) := by
    refine (isUnit_int_iff _).2 ?_
    have : (((ω - c0 ω : intL L)) : L) = x0 - σ x0 := rfl
    rw [this, Valuation.map_sub_swap]
    exact hx1
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.1 hω
  have hp1 : ∀ (m : ℕ) (e : intL L), Valued.v (((p ^ m * e : intL L)) : L) ≤ Valued.v ϖ ^ m := by
    intro m e
    have : (((p ^ m * e : intL L)) : L) = ϖ ^ m * (e : L) := rfl
    rw [this, map_mul, map_pow]
    exact mul_le_of_le_one_right' e.2
  refine ⟨S c0, inferInstance, isLocal_S c0 isUnit_or, inferInstance, cE c0 hc, p, ω,
    isGal_cE c0 hc ω u hu, hc0, Subtype.ext hfix, fun h0 => hϖ0 (congrArg Subtype.val h0), ?_, ?_, ?_, hω⟩
  · intro f hf
    have hg : ∀ m, Valued.v ((f (m + 1) : L) - (f m : L)) ≤ Valued.v ϖ ^ m := by
      intro m
      obtain ⟨e, he⟩ := hf m
      have := hp1 m e
      rwa [← he] at this
    obtain ⟨l, hl'⟩ := exists_limit (g := fun m => (f m : L)) hϖ0 hlt hg
    have hl : ∀ m, Valued.v ((f m : L) - l) ≤ Valued.v ϖ ^ m := hl'
    have hl1 : Valued.v l ≤ 1 := by
      have h0 := hl 0
      rw [pow_zero] at h0
      have e : l = (f 0 : L) - ((f 0 : L) - l) := by ring
      rw [e]
      exact (Valuation.map_sub _ _ _).trans (max_le (f 0).2 h0)
    refine ⟨⟨l, hl1⟩, fun m => ?_⟩
    have hb : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ0
    refine ⟨⟨((f m : L) - l) * (ϖ ^ m)⁻¹, (le_iff_mul_inv hb).2 (by rw [map_pow]; exact hl m)⟩, Subtype.ext ?_⟩
    show (f m : L) - l = ϖ ^ m * (((f m : L) - l) * (ϖ ^ m)⁻¹)
    field_simp
  · intro x hx
    by_contra hne
    have hx0' : Valued.v (x : L) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (fun h0 => hne (Subtype.ext h0))
    obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hx0')
    obtain ⟨e, he⟩ := hx N
    have := hp1 N e
    rw [← he] at this
    exact absurd (lt_of_le_of_lt this hN) (lt_irrefl _)
  · have hfin : Finite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
        IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    rw [span_eq hv p rfl]
    exact hfin

end Main

end UpperTheory.G3.FixRing

theorem UpperTheory.exists_local_quadratic_galois_data_at_nonsplit_place :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w →
        ∃ (k : Type) (_ : CommRing k) (_ : IsLocalRing k) (_ : Algebra k (Ov E w)) (c : Ov E w ≃ₐ[k] Ov E w) (ϖ ω : Ov E w),
          UpperTheory.ConvolutionTheory.D.IsGal c 2 ∧ (∀ x : Ov E w, ((c x : Ov E w) : w.adicCompletion E) = cj w x) ∧ c ϖ = ϖ ∧ ϖ ≠ 0 ∧
          (∀ f : ℕ → Ov E w, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) → ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e) ∧
          (∀ x : Ov E w, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0) ∧
          Finite (Ov E w ⧸ Ideal.span {ϖ}) ∧ IsUnit (ω - c ω) := by
  intro E _ _ _ hU w hw
  obtain ⟨ϖ, q, hq, -⟩ := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hw).2.1
  exact UpperTheory.G3.FixRing.fixed_ring_data hq
end

section -- merged from Development.AutomorphicArithmetic.UnitaryInvolutions.TwistedConjOfCharpolyMulGalConjEqOfSeparable
open Matrix Polynomial
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem twistedInverse_mul (c : R ≃ₐ[k] R) (a b : GL (Fin n) R) :
    th c (a * b) = th c a * th c b := by
  refine Units.ext ?_
  change ct c ((a * b)⁻¹ : GL (Fin n) R).val =
    ct c (a⁻¹ : GL (Fin n) R).val * ct c (b⁻¹ : GL (Fin n) R).val
  rw [_root_.mul_inv_rev, Units.val_mul, ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

private theorem twistedInverse_one (c : R ≃ₐ[k] R) : th c (1 : GL (Fin n) R) = 1 := by
  refine Units.ext ?_
  change ct c ((1 : GL (Fin n) R)⁻¹ : GL (Fin n) R).val = 1
  rw [inv_one, Units.val_one, ct, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]

private theorem twistedConj_mul (c : R ≃ₐ[k] R) (u v d : GL (Fin n) R) :
    thConj c (u * v) d = thConj c v (thConj c u d) := by
  simp only [thConj, twistedInverse_mul, _root_.mul_inv_rev, mul_assoc]

private theorem twistedConj_one (c : R ≃ₐ[k] R) (d : GL (Fin n) R) : thConj c 1 d = d := by
  simp only [thConj, twistedInverse_one, inv_one, one_mul, mul_one]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.twistedConj_of_charpoly_mul_galConj_eq_of_separable :
    ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R), UpperTheory.ConvolutionTheory.D.IsGal c 2 →
        (∀ (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (_ : Module.Basis (Fin n) k A) (x : Aˣ), UpperTheory.ConvolutionTheory.D.NormIn c x) →
        ∀ (n : ℕ) (d d' : GL (Fin n) R), (UpperTheory.ConvolutionTheory.D.cp (d * UpperTheory.ConvolutionTheory.D.th c d)).Separable →
          UpperTheory.ConvolutionTheory.D.cp (d' * UpperTheory.ConvolutionTheory.D.th c d') = UpperTheory.ConvolutionTheory.D.cp (d * UpperTheory.ConvolutionTheory.D.th c d) →
          ∃ t, d' = UpperTheory.ConvolutionTheory.D.thConj c t d := by
  intro k R _ _ _ _ c hG hN n d d' hsep hcp
  haveI : Nontrivial R := hG.inj.nontrivial
  have hP := (UpperTheory.ConvolutionTheory.D.csrOf k R c hG.pow n).2 d
  obtain ⟨A, _, _, b, g, hg, hgP⟩ := UpperTheory.ConvolutionTheory.D.modelEx k R c hG n _ hP hsep
  obtain ⟨w, hw⟩ := UpperTheory.ConvolutionTheory.D.tBase k R A n b c hG g hg
  obtain ⟨x, y, hx⟩ := UpperTheory.ConvolutionTheory.D.tClass k R A n b c hG g hg w hw d hgP.symm
  obtain ⟨x', y', hx'⟩ := UpperTheory.ConvolutionTheory.D.tClass k R A n b c hG g hg w hw d' (hcp.trans hgP.symm)
  obtain ⟨z, hz⟩ := hN A n b (x' / x)
  have h2 := (((UpperTheory.ConvolutionTheory.D.tIso k R A n b c hG g hg w hw).2 x x' _ _ hx hx').2
    (UpperTheory.ConvolutionTheory.D.matU b z)).2 ⟨z, rfl, hz⟩
  refine ⟨y * UpperTheory.ConvolutionTheory.D.matU b z * y'⁻¹, ?_⟩
  rw [UpperTheory.ConvolutionTheory.D.twistedConj_mul, UpperTheory.ConvolutionTheory.D.twistedConj_mul c y, ← h2,
    ← UpperTheory.ConvolutionTheory.D.twistedConj_mul, mul_inv_cancel, UpperTheory.ConvolutionTheory.D.twistedConj_one]
end

section -- merged from Development.AutomorphicArithmetic.UnitaryInvolutions.NormInOfFreeAlgebraOfCompleteQuadratic
section -- merged from Development.AutomorphicArithmetic.UnitaryInvolutions.ExistsMulInvolutionEqFixedUnitOfComplete
open scoped Classical

private lemma normStep_algebra {T : Type} [CommRing T] (z zb u P a b bb v : T)
    (h1 : z * zb - u = P * a) (hb : b + bb = -(v * a)) (hv : v * u = 1) :
    z * (1 + P * b) * (zb * (1 + P * bb)) - u
      = P * P * (u * b * bb - v * a * a + P * a * b * bb) := by
  linear_combination (1 + P * (b + bb) + P ^ 2 * b * bb) * h1 + (u + P * a) * P * hb - P * a * hv

private lemma normLimit_algebra {T : Type} [CommRing T] (F Fb L Lb u P e eb c : T)
    (h : F - L = P * e) (hb : Fb - Lb = P * eb) (hf : F * Fb - u = P * c) :
    L * Lb - u = P * (c - e * Fb - F * eb + P * e * eb) := by
  linear_combination -Lb * h - (F - P * e) * hb + hf

private lemma pow_regular {T : Type} [CommRing T] (ϖ : T) (hreg : ∀ x : T, ϖ * x = 0 → x = 0)
    (n : ℕ) (x : T) (h : ϖ ^ n * x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    apply hreg
    apply ih
    rw [← mul_assoc, ← pow_succ]
    exact h

private lemma norm_level_zero (T : Type) [CommRing T] (ι : T →+* T) (ϖ ω : T)
    (hι : ∀ x, ι (ι x) = x) (hϖ : ι ϖ = ϖ) (hfin : Finite (T ⧸ Ideal.span {ϖ}))
    (hω : IsUnit (ω - ι ω)) (u : T) (hu : IsUnit u) (hfix : ι u = u) :
    ∃ z a, z * ι z - u = ϖ ^ (0 + 1) * a := by
  have hle : Ideal.span {ϖ} ≤ (Ideal.span {ϖ}).comap ι := by
    rw [Ideal.span_le]
    intro x hx
    have hx' : x = ϖ := hx
    subst hx'
    change ι x ∈ Ideal.span {x}
    rw [hϖ]
    exact Ideal.mem_span_singleton_self x
  let c : (T ⧸ Ideal.span {ϖ}) →+* (T ⧸ Ideal.span {ϖ}) :=
    Ideal.quotientMap (Ideal.span {ϖ}) ι hle
  have hc : ∀ x : T, c (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ι x) := fun x =>
    Ideal.quotientMap_mk
  have hinv : ∀ x, c (c x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hc, hc, hι]
  have hunit : IsUnit ((Ideal.Quotient.mk (Ideal.span {ϖ}) ω) - c (Ideal.Quotient.mk _ ω)) := by
    rw [hc, ← map_sub]
    exact hω.map _
  obtain ⟨x, hx⟩ := GlobalTheory.finite_involution_fixed_unit_isNorm (T ⧸ Ideal.span {ϖ}) c hinv
    ⟨_, hunit⟩ (Ideal.Quotient.mk _ u) (by rw [hc, hfix]) (hu.map _)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [hc, ← map_mul] at hx
  have hmem : z * ι z - u ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq]
    exact hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨z, a, by simpa using ha⟩

private lemma norm_step (T : Type) [CommRing T] (ι : T →+* T) (ϖ ω : T)
    (hι : ∀ x, ι (ι x) = x) (hϖ : ι ϖ = ϖ) (hreg : ∀ x : T, ϖ * x = 0 → x = 0)
    (hω : IsUnit (ω - ι ω)) (u : T) (hu : IsUnit u) (hfix : ι u = u)
    (j : ℕ) (z : T) (hz : ∃ a, z * ι z - u = ϖ ^ (j + 1) * a) :
    ∃ z', (∃ a, z' * ι z' - u = ϖ ^ (j + 1 + 1) * a) ∧ ∃ e, z' - z = ϖ ^ (j + 1) * e := by
  obtain ⟨a, ha⟩ := hz
  have hιP : ι (ϖ ^ (j + 1)) = ϖ ^ (j + 1) := by rw [map_pow, hϖ]
  have haι : ι a = a := by
    have h2 : z * ι z - u = ϖ ^ (j + 1) * ι a := by
      have := congrArg ι ha
      simp only [map_sub, map_mul, hι, hfix, hιP] at this
      rw [← this]
      ring
    have h3 : ϖ ^ (j + 1) * (ι a - a) = 0 := by
      linear_combination ha - h2
    exact sub_eq_zero.mp (pow_regular ϖ hreg _ _ h3)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨w, hw⟩ := hω.exists_left_inv
  have hιv : ι v = v := by
    have h1 : ι v * u = 1 := by
      have := congrArg ι hv
      simpa [hfix] using this
    linear_combination v * h1 - ι v * hv
  have hιw : ι w = -w := by
    have h1 : ι w * (ι ω - ω) = 1 := by
      have := congrArg ι hw
      simpa [hι] using this
    linear_combination (-w) * h1 - ι w * hw
  have hsum : ω * w + ι (ω * w) = 1 := by
    rw [map_mul, hιw]
    linear_combination hw
  set b : T := -(ω * w * v * a) with hbdef
  have hbsum : b + ι b = -(v * a) := by
    have : ι b = -(ι (ω * w) * v * a) := by
      rw [hbdef]
      simp only [map_neg, map_mul, hιv, haι]
    rw [this, hbdef]
    linear_combination (-(v * a)) * hsum
  refine ⟨z * (1 + ϖ ^ (j + 1) * b), ⟨ϖ ^ j * (u * b * ι b - v * a * a +
    ϖ ^ (j + 1) * a * b * ι b), ?_⟩, ⟨z * b, by ring⟩⟩
  have h := normStep_algebra z (ι z) u (ϖ ^ (j + 1)) a b (ι b) v ha hbsum hv
  have hι' : ι (z * (1 + ϖ ^ (j + 1) * b)) = ι z * (1 + ϖ ^ (j + 1) * ι b) := by
    simp only [map_mul, map_add (f := _), map_one, hιP]
  rw [hι', h]
  ring

theorem UpperTheory.exists_mul_involution_eq_fixed_unit_of_complete :
    ∀ (T : Type) [CommRing T] (ι : T →+* T) (ϖ ω : T), (∀ x, ι (ι x) = x) → ι ϖ = ϖ →
        (∀ x : T, ϖ * x = 0 → x = 0) →
        (∀ f : ℕ → T, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) → ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e) →
        (∀ x : T, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0) →
        Finite (T ⧸ Ideal.span {ϖ}) → IsUnit (ω - ι ω) →
        ∀ u : T, IsUnit u → ι u = u → ∃ z, z * ι z = u := by
  intro T _ ι ϖ ω hι hϖ hreg hcomp hsep hfin hω u hu hfix
  obtain ⟨z₀, hz₀⟩ := norm_level_zero T ι ϖ ω hι hϖ hfin hω u hu hfix
  have step := norm_step T ι ϖ ω hι hϖ hreg hω u hu hfix
  let g : (j : ℕ) → {z : T // ∃ a, z * ι z - u = ϖ ^ (j + 1) * a} := fun j =>
    Nat.rec ⟨z₀, hz₀⟩
      (fun j p => ⟨(step j p.1 p.2).choose, (step j p.1 p.2).choose_spec.1⟩) j
  have hg : ∀ j, ∃ e, (g (j + 1)).1 - (g j).1 = ϖ ^ (j + 1) * e := fun j =>
    (step j (g j).1 (g j).2).choose_spec.2
  obtain ⟨L, hL⟩ := hcomp (fun j => (g j).1) (fun m => by
    obtain ⟨e, he⟩ := hg m
    exact ⟨ϖ * e, by rw [he, pow_succ]; ring⟩)
  refine ⟨L, sub_eq_zero.mp (hsep _ fun m => ?_)⟩
  obtain ⟨e, he⟩ := hL m
  obtain ⟨a, ha⟩ := (g m).2
  have heι : ι (g m).1 - ι L = ϖ ^ m * ι e := by
    have := congrArg ι he
    simpa [hϖ] using this
  have hf : (g m).1 * ι (g m).1 - u = ϖ ^ m * (ϖ * a) := by
    rw [ha, pow_succ]
    ring
  exact ⟨_, normLimit_algebra _ _ _ _ _ _ _ _ _ he heι hf⟩
end

open Matrix Polynomial
open scoped TensorProduct

private lemma repr_sum {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (e : Fin n → R) (i : Fin n) :
    B.repr (∑ j, e j • B j) i = e i :=
  congrFun (B.repr_sum_self e) i

private lemma coord_dvd {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R) (m : ℕ) (y : T) :
    (∃ e, y = (algebraMap R T ϖ) ^ m * e) ↔ ∀ i, ∃ e, B.repr y i = ϖ ^ m * e := by
  constructor
  · rintro ⟨e, rfl⟩ i
    refine ⟨B.repr e i, ?_⟩
    rw [← map_pow, ← Algebra.smul_def, map_smul]
    simp
  · intro h
    choose e he using h
    refine ⟨∑ i, e i • B i, ?_⟩
    rw [← map_pow, ← Algebra.smul_def]
    apply B.ext_elem
    intro i
    rw [he, map_smul, Finsupp.smul_apply, repr_sum]
    simp

private lemma coord_reg {R T : Type} [CommRing R] [IsDomain R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R) (hϖ : ϖ ≠ 0) (x : T)
    (h : algebraMap R T ϖ * x = 0) : x = 0 := by
  apply B.ext_elem
  intro i
  have h1 : B.repr (ϖ • x) i = 0 := by
    rw [Algebra.smul_def, h]
    simp
  rw [map_smul] at h1
  simpa [hϖ] using h1

private lemma coord_complete {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R)
    (hcomp : ∀ f : ℕ → R, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) →
      ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e)
    (f : ℕ → T) (hf : ∀ m, ∃ e, f (m + 1) - f m = (algebraMap R T ϖ) ^ m * e) :
    ∃ L, ∀ m, ∃ e, f m - L = (algebraMap R T ϖ) ^ m * e := by
  have h1 : ∀ i, ∃ L, ∀ m, ∃ e, B.repr (f m) i - L = ϖ ^ m * e := by
    intro i
    apply hcomp (fun m => B.repr (f m) i)
    intro m
    obtain ⟨e, he⟩ := (coord_dvd B ϖ m _).1 (hf m) i
    exact ⟨e, by simpa using he⟩
  choose L hL using h1
  refine ⟨∑ i, L i • B i, fun m => (coord_dvd B ϖ m _).2 fun i => ?_⟩
  obtain ⟨e, he⟩ := hL i m
  refine ⟨e, ?_⟩
  rw [map_sub, Finsupp.sub_apply, repr_sum]
  exact he

private lemma coord_sep {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R)
    (hsep : ∀ x : R, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0)
    (x : T) (h : ∀ m : ℕ, ∃ e, x = (algebraMap R T ϖ) ^ m * e) : x = 0 := by
  apply B.ext_elem
  intro i
  simpa using hsep _ fun m => (coord_dvd B ϖ m x).1 (h m) i

private lemma coord_finite {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R) (hfin : Finite (R ⧸ Ideal.span {ϖ})) :
    Finite (T ⧸ Ideal.span {algebraMap R T ϖ}) := by
  let g : (Fin n → R ⧸ Ideal.span {ϖ}) → T ⧸ Ideal.span {algebraMap R T ϖ} := fun v =>
    Ideal.Quotient.mk _ (∑ i, (Quotient.out (v i) : R) • B i)
  refine Finite.of_surjective g fun y => ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun i => Ideal.Quotient.mk _ (B.repr t i), ?_⟩
  refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ?_)
  have hd : ∃ e, (∑ i, (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr t i)) : R) • B i) - t
      = (algebraMap R T ϖ) ^ 1 * e := by
    refine (coord_dvd B ϖ 1 _).2 fun i => ?_
    have hm : (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr t i)) : R) - B.repr t i
        ∈ Ideal.span {ϖ} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨e, ?_⟩
    rw [map_sub, Finsupp.sub_apply, repr_sum]
    simpa [mul_comm] using he.symm
  obtain ⟨e, he⟩ := hd
  exact ⟨e, by rw [he, pow_one, mul_comm]⟩

theorem UpperTheory.normIn_of_free_algebra_of_complete_quadratic :
    ∀ (k R : Type) [CommRing k] [CommRing R] [IsDomain R] [Algebra k R] (c : R ≃ₐ[k] R) (ϖ ω : R),
        UpperTheory.ConvolutionTheory.D.IsGal c 2 → c ϖ = ϖ → ϖ ≠ 0 →
        (∀ f : ℕ → R, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) → ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e) →
        (∀ x : R, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0) →
        Finite (R ⧸ Ideal.span {ϖ}) → IsUnit (ω - c ω) →
        ∀ (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (_ : Module.Basis (Fin n) k A) (x : Aˣ), UpperTheory.ConvolutionTheory.D.NormIn c x := by
  intro k R _ _ _ _ c ϖ ω hG hcϖ hϖ hcomp hsep hfin hω A _ _ n b x
  have hc2 : ∀ r, c (c r) = r := fun r => by
    have h := DFunLike.congr_fun hG.pow r
    simpa [pow_two] using h
  have hio : ∀ (r : R) (a : A), UpperTheory.ConvolutionTheory.D.io c A (r ⊗ₜ[k] a) = (c r) ⊗ₜ[k] a := fun r a => by
    simp [UpperTheory.ConvolutionTheory.D.io]
  have hioalg : ∀ r : R, UpperTheory.ConvolutionTheory.D.io c A (algebraMap R (R ⊗[k] A) r)
      = algebraMap R (R ⊗[k] A) (c r) := fun r => by
    simp [Algebra.TensorProduct.algebraMap_apply, hio]
  let ι : (R ⊗[k] A) →+* (R ⊗[k] A) := (UpperTheory.ConvolutionTheory.D.io c A : (R ⊗[k] A) ≃ₐ[k] (R ⊗[k] A))
  have hιa : ∀ t, ι t = UpperTheory.ConvolutionTheory.D.io c A t := fun _ => rfl
  have hinv : ∀ t, ι (ι t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp only [hιa, hio, hc2]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have B := Algebra.TensorProduct.basis R b
  obtain ⟨z, hz⟩ := UpperTheory.exists_mul_involution_eq_fixed_unit_of_complete (R ⊗[k] A) ι (algebraMap R _ ϖ) (algebraMap R _ ω) hinv
    (by rw [hιa, hioalg, hcϖ]) (coord_reg B ϖ hϖ) (coord_complete B ϖ hcomp) (coord_sep B ϖ hsep)
    (coord_finite B ϖ hfin)
    (by
      rw [hιa, hioalg, ← map_sub]
      exact hω.map _)
    ((1 : R) ⊗ₜ[k] (x : A))
    (x.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A))
    (by rw [hιa, hio, map_one])
  have hu : IsUnit ((1 : R) ⊗ₜ[k] (x : A)) :=
    x.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)
  have hzu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ hu)
  exact ⟨hzu.unit, by simpa [hιa] using hz.symm⟩
end

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem UpperTheory.G3.InertCase.th_mul {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (c : R ≃ₐ[k] R) (a b : GL (Fin n) R) :
    UpperTheory.ConvolutionTheory.D.th c (a * b) = UpperTheory.ConvolutionTheory.D.th c a * UpperTheory.ConvolutionTheory.D.th c b := by
  refine Units.ext ?_
  change UpperTheory.ConvolutionTheory.D.ct c ((a * b)⁻¹ : GL (Fin n) R).val =
    UpperTheory.ConvolutionTheory.D.ct c (a⁻¹ : GL (Fin n) R).val * UpperTheory.ConvolutionTheory.D.ct c (b⁻¹ : GL (Fin n) R).val
  rw [_root_.mul_inv_rev, Units.val_mul, UpperTheory.ConvolutionTheory.D.ct, UpperTheory.ConvolutionTheory.D.ct, UpperTheory.ConvolutionTheory.D.ct, Matrix.map_mul,
    Matrix.transpose_mul]

theorem UpperTheory.unitary_involution_stabilizes_integral_at_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (u δ : GL (Fin n) E),
        (∀ g, thE E n g = u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) g * u⁻¹) →
        u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) u = 1 → ∀ w : Pl E, ¬ IsSplitAt w →
        (∀ g : GLw n w, (thL n w g).val = u.val.map (algebraMap E _) * ((g⁻¹ : GLw n w).val.map (cj w))ᵀ * (u⁻¹ : GL (Fin n) E).val.map (algebraMap E _)) →
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) u ∈ GlobalTheory.LFun.KGL w (n := n) →
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ ∈ GlobalTheory.LFun.KGL w (n := n) →
        (∀ Q : (Ov E w)[X], Q.map (Ov E w).subtype = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) → Q.Separable) →
        ∀ y ∈ GlobalTheory.LFun.KGL w (n := n), UpperTheory.ConvolutionTheory.G3.lpol w y = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) →
          ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), y = k⁻¹ * locEl n w δ * thL n w k := by
  intro E _ _ _ hU n u δ hT hu w hw hL huK hδK hQ y hyK hy
  obtain ⟨k, _, _, _, c, ϖ, ω, hG, hc, hcϖ, hϖ, hcomp, hsep, hfin, hω⟩ := UpperTheory.exists_local_quadratic_galois_data_at_nonsplit_place E hU w hw
  have core := UpperTheory.twistedConj_of_charpoly_mul_galConj_eq_of_separable k (Ov E w) c hG
    (UpperTheory.normIn_of_free_algebra_of_complete_quadratic k (Ov E w) c ϖ ω hG hcϖ hϖ hcomp hsep hfin hω) n
  have hconj := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hw).1
  obtain ⟨ι, hιdef⟩ : ∃ ι : GL (Fin n) (Ov E w) →* GLw n w, ι = Formalism.UG.bc (Ov E w).subtype := ⟨_, rfl⟩
  have hιv : ∀ a, (ι a).val = a.val.map (Ov E w).subtype := fun a => by rw [hιdef]; rfl
  have hinj : Function.Injective ι := fun a b e =>
    Units.ext (Matrix.map_injective (Ov E w).subtype_injective
      (by
        show a.val.map (Ov E w).subtype = b.val.map (Ov E w).subtype
        rw [← hιv, ← hιv, e]))
  have hK : ∀ x ∈ GlobalTheory.LFun.KGL w (n := n), ∃ a, ι a = x := by
    intro x hx
    rw [hιdef]
    exact hx
  obtain ⟨u₀, hu₀⟩ := hK _ huK
  obtain ⟨δ₀, hδ₀⟩ := hK _ hδK
  obtain ⟨y₀, rfl⟩ := hK _ hyK
  have hcompat : ∀ a : GL (Fin n) (Ov E w),
      (ι (UpperTheory.ConvolutionTheory.D.th c a)).val = (((ι a)⁻¹ : GLw n w).val.map (cj w))ᵀ := by
    intro a
    rw [← map_inv, hιv, hιv]
    refine Matrix.ext fun i j => ?_
    exact hc _
  have hthL : ∀ a : GL (Fin n) (Ov E w),
      thL n w (ι a) = ι u₀ * ι (UpperTheory.ConvolutionTheory.D.th c a) * (ι u₀)⁻¹ := by
    intro a
    refine Units.ext ?_
    rw [hL, Units.val_mul, Units.val_mul, hcompat, hu₀, ← map_inv]
    rfl
  have hmapth : ι (UpperTheory.ConvolutionTheory.D.th c u₀) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))
      (UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) u) := by
    refine Units.ext ?_
    rw [hcompat, hu₀, ← map_inv]
    refine Matrix.ext fun i j => ?_
    exact hconj _
  have hu1 : UpperTheory.ConvolutionTheory.D.th c u₀ = u₀⁻¹ := by
    refine eq_inv_of_mul_eq_one_right (hinj ?_)
    rw [map_mul, map_one, hmapth, hu₀, ← map_mul, hu, map_one]
  have hnrm : ∀ a : GL (Fin n) (Ov E w),
      nrmL n w (ι a) = ι (a * u₀ * UpperTheory.ConvolutionTheory.D.th c (a * u₀)) := by
    intro a
    have e : nrmL n w (ι a) = ι a * thL n w (ι a) := by
      unfold nrmL thL
      rw [if_neg hw, if_neg hw]
    rw [e, hthL, UpperTheory.G3.InertCase.th_mul, hu1]
    simp only [map_mul, map_inv, mul_assoc]
  have hloc : locEl n w δ = ι δ₀ := by
    rw [hδ₀]
    unfold locEl
    rw [if_neg hw]
  have hcpmap : ∀ a : GL (Fin n) (Ov E w),
      (UpperTheory.ConvolutionTheory.D.cp (a * u₀ * UpperTheory.ConvolutionTheory.D.th c (a * u₀))).map (Ov E w).subtype =
        (nrmL n w (ι a)).val.charpoly := by
    intro a
    rw [hnrm, hιv]
    exact (Matrix.charpoly_map _ _).symm
  have hδpol : (UpperTheory.ConvolutionTheory.D.cp (δ₀ * u₀ * UpperTheory.ConvolutionTheory.D.th c (δ₀ * u₀))).map (Ov E w).subtype =
      atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) := by
    rw [hcpmap, ← hloc]
    exact GlobalTheory.BCT.ThBasic.charpoly_nrmL hU n w δ
  have hypol : (UpperTheory.ConvolutionTheory.D.cp (y₀ * u₀ * UpperTheory.ConvolutionTheory.D.th c (y₀ * u₀))).map (Ov E w).subtype =
      atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) := (hcpmap y₀).trans hy
  obtain ⟨t, ht⟩ := core (δ₀ * u₀) (y₀ * u₀) (hQ _ hδpol)
    (Polynomial.map_injective _ (Ov E w).subtype_injective (hypol.trans hδpol.symm))
  refine ⟨ι t, ⟨t, by rw [hιdef]⟩, ?_⟩
  have h1 := congrArg ι ht
  rw [UpperTheory.ConvolutionTheory.D.thConj] at h1
  simp only [map_mul, map_inv] at h1
  rw [hloc, hthL]
  have h2 : ι y₀ = (ι y₀ * ι u₀) * (ι u₀)⁻¹ := by group
  rw [h2, h1]
  simp only [mul_assoc]

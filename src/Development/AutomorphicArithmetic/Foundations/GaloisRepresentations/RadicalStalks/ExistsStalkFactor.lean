module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ArtTangent
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

open Polynomial IsLocalRing in
private lemma art_tangent (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (f : ℕ) (hf : 0 < f) :
    ∃ (τ : AdjoinRoot (X ^ (p ^ f + 1) : k[X]) →ₐ[k] DualNumber k)
      (j : DualNumber k →+* AdjoinRoot (X ^ (p ^ f + 1) : k[X])),
      Function.Injective j ∧ (∀ x, j (τ x) = x ^ p ^ f) ∧
        τ (AdjoinRoot.root (X ^ (p ^ f + 1) : k[X])) = DualNumber.eps := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
  have hq0 : p ^ f ≠ 0 := by omega
  set q := p ^ f with hq
  set P : k[X] := X ^ (q + 1) with hP
  have hdeg : P.degree ≠ 0 := by
    rw [hP, degree_X_pow]
    exact_mod_cast Nat.succ_ne_zero q
  haveI : Nontrivial (AdjoinRoot P) := AdjoinRoot.nontrivial P hdeg
  haveI : CharP (AdjoinRoot P) p := charP_of_injective_algebraMap (algebraMap k (AdjoinRoot P)).injective p
  set r := AdjoinRoot.root P with hr
  have hr0 : r ^ (q + 1) = 0 := by
    rw [hr, AdjoinRoot.root, ← map_pow]
    exact AdjoinRoot.mk_self
  have hrr : r ^ q * r ^ q = 0 := by
    have : q + q = (q + 1) + (q - 1) := by omega
    rw [← pow_add, this, pow_add, hr0, zero_mul]
  have he2 : (DualNumber.eps : DualNumber k) ^ 2 = 0 := by
    rw [pow_two, DualNumber.eps_mul_eps]
  have heq : ∀ n, 2 ≤ n → (DualNumber.eps : DualNumber k) ^ n = 0 := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, he2, zero_mul]
  let τ : AdjoinRoot P →ₐ[k] DualNumber k :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId k (DualNumber k)) DualNumber.eps (by
      simp [hP, heq (q + 1) (by omega)])
  have hτr : τ r = DualNumber.eps := by
    simp [τ, hr, AdjoinRoot.liftAlgHom_root]
  let of := algebraMap k (AdjoinRoot P)
  let j : DualNumber k →+* AdjoinRoot P :=
    { toFun := fun z => of (z.fst ^ q) + of (z.snd ^ q) * r ^ q
      map_one' := by simp [hq0]
      map_zero' := by simp [hq0]
      map_add' := fun z w => by
        simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hq, add_pow_char_pow, map_add (f := _)]
        ring
      map_mul' := fun z w => by
        simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
          MulOpposite.unop_op, hq, add_pow_char_pow, mul_pow, map_add, map_mul]
        rw [← hq]
        linear_combination (-(of (z.snd ^ q) * of (w.snd ^ q))) * hrr }
  have hj : ∀ z, j z = of (z.fst ^ q) + of (z.snd ^ q) * r ^ q := fun _ => rfl
  refine ⟨τ, j, ?_, ?_, hτr⟩
  · refine (injective_iff_map_eq_zero j).2 fun z hz => ?_
    have h1 : z.fst = 0 := by
      have h0 : τ (j z) = algebraMap k (DualNumber k) (z.fst ^ q) := by
        have e : τ (r ^ q) = 0 := by rw [map_pow, hτr, heq q hq2]
        rw [hj, map_add (f := _), map_mul, e, mul_zero, add_zero]
        exact τ.commutes _
      rw [hz, map_zero] at h0
      have h0' := congrArg TrivSqZeroExt.fst h0
      rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl] at h0'
      exact (pow_eq_zero_iff hq0).1 h0'.symm
    rw [hj, h1] at hz
    have h2 : of (z.snd ^ q) * r ^ q = 0 := by
      rwa [zero_pow hq0, map_zero, zero_add] at hz
    have h3 : AdjoinRoot.mk P (C (z.snd ^ q) * X ^ q) = 0 := by
      rw [map_mul, map_pow (AdjoinRoot.mk P) X q]
      exact h2
    rw [AdjoinRoot.mk_eq_zero, hP, X_pow_dvd_iff] at h3
    have h4 := h3 q (by omega)
    rw [coeff_C_mul, coeff_X_pow_self, _root_.mul_one] at h4
    have h5 : z.snd = 0 := (pow_eq_zero_iff hq0).1 h4
    exact TrivSqZeroExt.ext h1 h5
  · have key : j.comp (τ : AdjoinRoot P →+* DualNumber k) = iterateFrobenius (AdjoinRoot P) p f := by
      apply Ideal.Quotient.ringHom_ext
      apply Polynomial.ringHom_ext
      · intro a
        show j (τ (of a)) = iterateFrobenius (AdjoinRoot P) p f (of a)
        rw [τ.commutes, hj, iterateFrobenius_def, ← map_pow, ← hq]
        simp only [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_pow hq0,
          map_zero, zero_mul, add_zero, map_pow]
      · show j (τ r) = iterateFrobenius (AdjoinRoot P) p f r
        rw [hτr, hj, iterateFrobenius_def, ← hq]
        simp [hq0]
    intro x
    have := RingHom.congr_fun key x
    simpa [iterateFrobenius_def] using this

end UpperTheory.Gal.Ord

namespace UpperTheory.Gal.Ord

section ArtB

open Polynomial IsLocalRing
open scoped Classical

variable {k : Type} [Field k] {B : Type} [CommRing B] [IsLocalRing B] [Algebra k B]

private lemma art_alg_mem {c : k} (h : algebraMap k B c ∈ maximalIdeal B) : c = 0 := by
  by_contra hc
  exact (mem_maximalIdeal _).1 h ((IsUnit.mk0 c hc).map (algebraMap k B))

private lemma art_res [IsAlgClosed k] [Module.Finite k B] :
    ∃ π : B →ₐ[k] k, ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B := by
  let K := B ⧸ maximalIdeal B
  letI : Field K := Ideal.Quotient.field _
  haveI : Algebra.IsIntegral k K := Algebra.IsIntegral.of_finite k K
  have hbij : Function.Bijective (algebraMap k K) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) hbij
  refine ⟨(e.symm : K →ₐ[k] k).comp (Ideal.Quotient.mkₐ k _), fun b => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have h := e.apply_symm_apply (Ideal.Quotient.mk (maximalIdeal B) b)
  exact h.symm

private lemma art_der (π : B →ₐ[k] k) (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    (φ : B →ₗ[k] k) (h1 : φ 1 = 0) (h2 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ z = 0) :
    ∃ u : B →ₐ[k] DualNumber k, ∀ b, TrivSqZeroExt.snd (u b) = φ b := by
  have halg : ∀ c b, φ (algebraMap k B c * b) = c * φ b := fun c b => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have halg1 : ∀ c, φ (algebraMap k B c) = 0 := fun c => by
    have := halg c 1
    rwa [_root_.mul_one, h1, mul_zero] at this
  have hmul : ∀ a b, φ (a * b) = π a * φ b + π b * φ a := fun a b => by
    have h := h2 _ (Ideal.mul_mem_mul (hπ a) (hπ b))
    have e : (a - algebraMap k B (π a)) * (b - algebraMap k B (π b)) =
        a * b - algebraMap k B (π a) * b - algebraMap k B (π b) * a + algebraMap k B (π a * π b) := by
      rw [map_mul]; ring
    rw [e, map_add (f := _), map_sub, map_sub, halg, halg, halg1] at h
    linear_combination h
  let L : B →ₗ[k] DualNumber k :=
    { toFun := fun b => TrivSqZeroExt.inl (π b) + TrivSqZeroExt.inr (φ b)
      map_add' := fun a b => by
        ext <;> simp
      map_smul' := fun c b => by
        ext <;> simp }
  refine ⟨AlgHom.ofLinearMap L ?_ ?_, fun b => ?_⟩
  · ext <;> simp [L, h1]
  · intro a b
    ext
    · simp [L]
    · simp [L, hmul]
      ring
  · simp [L]

private lemma art_gen [Module.Finite k B] (π : B →ₐ[k] k)
    (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    (H : ∀ u v : B →ₐ[k] DualNumber k, (∃ x, TrivSqZeroExt.snd (u x) ≠ 0) →
      ∃ l : k, ∀ x, TrivSqZeroExt.snd (v x) = l * TrivSqZeroExt.snd (u x)) :
    ∃ x ∈ maximalIdeal B, maximalIdeal B ≤ Ideal.span {x} := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hfg : (maximalIdeal B).FG := IsNoetherian.noetherian _
  have hjac : maximalIdeal B ≤ (⊥ : Ideal B).jacobson :=
    (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have nak : ∀ x, maximalIdeal B ≤ Ideal.span {x} ⊔ maximalIdeal B * maximalIdeal B →
      maximalIdeal B ≤ Ideal.span {x} := fun x h =>
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac h
  by_cases hm : maximalIdeal B ≤ maximalIdeal B * maximalIdeal B
  · exact ⟨0, Ideal.zero_mem _, nak 0 (hm.trans le_sup_right)⟩
  obtain ⟨x, hxm, hx2⟩ := SetLike.not_le_iff_exists.1 hm
  refine ⟨x, hxm, nak x fun y hy => ?_⟩
  by_contra hy2
  let M2 : Submodule k B := (maximalIdeal B * maximalIdeal B).restrictScalars k
  have hM2 : ∀ z ∈ M2, z ∈ maximalIdeal B := fun z hz => Ideal.mul_le_left hz
  let W1 : Submodule k B := (k ∙ (1 : B)) ⊔ M2
  have hW1 : ∀ z ∈ W1, ∃ c : k, ∃ t ∈ M2, z = algebraMap k B c + t := fun z hz => by
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    exact ⟨c, t, ht, by rw [Algebra.algebraMap_eq_smul_one]⟩
  have hxW : x ∉ W1 := fun h => by
    obtain ⟨c, t, ht, rfl⟩ := hW1 _ h
    have hc : algebraMap k B c ∈ maximalIdeal B := by
      simpa using Ideal.sub_mem _ hxm (hM2 t ht)
    rw [art_alg_mem hc, map_zero, zero_add] at hx2
    exact hx2 ht
  let W2 : Submodule k B := W1 ⊔ (k ∙ x)
  have hyW : y ∉ W2 := fun h => by
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 ht
    obtain ⟨c, s, hs, rfl⟩ := hW1 _ ha
    have hdx : d • x ∈ maximalIdeal B := by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hxm
    have hc : algebraMap k B c ∈ maximalIdeal B := by
      have h3 := Ideal.sub_mem _ (Ideal.sub_mem _ hy (hM2 s hs)) hdx
      have e : algebraMap k B c + s + d • x - s - d • x = algebraMap k B c := by abel
      rwa [e] at h3
    rw [art_alg_mem hc, map_zero, zero_add] at hy2
    apply hy2
    refine Submodule.mem_sup.2 ⟨d • x, ?_, s, hs, add_comm _ _⟩
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨φ₁, hφ₁x, hφ₁⟩ := Submodule.exists_le_ker_of_notMem hxW
  obtain ⟨φ₂, hφ₂y, hφ₂⟩ := Submodule.exists_le_ker_of_notMem hyW
  have h11 : φ₁ 1 = 0 := hφ₁ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1))
  have h12 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ₁ z = 0 := fun z hz =>
    hφ₁ (Submodule.mem_sup_right hz)
  have hW12 : W1 ≤ W2 := le_sup_left
  have h21 : φ₂ 1 = 0 :=
    hφ₂ (hW12 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1)))
  have h22 : ∀ z ∈ maximalIdeal B * maximalIdeal B, φ₂ z = 0 := fun z hz =>
    hφ₂ (hW12 (Submodule.mem_sup_right hz))
  have h2x : φ₂ x = 0 := hφ₂ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  obtain ⟨u, hu⟩ := art_der π hπ φ₁ h11 h12
  obtain ⟨v, hv⟩ := art_der π hπ φ₂ h21 h22
  obtain ⟨l, hl⟩ := H u v ⟨x, by rwa [hu]⟩
  have hl0 : l = 0 := by
    have := hl x
    rw [hu, hv, h2x] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hφ₁x
  have := hl y
  rw [hu, hv, hl0, zero_mul] at this
  exact hφ₂y this

private lemma art_span (π : B →ₐ[k] k) (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    {x : B} (hx : maximalIdeal B ≤ Ideal.span {x}) (n : ℕ) (b : B) :
    ∃ s ∈ Submodule.span k (((Finset.range n).image fun i => x ^ i : Finset B) : Set B),
      ∃ r, b = s + x ^ n * r := by
  induction n with
  | zero => exact ⟨0, Submodule.zero_mem _, b, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, r, rfl⟩ := ih
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hx (hπ r))
    have hmono : Submodule.span k (((Finset.range n).image fun i => x ^ i : Finset B) : Set B) ≤
        Submodule.span k (((Finset.range (n + 1)).image fun i => x ^ i : Finset B) : Set B) := by
      refine Submodule.span_mono ?_
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hz ⊢
      obtain ⟨i, hi, rfl⟩ := hz
      exact ⟨i, by omega, rfl⟩
    have hxn : x ^ n ∈ Submodule.span k (((Finset.range (n + 1)).image fun i => x ^ i : Finset B) : Set B) := by
      refine Submodule.subset_span ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
      exact ⟨n, by omega, rfl⟩
    refine ⟨s + π r • x ^ n, Submodule.add_mem _ (hmono hs) (Submodule.smul_mem _ _ hxn), t, ?_⟩
    have hr : r = algebraMap k B (π r) + t * x := by rw [ht]; ring
    rw [Algebra.smul_def]
    conv_lhs => rw [hr]
    ring

private lemma art_length [Module.Finite k B] (π : B →ₐ[k] k)
    (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    {x : B} (hx : maximalIdeal B ≤ Ideal.span {x}) {q : ℕ} (h0 : x ^ q = 0) :
    Module.length B B ≤ (q : ℕ∞) := by
  have hle : Module.length B B ≤ Module.length k B := by
    rw [Module.length_eq_height, Module.length_eq_height]
    have hs : StrictMono (fun I : Submodule B B => I.restrictScalars k) := fun I J h => by
      refine lt_of_le_of_ne (fun z hz => h.le hz) fun e => h.ne ?_
      exact Submodule.restrictScalars_injective k B B e
    exact Order.height_le_height_apply_of_strictMono _ hs ⊤
  refine hle.trans ?_
  rw [Module.length_eq_finrank]
  have htop : Submodule.span k (((Finset.range q).image fun i => x ^ i : Finset B) : Set B) = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    obtain ⟨s, hs, r, rfl⟩ := art_span π hπ hx q b
    rwa [h0, zero_mul, add_zero]
  have h1 := finrank_span_finset_le_card (R := k) ((Finset.range q).image fun i => x ^ i)
  have h2 : Module.finrank k B ≤ q := by
    calc Module.finrank k B = Set.finrank k (((Finset.range q).image fun i => x ^ i : Finset B) : Set B) := by
          rw [Set.finrank, htop, finrank_top]
      _ ≤ _ := h1
      _ ≤ (Finset.range q).card := Finset.card_image_le
      _ = q := Finset.card_range q
  exact_mod_cast h2

private lemma art_map [Module.Finite k B] (π : B →ₐ[k] k)
    (hπ : ∀ b, b - algebraMap k B (π b) ∈ maximalIdeal B)
    {x : B} (hxm : x ∈ maximalIdeal B) (hx : maximalIdeal B ≤ Ideal.span {x}) {q : ℕ} (hq : x ^ q ≠ 0) :
    ∃ u : B →ₐ[k] AdjoinRoot (X ^ (q + 1) : k[X]), u x = AdjoinRoot.root (X ^ (q + 1) : k[X]) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  have hxN : x ^ N = 0 := by
    have := Ideal.pow_mem_pow hxm N
    rw [hN] at this
    simpa using this
  let ψ : k[X] →ₐ[k] B := aeval x
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨s, hs, r, rfl⟩ := art_span π hπ hx N b
    rw [hxN, zero_mul, add_zero]
    have : Submodule.span k (((Finset.range N).image fun i => x ^ i : Finset B) : Set B) ≤
        LinearMap.range ψ.toLinearMap := by
      refine Submodule.span_le.2 fun z hz => ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hz
      obtain ⟨i, -, rfl⟩ := hz
      exact ⟨X ^ i, by simp [ψ]⟩
    obtain ⟨P, hP⟩ := this hs
    exact ⟨P, hP⟩
  have hker : RingHom.ker ψ.toRingHom ≤
      RingHom.ker (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X])) : k[X] →ₐ[k] _).toRingHom := fun P hP => by
    have hP0 : aeval x P = 0 := hP
    have hdvd : (X ^ (q + 1) : k[X]) ∣ P := by
      by_cases hne : P = 0
      · simp [hne]
      obtain ⟨Q, hQ, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hne 0
      rw [C_0, sub_zero] at hQ hnd
      set e := rootMultiplicity 0 P
      have hc : Q.coeff 0 ≠ 0 := fun h => hnd (X_dvd_iff.2 h)
      have hunit : IsUnit (aeval x Q) := by
        by_contra hu
        have hmem : aeval x Q ∈ maximalIdeal B := (mem_maximalIdeal _).2 hu
        have hdiv := congrArg (aeval x) (divX_mul_X_add Q)
        rw [map_add (f := _), map_mul, aeval_X, aeval_C] at hdiv
        have : algebraMap k B (Q.coeff 0) ∈ maximalIdeal B := by
          have h3 := Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ (aeval x (divX Q)) hxm)
          rwa [← hdiv, add_sub_cancel_left] at h3
        exact hc (art_alg_mem this)
      have hxe : x ^ e = 0 := by
        rw [hQ, map_mul, map_pow, aeval_X] at hP0
        exact (hunit.mul_left_eq_zero).1 hP0
      have hqe : q + 1 ≤ e := by
        by_contra hlt
        apply hq
        have : q = e + (q - e) := by omega
        rw [this, pow_add, hxe, zero_mul]
      rw [hQ]
      exact (pow_dvd_pow X hqe).mul_right Q
    show (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X])) : k[X] →ₐ[k] _) P = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hdvd
  refine ⟨AlgHom.liftOfSurjective ψ hsurj _ hker, ?_⟩
  have := AlgHom.liftOfSurjective_apply ψ hsurj (aeval (AdjoinRoot.root (X ^ (q + 1) : k[X]))) hker X
  have hX : ψ X = x := by simp [ψ]
  rw [hX] at this
  rw [this, aeval_X]

end ArtB

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.art :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (B : Type) [CommRing B] [IsLocalRing B] [Algebra k B] [Module.Finite k B] (f : ℕ), 0 < f →
      (∀ u v : B →ₐ[k] DualNumber k, (∃ x, TrivSqZeroExt.snd (u x) ≠ 0) → ∃ l : k, ∀ x, TrivSqZeroExt.snd (v x) = l * TrivSqZeroExt.snd (u x)) →
      ((p ^ f : ℕ) : ℕ∞) < Module.length B B →
      ∃ (T : Type) (_ : CommRing T) (_ : Algebra k T) (τ : T →ₐ[k] DualNumber k) (j : DualNumber k →+* T) (u : B →ₐ[k] T),
        Function.Injective j ∧ (∀ x, j (τ x) = x ^ p ^ f) ∧ ∃ x, TrivSqZeroExt.snd (τ (u x)) ≠ 0 := by
  intro p _ k _ _ _ B _ _ _ _ f hf H hL
  obtain ⟨π, hπ⟩ := art_res (k := k) (B := B)
  obtain ⟨x, hxm, hx⟩ := art_gen π hπ H
  have hxq : x ^ p ^ f ≠ 0 := fun h => not_le.2 hL (art_length π hπ hx h)
  obtain ⟨τ, j, hj, hjτ, hτ⟩ := art_tangent p k f hf
  obtain ⟨u, hu⟩ := art_map π hπ hxm hx hxq
  refine ⟨_, inferInstance, inferInstance, τ, j, u, hj, hjτ, x, ?_⟩
  rw [hu, hτ]
  simp
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace UpperTheory.Gal.Ord.CntStalk

variable {k : Type} [Field k]

private theorem exists_stalk_factor {X : Scheme.{0}} (x : X) {T : Type} [CommRing T] [IsLocalRing T] (g : Sp T ⟶ X)
    (hx : g (IsLocalRing.closedPoint T) = x) :
    ∃ u : X.presheaf.stalk x →+* T, Spec.map (CommRingCat.ofHom u) ≫ X.fromSpecStalk x = g := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo g).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk g⟩

private def stalkAlg (K : Over (Sp k)) (x : K.left) : CommRingCat.of k ⟶ K.left.presheaf.stalk x :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ K.hom.appTop ≫ K.left.presheaf.germ ⊤ x trivial

private theorem spec_stalkAlg (K : Over (Sp k)) (x : K.left) :
    Spec.map (stalkAlg K x) = K.left.fromSpecStalk x ≫ K.hom := by
  rw [stalkAlg, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

private theorem stalkAlg_finite (K : Over (Sp k)) [IsFinite K.hom] (x : K.left) : (stalkAlg K x).hom.Finite := by
  have hA : IsAffine K.left := isAffine_of_isAffineHom K.hom
  have h1 : K.hom.appTop.hom.Finite := K.hom.finite_appTop
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  have h01 : (K.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite := h1.comp h0
  letI : Algebra k Γ(K.left, ⊤) := (K.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  haveI : Module.Finite k Γ(K.left, ⊤) := h01
  haveI : IsArtinianRing Γ(K.left, ⊤) := IsArtinianRing.of_finite k _
  letI := TopCat.Presheaf.algebra_section_stalk K.left.presheaf (⟨x, trivial⟩ : (⊤ : K.left.Opens))
  have hloc := (isAffineOpen_top K.left).isLocalization_stalk ⟨x, trivial⟩
  have hs : Function.Surjective (algebraMap Γ(K.left, ⊤) (K.left.presheaf.stalk x)) :=
    IsArtinianRing.localization_surjective ((isAffineOpen_top K.left).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _
  have h2 : (K.left.presheaf.germ ⊤ x trivial).hom.Finite := RingHom.Finite.of_surjective _ hs
  exact h2.comp h01

@[reducible] private def stalkAlgebra (K : Over (Sp k)) (x : K.left) : Algebra k (K.left.presheaf.stalk x) :=
  (stalkAlg K x).hom.toAlgebra

attribute [local instance] stalkAlgebra

private def stalkPt (K : Over (Sp k)) (x : K.left) :
    Over.mk (spMap (algebraMap k (K.left.presheaf.stalk x))) ⟶ K :=
  Over.homMk (K.left.fromSpecStalk x) (spec_stalkAlg K x).symm

private theorem exists_alg (K : Over (Sp k)) (x : K.left) {T : Type} [CommRing T] [IsLocalRing T] [Algebra k T]
    (g : Over.mk (spMap (algebraMap k T)) ⟶ K) (hx : g.left (IsLocalRing.closedPoint T) = x) :
    ∃ u : K.left.presheaf.stalk x →ₐ[k] T, spOver u ≫ stalkPt K x = g := by
  obtain ⟨u, hu⟩ := exists_stalk_factor x g.left hx
  let u' : K.left.presheaf.stalk x ⟶ CommRingCat.of T := CommRingCat.ofHom u
  have hc : stalkAlg K x ≫ u' = CommRingCat.ofHom (algebraMap k T) := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_stalkAlg, ← Category.assoc]
    exact (congrArg (· ≫ K.hom) hu).trans (Over.w g)
  refine ⟨{ u with commutes' := fun a => ?_ }, ?_⟩
  · exact congrArg (fun f => f.hom a) hc
  · apply Over.OverMorphism.ext
    exact hu

private theorem closed_eps : (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (IsLocalRing.closedPoint k) =
    IsLocalRing.closedPoint (DualNumber k) := by
  haveI : IsLocalHom (TrivSqZeroExt.fstHom k k k).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  exact Spec_closedPoint (R := CommRingCat.of (DualNumber k)) (S := CommRingCat.of k)
    (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

private theorem exists_stalkPt [IsAlgClosed k] (K : Over (Sp k)) [GrpObj K] [IsFinite K.hom] :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra k B) (_ : Module.Finite k B)
      (y : Over.mk (spMap (algebraMap k B)) ⟶ K),
      Mono y.left ∧
      (∀ x : K.left, Module.length (K.left.presheaf.stalk x) (K.left.presheaf.stalk x) = Module.length B B) ∧
      (∃ c : B →ₐ[k] k, spOver c ≫ y = 1) ∧
      ∀ v : epsR k ⟶ K, IsTangent v → ∃ u : B →ₐ[k] DualNumber k, spOver u ≫ y = v := by
  set g₁ : Over.mk (spMap (algebraMap k k)) ⟶ K := 1 with hg₁
  set x₀ : K.left := g₁.left (IsLocalRing.closedPoint k) with hx₀
  haveI : Module.Finite k (K.left.presheaf.stalk x₀) := stalkAlg_finite K x₀
  obtain ⟨c, hc⟩ := exists_alg K x₀ g₁ rfl
  refine ⟨K.left.presheaf.stalk x₀, inferInstance, inferInstance, inferInstance, inferInstance, stalkPt K x₀,
    ?_, fun x => GlobalTheory.T.finite_group_scheme_stalk_length_constant k K inferInstance x x₀, ⟨c, hc⟩, fun v hv => ?_⟩
  · show Mono (K.left.fromSpecStalk x₀)
    infer_instance
  · apply exists_alg
    have h1 : spMap (algebraMap k k) = 𝟙 (Sp k) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hg : g₁.left = Over.Hom.left η := by
      rw [hg₁, GlobalTheory.HTSummand.LieMod.one_left, h1, Category.id_comp]
    unfold IsTangent at hv
    rw [← closed_eps, hx₀, hg, ← hv]
    rfl

end UpperTheory.Gal.Ord.CntStalk

namespace UpperTheory.Gal.Ord.CntLie

private theorem lie_line (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (hN : 3 ≤ N) (hNp : N.Coprime p) (hm : D.m = 1)
    (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ)
    (hw : RingHom.ker (β.comp (b.t i)) = w) (hq : Ideal.absNorm w = p ^ f) (hf : 0 < f) (π : Par p w f) :
    (∃ v₀ : epsR k ⟶ o.A, IsTangent v₀ ∧ v₀ ≠ 1 ∧ KilledBy o w v₀) ∧
    ∀ v₁ v₂ : epsR k ⟶ o.A, IsTangent v₁ → IsTangent v₂ → KilledBy o w v₁ → KilledBy o w v₂ → v₁ ≠ 1 →
      ∃ l : k, v₂ = GlobalTheory.GrpTangent.epsScale l ≫ v₁ := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o.A o.ab
  have HL : LieExact o.A := (GlobalTheory.abelianDeRham.2.1 k o.A g o.ab hg).1
  let a := OActN.toF D o.act
  have e1 : ∀ (c : 𝓞 D.F) (V : GlobalTheory.Serre.Lie a), (c • V).hom = V.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) :=
    fun c V => rfl
  have e2 : ∀ (l : k) (V : GlobalTheory.Serre.Lie a), (l • V).hom = GlobalTheory.GrpTangent.epsScale l ≫ V.hom := fun l V => rfl
  have e3 : (0 : GlobalTheory.Serre.Lie a).hom = 1 := rfl
  obtain ⟨h1, ⟨h₀, hne, hspan⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hq hf π
  set T := HL.toLie a with hT
  have Tker : ∀ h, T h = 0 ↔ h ∈ Fil o.A := fun h => by
    rw [← LinearMap.mem_ker, hT, LieExact.ker_toLie]
  have Tcrys : ∀ (c : 𝓞 D.F) h, T (UpperTheory.Gal.Ord.hom o c h) = c • T h := fun c h =>
    GlobalTheory.HTLieRho.toLie_crys o HL c h
  have hzero : ∀ c ∈ w, β (b.t i c) = 0 := fun c hc => by
    rw [← hw] at hc
    exact RingHom.mem_ker.mp hc
  have stepA : ∀ c ∈ w, ∀ h, c • T (UpperTheory.Gal.Ord.hom o π.ε h) = 0 := fun c hc h => by
    rw [← Tcrys, Tker]
    have := h1 c h
    rwa [hzero c hc, zero_smul, sub_zero] at this
  have killed : ∀ (V : GlobalTheory.Serre.Lie a), KilledBy o w V.hom → ∀ c ∈ w, c • V = 0 := fun V hV c hc =>
    GlobalTheory.Serre.Lie.ext (by rw [e1, e3]; exact hV c hc)
  have stepB : ∀ V : GlobalTheory.Serre.Lie a, (∀ c ∈ w, c • V = 0) → ∃ h, V = T (UpperTheory.Gal.Ord.hom o π.ε h) := fun V hV => by
    obtain ⟨h', rfl⟩ := LieExact.toLie_surjective HL a V
    refine ⟨h', ?_⟩
    rw [Tcrys]
    have h2 := hV (π.ε - 1) π.one
    rw [sub_smul, one_smul, sub_eq_zero] at h2
    exact h2.symm
  have stepC : ∀ h, ∃ l : k, T (UpperTheory.Gal.Ord.hom o π.ε h) = l • T (UpperTheory.Gal.Ord.hom o π.ε h₀) := fun h => by
    obtain ⟨l, hl⟩ := hspan h
    refine ⟨l, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Tker]
    exact hl
  have ne0 : T (UpperTheory.Gal.Ord.hom o π.ε h₀) ≠ 0 := fun h => hne ((Tker _).mp h)
  refine ⟨⟨(T (UpperTheory.Gal.Ord.hom o π.ε h₀)).hom, (T (UpperTheory.Gal.Ord.hom o π.ε h₀)).isTangent,
    fun h => ne0 (GlobalTheory.Serre.Lie.ext (by rw [h, e3])), ?_⟩, ?_⟩
  · intro c hc
    rw [← e1, stepA c hc, e3]
  · intro v₁ v₂ hv₁ hv₂ hk₁ hk₂ hne₁
    obtain ⟨g₁, hg₁⟩ := stepB _ (killed (GlobalTheory.Serre.Lie.mk a v₁ hv₁) hk₁)
    obtain ⟨g₂, hg₂⟩ := stepB _ (killed (GlobalTheory.Serre.Lie.mk a v₂ hv₂) hk₂)
    obtain ⟨l₁, hl₁⟩ := stepC g₁
    obtain ⟨l₂, hl₂⟩ := stepC g₂
    have hl₁0 : l₁ ≠ 0 := by
      rintro rfl
      apply hne₁
      have := congrArg GlobalTheory.Serre.Lie.hom (hg₁.trans hl₁)
      rw [zero_smul, e3] at this
      exact this
    refine ⟨l₂ / l₁, ?_⟩
    have h3 : GlobalTheory.Serre.Lie.mk a v₂ hv₂ = (l₂ / l₁) • GlobalTheory.Serre.Lie.mk a v₁ hv₁ := by
      rw [hg₂, hl₂, hg₁, hl₁, smul_smul, div_mul_cancel₀ _ hl₁0]
    have := congrArg GlobalTheory.Serre.Lie.hom h3
    rw [e2] at this
    exact this

end UpperTheory.Gal.Ord.CntLie

namespace UpperTheory.Gal.Ord.CntPt

variable {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B] {A : Over (Sp k)} [GrpObj A]

private theorem algHom_unique [IsLocalRing B] (c c' : B →ₐ[k] k) : c = c' := by
  have key : ∀ d : B →ₐ[k] k, RingHom.ker d.toRingHom = IsLocalRing.maximalIdeal B := fun d =>
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨algebraMap k B a, by simp⟩))
  ext b
  have hm : b - algebraMap k B (c b) ∈ RingHom.ker c'.toRingHom := by
    rw [key c', ← key c, RingHom.mem_ker]
    simp
  rw [RingHom.mem_ker] at hm
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at hm
  exact hm.symm

private abbrev fstA : DualNumber k →ₐ[k] k := TrivSqZeroExt.fstHom k k k

private abbrev inlA : k →ₐ[k] DualNumber k := Algebra.ofId k _

private def scA (l : k) : DualNumber k →ₐ[k] DualNumber k :=
  { epsScaleR l with
    commutes' := fun a => by
      simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl] }

private theorem snd_scA (l : k) (x : DualNumber k) : TrivSqZeroExt.snd (scA l x) = l * TrivSqZeroExt.snd x := by
  show TrivSqZeroExt.snd (epsScaleR l x) = _
  simp [epsScaleR]

private theorem spOver_inj (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (hz : Mono z.left) {T : Type} [CommRing T] [Algebra k T]
    {u u' : B →ₐ[k] T} (h : spOver u ≫ z = spOver u' ≫ z) : u = u' := by
  have h1 := congrArg (fun f => f.left) h
  simp only [Over.comp_left] at h1
  have h2 : (spOver u).left = (spOver u').left := (cancel_mono z.left).mp h1
  have h3 : CommRingCat.ofHom (u : B →+* T) = CommRingCat.ofHom (u' : B →+* T) := Spec.map_injective h2
  ext b
  exact congrArg (fun f => f.hom b) h3

private theorem tangent_of [IsLocalRing B] (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (c : B →ₐ[k] k) (hc : spOver c ≫ z = 1)
    (u : B →ₐ[k] DualNumber k) : IsTangent (spOver u ≫ z) := by
  have hcu : (fstA (k := k)).comp u = c := algHom_unique _ _
  have h1 := congrArg (fun f => f.left) hc
  simp only [Over.comp_left, GlobalTheory.HTSummand.LieMod.one_left] at h1
  have h2 : (spOver (fstA (k := k)) ≫ spOver u).left = (spOver c).left := by
    rw [spOver_comp, hcu]
  rw [Over.comp_left] at h2
  unfold IsTangent
  rw [Over.comp_left, ← Category.assoc]
  erw [h2, h1]
  simp only [Algebra.algebraMap_self]
  show Spec.map (CommRingCat.ofHom (RingHom.id k)) ≫ _ = _
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

private theorem const_eq_one (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (c : B →ₐ[k] k) (hc : spOver c ≫ z = 1) :
    spOver (inlA.comp c) ≫ z = (1 : epsR k ⟶ A) := by
  have h1 := congrArg (fun f => f.left) hc
  simp only [Over.comp_left, GlobalTheory.HTSummand.LieMod.one_left] at h1
  have hw := Over.w (spOver (inlA (k := k)))
  simp only [Over.mk_hom] at hw
  apply Over.OverMorphism.ext
  rw [GlobalTheory.HTSummand.LieMod.one_left, ← spOver_comp, Category.assoc, Over.comp_left, Over.comp_left, h1,
    ← Category.assoc, hw]

private theorem eq_const_of_one (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (hz : Mono z.left) (c : B →ₐ[k] k)
    (hc : spOver c ≫ z = 1) (u : B →ₐ[k] DualNumber k) (h : spOver u ≫ z = (1 : epsR k ⟶ A)) :
    ∀ x, TrivSqZeroExt.snd (u x) = 0 := by
  have := spOver_inj z hz (h.trans (const_eq_one z c hc).symm)
  intro x
  rw [this]
  simp [inlA, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]

private theorem scale_comp (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (l : k) (u : B →ₐ[k] DualNumber k) :
    GlobalTheory.GrpTangent.epsScale l ≫ spOver u ≫ z = spOver ((scA l).comp u) ≫ z := by
  have he : GlobalTheory.GrpTangent.epsScale l = spOver (scA l) := Over.OverMorphism.ext rfl
  rw [he, ← Category.assoc, spOver_comp]

private theorem const_of_length [IsLocalRing B] (h : Module.length B B = 1) (c : B →ₐ[k] k) (u : B →ₐ[k] DualNumber k) :
    u = inlA.comp c := by
  have hs := (isSimpleModule_self_iff_isUnit.mp (Module.length_eq_one_iff.mp h)).2
  refine AlgHom.ext fun b => ?_
  have hb : b = algebraMap k B (c b) := by
    by_contra hne
    have hu := (hs (b - algebraMap k B (c b)) (sub_ne_zero.mpr hne)).map c
    simp at hu
  rw [hb, AlgHom.commutes, AlgHom.commutes]

end UpperTheory.Gal.Ord.CntPt

theorem UpperTheory.Gal.Ord.cnt :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      IsWOrd o w (𝟙 (Sp k)) ∨ ∃ v : epsR k ⟶ o.A, IsTangent v ∧ v ≠ 1 ∧ IsDeep o w (p ^ f) v := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i₀ w f hw hq hf π
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hk
  have hPne : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : p.Prime).ne_zero
  have hP2 : 2 ≤ p ^ f := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hf.ne' p)
  have hwP : w.IsPrime := hw ▸ RingHom.ker_isPrime _
  have hpw : ((p : ℕ) : 𝓞 D.F) ∈ w := by
    rw [← hw, RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast, hk]
  have hw0 : w ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hq
    exact hPne hq.symm
  have hwM : w.IsMaximal := hwP.isMaximal hw0
  obtain ⟨K, _, i, hiMon, hiMono, hdeg, hiff⟩ := GlobalTheory.HTTors.htTorsion p D R b N (Sp k) (spMap β) o w hw0
  have hKiff : ∀ (T : Over (Sp k)) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ KilledBy o w x := fun T x =>
    (hiff T x).trans ((GlobalTheory.HTTors.killedBy_map o w x).trans Iff.rfl)
  have hqK : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  haveI : IsFinite K.hom := hqK ▸ hdeg.fin
  obtain ⟨B, _, _, _, _, y, hyMono, hlen, ⟨c, hc⟩, hfac⟩ := UpperTheory.Gal.Ord.CntStalk.exists_stalkPt K
  let z : Over.mk (spMap (algebraMap k B)) ⟶ o.A := y ≫ i
  have hzMono : Mono z.left := by
    show Mono (y ≫ i).left
    rw [Over.comp_left]
    exact mono_comp _ _
  have hzc : spOver c ≫ z = 1 := by
    show spOver c ≫ y ≫ i = 1
    rw [← Category.assoc, hc]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.HTSummand.LieMod.one_left, GlobalTheory.HTSummand.LieMod.one_left, Category.assoc]
    congr 1
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hkill : ∀ {T : Type} [CommRing T] [Algebra k T] (u : B →ₐ[k] T), KilledBy o w (spOver u ≫ z) := by
    intro T _ _ u
    exact (hKiff _ _).mp ⟨spOver u ≫ y, Category.assoc _ _ _⟩
  let pt : ↥(Sp k) := IsLocalRing.closedPoint k
  have hI := GlobalTheory.T.finrank_fiber_eq_card_sections_mul_length k K.left K.hom inferInstance (Module.length B B) hlen pt
  have hrank : Scheme.Hom.finrank K.hom pt = (Ideal.absNorm w ^ D.m) ^ D.n := by
    rw [← hqK]
    exact hdeg.rank pt
  rw [hrank, hm, pow_one, hq] at hI
  let e₁ : (Over.mk (𝟙 (Sp k)) ⟶ K) ≃ {s : Sp k ⟶ K.left // s ≫ K.hom = 𝟙 (Sp k)} :=
    { toFun := fun g => ⟨g.left, by simpa using Over.w g⟩
      invFun := fun s => Over.homMk s.1 (by simpa using s.2)
      left_inv := fun g => Over.OverMorphism.ext rfl
      right_inv := fun s => rfl }
  let e₂ := GlobalTheory.UPel.HT.ES.OrdCount.subEquiv (T := Over.mk (𝟙 (Sp k))) i
    (fun g : Over.mk (𝟙 (Sp k)) ⟶ o.A => KilledBy o w g) (hKiff _)
  have hcard : Nat.card {s : Sp k ⟶ K.left // s ≫ K.hom = 𝟙 (Sp k)} =
      Nat.card {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} :=
    (Nat.card_congr e₁.symm).trans (Nat.card_congr e₂)
  rw [hcard] at hI
  set M := Nat.card {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} with hM
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, zero_mul] at hI
    exact pow_ne_zero _ hPne (by exact_mod_cast hI)
  obtain ⟨L, hL⟩ : ∃ L : ℕ, Module.length B B = L := by
    have hne : Module.length B B ≠ ⊤ := by
      intro htop
      rw [htop, ENat.mul_top (by exact_mod_cast hM0)] at hI
      exact ENat.coe_ne_top _ hI
    obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.mp hne
    exact ⟨L, hL.symm⟩
  rw [hL] at hI
  have hIN : (p ^ f) ^ D.n = M * L := by exact_mod_cast hI
  let ψ := o.act.act (algebraMap (𝓞 D.F) D.O ((p : ℕ) : 𝓞 D.F))
  have eψ : {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} ≃
      {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} :=
    Equiv.subtypeEquivRight fun g => ⟨fun h => h.2, fun h => ⟨h _ hpw, h⟩⟩
  haveI : Finite {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} := Nat.finite_of_card_ne_zero hM0
  haveI : Finite {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} := Finite.of_equiv _ eψ.symm
  obtain ⟨j', hj'⟩ := GlobalTheory.UPel.HT.ES.card_kerW_eq_pow o o ψ (o.act.hom _)
    (fun a => by rw [← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]) w hwM (𝟙 (Sp k)) inferInstance
  have hMpow : M = (p ^ f) ^ j' := by
    rw [hM, ← Nat.card_congr eψ, hj', hq]
  obtain ⟨⟨v₀, hv₀t, hv₀1, hv₀k⟩, hline⟩ :=
    UpperTheory.Gal.Ord.CntLie.lie_line p D R b N hN hNp hm k hk β o i₀ w f hw hq hf π
  obtain ⟨v₀', hv₀'⟩ := (hKiff _ v₀).mpr hv₀k
  have hv₀'t : IsTangent v₀' := by
    unfold IsTangent at hv₀t ⊢
    apply (cancel_mono i.left).mp
    rw [Category.assoc, ← Over.comp_left, hv₀', hv₀t, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨u₀, hu₀⟩ := hfac v₀' hv₀'t
  have hL1 : L ≠ 1 := by
    intro hL1
    have hlen1 : Module.length B B = 1 := by rw [hL, hL1]; rfl
    have hu := UpperTheory.Gal.Ord.CntPt.const_of_length hlen1 c u₀
    apply hv₀1
    rw [← hv₀', ← hu₀, hu, Category.assoc]
    exact UpperTheory.Gal.Ord.CntPt.const_eq_one z c hzc
  have hdim : ∀ (u v : B →ₐ[k] DualNumber k), (∃ x, TrivSqZeroExt.snd (u x) ≠ 0) →
      ∃ l : k, ∀ x, TrivSqZeroExt.snd (v x) = l * TrivSqZeroExt.snd (u x) := by
    intro u v ⟨x, hx⟩
    have h1 : spOver u ≫ z ≠ 1 := fun h => hx (UpperTheory.Gal.Ord.CntPt.eq_const_of_one z hzMono c hzc u h x)
    obtain ⟨l, hl⟩ := hline _ _ (UpperTheory.Gal.Ord.CntPt.tangent_of z c hzc u) (UpperTheory.Gal.Ord.CntPt.tangent_of z c hzc v)
      (hkill u) (hkill v) h1
    rw [UpperTheory.Gal.Ord.CntPt.scale_comp] at hl
    have hv := UpperTheory.Gal.Ord.CntPt.spOver_inj z hzMono hl
    refine ⟨l, fun x => ?_⟩
    rw [hv]
    exact UpperTheory.Gal.Ord.CntPt.snd_scA l (u x)
  by_cases hlt : ((p ^ f : ℕ) : ℕ∞) < Module.length B B
  · right
    obtain ⟨T, _, _, τ, j, u, hj, hpow, x, hx⟩ := UpperTheory.Gal.Ord.art p k B f hf hdim hlt
    refine ⟨spOver (τ.comp u) ≫ z, UpperTheory.Gal.Ord.CntPt.tangent_of z c hzc _,
      fun h => hx (UpperTheory.Gal.Ord.CntPt.eq_const_of_one z hzMono c hzc _ h x),
      T, inferInstance, inferInstance, τ, j, spOver u ≫ z, hj, hpow, hkill u, ?_⟩
    rw [← spOver_comp, Category.assoc]
    rfl
  · left
    push_neg at hlt
    have hLle : L ≤ p ^ f := by
      rw [hL] at hlt
      exact_mod_cast hlt
    have hL0 : L ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hIN
      exact pow_ne_zero _ hPne hIN
    have hjle : j' ≤ D.n := by
      by_contra hcon
      push_neg at hcon
      have h1 : (p ^ f) ^ D.n < (p ^ f) ^ j' := Nat.pow_lt_pow_right hP2 hcon
      have h2 : (p ^ f) ^ j' ≤ (p ^ f) ^ j' * L := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hL0)
      rw [hIN, hMpow] at h1
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    have hLeq : L = (p ^ f) ^ (D.n - j') := by
      have h3 : (p ^ f) ^ D.n = (p ^ f) ^ j' * (p ^ f) ^ (D.n - j') := by
        rw [← pow_add, Nat.add_sub_cancel' hjle]
      rw [hIN, hMpow] at h3
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hPne) j') h3
    have hd : D.n - j' = 1 := by
      rcases Nat.lt_trichotomy (D.n - j') 1 with h | h | h
      · exfalso
        apply hL1
        rw [hLeq, Nat.lt_one_iff.mp h, pow_zero]
      · exact h
      · exfalso
        have h4 : (p ^ f) ^ 2 ≤ (p ^ f) ^ (D.n - j') := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hPne) h
        have h5 : p ^ f < (p ^ f) ^ 2 := by
          rw [pow_two]
          nlinarith
        have h6 : (p ^ f) ^ (D.n - j') ≤ p ^ f := by
          rw [← hLeq]
          exact hLle
        exact absurd (lt_of_lt_of_le h5 (h4.trans h6)) (lt_irrefl _)
    have hjn : j' = D.n - 1 := by omega
    refine ⟨inferInstance, hwP, hpw, ?_⟩
    show M = _
    rw [hMpow, hjn, hm, Nat.one_mul, hq]

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PVdmSplit
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.vdmSplit_of :
    PairSplit → VdmSplit := by
  intro h R _ n g i
  have key := h R n (fun a b => g a - g b) i
  have h1 : ∀ k ∈ univ.erase i, (if k < i then g k - g i else g i - g k) =
      (if k < i then (-1 : R) else 1) * (g i - g k) := by
    intro k _
    split_ifs <;> ring
  have h2 : ∏ k ∈ univ.erase i, (if k < i then (-1 : R) else 1) = (-1) ^ (i : ℕ) := by
    have hf : (univ.erase i).filter (· < i) = Finset.Iio i := by
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio]
      exact ⟨fun hk => hk.2, fun hk => ⟨ne_of_lt hk, hk⟩⟩
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, hf, Fin.card_Iio]
  unfold vdm vdmAway
  rw [key, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, h2]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffRed
open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

end UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrRed_of :
    OffClrPow → OffClrRed := by
  intro h R _ _ n lam g y
  have key := h (Polynomial R) n lam (fun k => Polynomial.C (g k)) Polynomial.X
  have key' := (Polynomial.isRegular_X_pow ((n - 1).choose 2)).left key
  let φ : Polynomial R →ₐ[ℚ] R := (Polynomial.evalRingHom y).toRatAlgHom
  have hφ : ∀ (f : Fin n → Polynomial R) (p : MvPolynomial (Fin n) ℚ),
      φ (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun k => φ (f k)) p := by
    intro f p
    rw [← MvPolynomial.comp_aeval]
    rfl
  have hC : ∀ r : R, φ (Polynomial.C r) = r := fun r => by simp [φ]
  have hX : φ Polynomial.X = y := by simp [φ]
  have hs : ∀ i, (fun k => φ (scaleOff Polynomial.X i (fun k => Polynomial.C (g k)) k)) = scaleOff y i g := by
    intro i
    funext k
    simp only [scaleOff]
    split_ifs
    · simp [hC]
    · rw [map_mul, hC, hX]
  have := congrArg φ key'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, map_sub, map_neg, map_one, sch, hφ, vdmAway, vdm,
    hs, hC, hX] at this
  simpa [sch, vdmAway, vdm] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanProd
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.spanProd_of :
    SpanE → SpanProd := by
  intro hS K ι _ _ _ n P hP
  choose k0 hk0 using fun t => hS K n (P t) (hP t)
  refine ⟨univ.sup k0, fun k hk => ?_⟩
  have hle : ∀ t, k0 t ≤ k := fun t => (le_sup (mem_univ t)).trans hk
  choose w hw using fun t => hk0 t k (hle t)
  refine ⟨fun m => ∏ t, (w t (fun s => m (t, s)) * ∏ s, (-1 : K) ^ ((m (t, s) : Fin (n + 1)) : ℕ)), ?_⟩
  intro R _ _ g
  have step : ∀ t, aeval (g t) (P t) = ∑ m : Fin k → Fin (n + 1),
      (w t m * ∏ s, (-1 : K) ^ (m s : ℕ)) • ∏ s, ((-1) ^ (m s : ℕ) * aeval (g t) (esymm (Fin n) K (m s))) := by
    intro t
    conv_lhs => rw [hw t]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_prod]
    refine sum_congr rfl fun m _ => ?_
    rw [prod_mul_distrib, Algebra.smul_def, Algebra.smul_def, map_mul, map_prod]
    simp only [map_pow, map_neg, map_one]
    have hc : (∏ s, (-1 : R) ^ (m s : ℕ)) * ∏ s, (-1 : R) ^ (m s : ℕ) = 1 := by
      rw [← prod_mul_distrib]
      simp [← mul_pow]
    linear_combination (-(algebraMap K R (w t m) * ∏ s, aeval (g t) (esymm (Fin n) K (m s)))) * hc
  simp only [step]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.curry ι (Fin k) (Fin (n + 1))).symm _ _ fun M => ?_
  rw [Fintype.prod_prod_type]
  simp only [Equiv.curry_symm_apply, Function.uncurry_apply_pair, Algebra.smul_def, map_prod,
    prod_mul_distrib]
  rw [← map_prod, prod_mul_distrib]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PESpan
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem elementary_span_mul (K : Type) [CommRing K] (n k l : ℕ)
    (P Q : MvPolynomial (Fin n) K) (hP : P ∈ eSpan K n k) (hQ : Q ∈ eSpan K n l) :
    P * Q ∈ eSpan K n (k + l) := by
  have hmem : P * Q ∈ eSpan K n k * eSpan K n l := Submodule.mul_mem_mul hP hQ
  have hle : eSpan K n k * eSpan K n l ≤ eSpan K n (k + l) := by
    unfold eSpan
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
    refine ⟨Fin.append m m', ?_⟩
    simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  exact hle hmem

private theorem one_mem_eSpan (K : Type) [CommRing K] (n j : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n j := by
  unfold eSpan
  apply Submodule.subset_span
  refine ⟨fun _ => 0, ?_⟩
  simp [esymm_zero]

theorem eSpanMul : ESpanMul := by
  intro K _ n
  refine ⟨fun k l hkl => ?_, fun k l P Q hP hQ => elementary_span_mul K n k l P Q hP hQ⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  intro P hP
  simpa using elementary_span_mul K n k d P 1 hP (one_mem_eSpan K n d)

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PHomog
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMulOfIsHomogeneous
theorem UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous :
    ∀ {σ R : Type} [Fintype σ]
    [inst : CommRing R] [inst_1 : Algebra ℚ R] {P : MvPolynomial σ ℚ} {d : ℕ},
    P.IsHomogeneous d →
      ∀ (y : R) (g : σ → R),
        (MvPolynomial.aeval fun (k : σ) ↦ y * g k : MvPolynomial σ ℚ → R) P =
          y ^ d * (MvPolynomial.aeval g : MvPolynomial σ ℚ → R) P := by
  intro σ R _ _ _ P d hP y g
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : s.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hs) (hP.coeff_eq_zero h)
  have h2 : ∑ i, s i = d := by
    rw [← h1, Finsupp.degree_eq_sum]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h2]
  ring
end

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem aeval_mul_of_isHomogeneous {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℚ R]
    {P : MvPolynomial σ ℚ} {d : ℕ} (hP : P.IsHomogeneous d) (y : R) (g : σ → R) :
    aeval (fun k => y * g k) P = y ^ d * aeval g P :=
  _root_.UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous hP y g

theorem schurHomog : SchurHomog := by
  intro R _ _ n lam g y
  unfold sch
  exact aeval_mul_of_isHomogeneous
    (GroundTheory.Heights₂.Heights.RestTerms.SchSchurHomogeneous.proof (Fin n) n lam) y g

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurDetOf
open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

private lemma vdm_X_ne (n : ℕ) : vdm (X : Fin n → MvPolynomial (Fin n) ℚ) ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  exact sub_ne_zero.2 (MvPolynomial.X_injective.ne (Finset.mem_Ioi.1 hj).ne)

private lemma aeval_sch {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (lam : Fin n → ℕ)
    (g : Fin n → R) :
    aeval g (sch lam (X : Fin n → MvPolynomial (Fin n) ℚ)) = sch lam g := by
  unfold sch
  rw [MvPolynomial.aeval_X_left_apply]

private lemma altn_zero {R : Type} [CommRing R] {n : ℕ} (g : Fin n → R) :
    altn (shift fun _ => 0) g = vdm g := by
  have h := GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_staircase_eq_vandermondeOf g
  have h' : vdm g = GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf g := rfl
  unfold altn
  rw [h']
  simpa [shift] using h

private lemma altn_add {R : Type} [CommRing R] {n : ℕ} (lam : Fin n → ℕ) (m : ℕ) (g : Fin n → R) :
    altn (shift fun i => lam i + m) g = (∏ k, g k) ^ m * altn (shift lam) g := by
  unfold altn
  have h : (Matrix.of fun i j : Fin n => g j ^ (shift (fun i => lam i + m)) i) =
      Matrix.of fun i j : Fin n =>
        g j ^ m * (Matrix.of fun i j : Fin n => g j ^ (shift lam) i) i j := by
    ext i j
    simp only [Matrix.of_apply, shift]
    rw [← pow_add]
    congr 1
    omega
  rw [h, Matrix.det_mul_row, Finset.prod_pow]

private lemma sch_zero_X (tie : Comparison₂) (n : ℕ) :
    sch (fun _ => 0) (X : Fin n → MvPolynomial (Fin n) ℚ) = 1 := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun _ => 0) X
  rw [altn_zero] at h
  exact mul_right_cancel₀ (vdm_X_ne n) (h.trans (one_mul _).symm)

private lemma sch_add_X (tie : Comparison₂) (n : ℕ) (lam : Fin n → ℕ) (m : ℕ) :
    sch (fun i => lam i + m) (X : Fin n → MvPolynomial (Fin n) ℚ) =
      (∏ k, (X k : MvPolynomial (Fin n) ℚ)) ^ m * sch lam X := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun i => lam i + m) X
  rw [altn_add, ← tie (MvPolynomial (Fin n) ℚ) n lam X, ← mul_assoc] at h
  exact mul_right_cancel₀ (vdm_X_ne n) h

theorem schurDet_of :
    Comparison₂ → SchurDet := by
  intro tie R _ _ n g
  refine ⟨?_, fun lam m => ?_⟩
  · rw [← aeval_sch, sch_zero_X tie, map_one]
  · rw [← aeval_sch, sch_add_X tie, map_mul, map_pow, map_prod, aeval_sch]
    simp only [aeval_X]

end UpperTheory.Gal.Schur
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibre
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private lemma prod_scaleOff {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleOff y i g k = y ^ (n - 1) * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h : ∏ k ∈ univ.erase i, scaleOff y i g k = ∏ k ∈ univ.erase i, (y * g k) :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleOff, (mem_erase.1 hk).1])
  rw [h, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]
  simp only [scaleOff, if_true]
  ring

theorem fibre_of : SchurY → SchurHomog → SchurDet → Fibre := by
  intro hY hH hD R ι _ _ _ _ n t₀ t₁ h01 ε lam m hm g y hu
  have hconst : ∀ h : Fin n → R, sch (lam t₁) h = (∏ k, h k) ^ m := by
    intro h
    have e := (hD R n h).2 (fun _ => 0) m
    simp only [zero_add, (hD R n h).1, mul_one] at e
    have hl : lam t₁ = fun _ => m := funext hm
    rw [hl, e]
  have h10 : t₁ ≠ t₀ := fun h => h01 h.symm
  have h1mem : t₁ ∈ univ.erase t₀ := mem_erase.mpr ⟨h10, mem_univ _⟩
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    apply prod_congr rfl
    intro t ht
    have ht1 : t ≠ t₁ := (mem_erase.mp ht).1
    have ht0 : t ≠ t₀ := (mem_erase.mp (mem_erase.mp ht).2).1
    simp only [twist, if_neg ht0, if_neg ht1]
    rw [hH R n (lam t) (g t) (y ^ ε t), ← pow_mul]
  have hi : ∀ i, ∏ t, sch (lam t) (twist t₀ t₁ ε y i g t) =
      sch (lam t₀) (scaleAt y i (g t₀)) *
        (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) := by
    intro i
    rw [← mul_prod_erase univ _ (mem_univ t₀), ← mul_prod_erase (univ.erase t₀) _ h1mem,
      ← mul_prod_erase (univ.erase t₀) (fun t => sch (lam t) (g t)) h1mem, hrest i]
    simp only [twist, eq_self_iff_true, ↓reduceIte, h10]
    rw [hconst, hconst, prod_scaleOff, mul_pow, ← pow_mul, pow_add]
    ring
  calc ∑ i, (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
        ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i)
      = (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) *
        ∑ i, sch (lam t₀) (scaleAt y i (g t₀)) *
          ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hi i]
        ring
    _ = _ := by
        rw [hY R n (lam t₀) (g t₀) y hu, ← mul_prod_erase univ (fun t => sch (lam t) (g t)) (mem_univ t₀)]
        ring

end UpperTheory.Gal.Schur
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterp
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem interp_of : SpanProd → Expand → Extract → DenseCoset → Interp := by
  intro hS hE hX hC O K ι _ _ _ _ τ hτ n P hP
  classical
  obtain ⟨k₀, hk₀⟩ := hS K ι n P hP
  refine ⟨k₀, fun k hk N hN a Q hQ => ?_⟩
  obtain ⟨w, hw⟩ := hk₀ k hk
  let A := {α : Fin k → O // (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0}
  let x : A → ι × Fin k → K := fun α => pt τ α.1
  have hdense : ZDense (Set.range x) := by
    have hset : Set.range x =
        {z | ∃ α, (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0 ∧ z = pt τ α} := by
      ext z
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨α.1, α.2.1, α.2.2, rfl⟩
      · rintro ⟨α, h1, h2, rfl⟩
        exact ⟨⟨α, h1, h2⟩, rfl⟩
    rw [hset]
    exact hC O K ι τ hτ N hN k a Q hQ
  have he : Function.Injective
      (fun (m : ι × Fin k → Fin (n + 1)) (p : ι × Fin k) => (m p : ℕ)) := by
    intro m₁ m₂ h
    funext p
    exact Fin.ext (congrFun h p)
  obtain ⟨c, hc⟩ := hX K (ι × Fin k) A (ι × Fin k → Fin (n + 1)) x hdense _ he w
  refine ⟨c.mapDomain Subtype.val, ?_, ?_⟩
  · intro α hα
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hα)
    exact β.2
  · intro R _ _ g
    let F : (Fin k → O) → R := fun α => ∏ t, ∏ s, detOne (algebraMap K R (τ t (α s))) (g t)
    have hmd : ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) =
        c.sum fun β (r : K) => r • F β.1 := by
      apply Finsupp.sum_mapDomain_index
      · intro _
        exact zero_smul K _
      · intro _ r₁ r₂
        exact add_smul r₁ r₂ _
    change ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) = _
    rw [hmd]
    have hexp : ∀ β : A, F β.1 =
        ∑ m : ι × Fin k → Fin (n + 1), algebraMap K R (∏ p, x β p ^ (m p : ℕ)) *
          ∏ p : ι × Fin k, (-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p : ℕ)) := by
      intro β
      have h := hE K R (ι × Fin k) n (fun p => algebraMap K R (pt τ β.1 p)) (fun p => g p.1)
      rw [Fintype.prod_prod_type] at h
      simp only [pt] at h
      simp only [F]
      rw [h]
      apply Finset.sum_congr rfl
      intro m _
      simp only [x, pt, map_prod, map_pow]
    simp only [Finsupp.sum, hexp]
    rw [hw R g]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [← hc m, Finsupp.sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro β _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    ring

end UpperTheory.Gal.Schur
end
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkInd :
    ∀ (n : ℕ) (p : Perm (Fin n) → Prop), p 1 →
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c → p w → p (swap a c * w)) → ∀ w, p w := by
  intro n p h1 hstep
  obtain ⟨hA, hB, -, -, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have red : ∀ w : Perm (Fin n), w ≠ 1 → ∃ w', invN w = invN w' + 1 ∧ (p w' → p w) := by
    intro w hw
    obtain ⟨a, c, hac, hlt⟩ := hB w hw
    have hlt' : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
      rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
        swap_apply_right]
      exact hlt
    have hw' : swap a c * (swap a c * w) = w := swap_mul_self_mul a c w
    refine ⟨swap a c * w, ?_, fun hp => ?_⟩
    · have := (hA a c hac _ hlt').2.2
      rwa [hw'] at this
    · have := hstep a c hac _ hlt' hp
      rwa [hw'] at this
  have key : ∀ k, ∀ w : Perm (Fin n), invN w = k → p w := by
    intro k
    induction k with
    | zero =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, -⟩ := red w h
        exfalso
        omega
    | succ k ih =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, hp⟩ := red w h
        exact hp (ih w' (by omega))
  exact fun w => key _ w rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem level_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (n : ℕ) {D : Type} [CommRing D]
    (g : R →+* D) (hu : ∀ s, s ∉ p → IsUnit (g s)) (hz : ∀ a, a ∈ p ^ n → g a = 0) :
    ∃ f : B →+* D, ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * f b = g a := by
  have hP := h.isPrime
  choose A S hS hAS using h.dense n
  have wd : ∀ (b : B) (a s a' s' : R), s ∉ p → s' ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n →
      algebraMap R B s' * b - algebraMap R B a' ∈ maximalIdeal B ^ n → g s * g a' = g s' * g a := by
    intro b a s a' s' _ hs' h1 h2
    have hm : algebraMap R B (s * a' - s' * a) ∈ maximalIdeal B ^ n := by
      have hid : algebraMap R B (s * a' - s' * a) = algebraMap R B s' *
          (algebraMap R B s * b - algebraMap R B a) - algebraMap R B s *
          (algebraMap R B s' * b - algebraMap R B a') := by
        simp only [map_sub, map_mul]
        ring
      rw [hid]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    obtain ⟨t, ht, hta⟩ := h.strict n _ hm
    have h0 := hz _ hta
    rw [map_mul, (hu t ht).mul_right_eq_zero, map_sub, map_mul, map_mul, sub_eq_zero] at h0
    exact h0
  let F : B → D := fun b => ↑(hu _ (hS b)).unit⁻¹ * g (A b)
  have hF0 : ∀ b, g (S b) * F b = g (A b) := by
    intro b
    simp only [F, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have spec : ∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g s * F b = g a := by
    intro b a s hs hb
    apply (hu _ (hS b)).mul_left_cancel
    rw [← mul_assoc, mul_comm (g (S b)), mul_assoc, hF0, wd b (A b) (S b) a s (hS b) hs (hAS b) hb]
  have eq_of : ∀ (b : B) (y : D) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g a = g s * y → F b = y := by
    intro b y a s hs hb hy
    exact (hu s hs).mul_left_cancel ((spec b a s hs hb).trans hy)
  have hprod : ∀ x y : B, S x * S y ∉ p := fun x y hm => (hP.mem_or_mem hm).elim (hS x) (hS y)
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, spec⟩
  · refine eq_of 1 1 1 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x * y) _ (A x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x * y) - algebraMap R B (A x * A y) =
          algebraMap R B (S x) * x * (algebraMap R B (S y) * y - algebraMap R B (A y)) +
          algebraMap R B (A y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) := by
        simp only [map_mul]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS y)) (Ideal.mul_mem_left _ _ (hAS x))
    · show g (A x * A y) = g (S x * S y) * (F x * F y)
      rw [map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring
  · refine eq_of 0 0 0 1 ?_ ?_ (by simp)
    · intro h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · simp
  · intro x y
    refine eq_of (x + y) _ (S y * A x + S x * A y) (S x * S y) (hprod x y) ?_ ?_
    · have hid : algebraMap R B (S x * S y) * (x + y) - algebraMap R B (S y * A x + S x * A y) =
          algebraMap R B (S y) * (algebraMap R B (S x) * x - algebraMap R B (A x)) +
          algebraMap R B (S x) * (algebraMap R B (S y) * y - algebraMap R B (A y)) := by
        simp only [map_mul, map_add (f := _)]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hAS x)) (Ideal.mul_mem_left _ _ (hAS y))
    · show g (S y * A x + S x * A y) = g (S x * S y) * (F x + F y)
      rw [map_add (f := _), map_mul, map_mul, map_mul, ← hF0 x, ← hF0 y]
      ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C] (φ : R →+* C),
      (maximalIdeal C).comap φ = p → ∃! ψ : B →+* C, ψ.comp (algebraMap R B) = φ := by
  intro R _ p B _ _ _ hB C _ _ _ φ hφ
  have hpI : ∀ n, ∀ a ∈ p ^ n, φ a ∈ maximalIdeal C ^ n := by
    intro n a ha
    have hle : Ideal.map φ p ≤ maximalIdeal C := by
      rw [← hφ]
      exact Ideal.map_comap_le
    have hmap : Ideal.map φ (p ^ n) ≤ maximalIdeal C ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hle n
    exact hmap (Ideal.mem_map_of_mem φ ha)
  have hunit : ∀ s, s ∉ p → IsUnit (φ s) := by
    intro s hs
    by_contra hn
    apply hs
    rw [← hφ, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let g : ∀ n, R →+* C ⧸ maximalIdeal C ^ n := fun n => (Ideal.Quotient.mk (maximalIdeal C ^ n)).comp φ
  have hu : ∀ n s, s ∉ p → IsUnit (g n s) := fun n s hs =>
    (hunit s hs).map (Ideal.Quotient.mk (maximalIdeal C ^ n))
  have hz : ∀ n a, a ∈ p ^ n → g n a = 0 := fun n a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hpI n a ha)
  choose f hf using fun n => level_map hB n (g n) (hu n) (hz n)
  have lvl : ∀ n (k : B → C ⧸ maximalIdeal C ^ n), (∀ (b : B) (a s : R), s ∉ p →
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n → g n s * k b = g n a) →
      ∀ b, k b = f n b := by
    intro n k hk b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    exact (hu n s hs).mul_left_cancel ((hk b a s hs hb).trans (hf n b a s hs hb).symm)
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (f n) = f m := by
    intro m n hle
    ext b
    obtain ⟨a, s, hs, hb⟩ := hB.dense n b
    have hbm : algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ m :=
      Ideal.pow_le_pow_right hle hb
    apply (hu m s hs).mul_left_cancel
    show g m s * Ideal.Quotient.factorPow (maximalIdeal C) hle (f n b) = g m s * f m b
    rw [hf m b a s hs hbm]
    have hc := congrArg (Ideal.Quotient.factorPow (maximalIdeal C) hle) (hf n b a s hs hb)
    rw [map_mul] at hc
    have hg : ∀ x, Ideal.Quotient.factorPow (maximalIdeal C) hle (g n x) = g m x := by
      intro x
      simp [g]
    rw [hg, hg] at hc
    exact hc
  have h1p : (1 : R) ∉ p := fun h1 => hB.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hmk : ∀ n b, Ideal.Quotient.mk (maximalIdeal C ^ n)
      (IsAdicComplete.liftRingHom (maximalIdeal C) f compat b) = f n b :=
    fun n b => IsAdicComplete.mk_liftRingHom (maximalIdeal C) f compat n b
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal C) f compat, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' (maximalIdeal C)
    intro n r
    rw [RingHom.comp_apply, hmk]
    apply (hu n 1 h1p).mul_left_cancel
    rw [hf n (algebraMap R B r) r 1 h1p (by simp), map_one, one_mul]
    rfl
  · intro ψ' hψ'
    apply IsAdicComplete.eq_liftRingHom (maximalIdeal C) f compat ψ'
    intro n
    ext b
    rw [RingHom.comp_apply]
    refine lvl n (fun b => Ideal.Quotient.mk (maximalIdeal C ^ n) (ψ' b)) ?_ b
    intro b a s hs hb
    have hmap : Ideal.map ψ' (maximalIdeal B ^ n) ≤ maximalIdeal C ^ n := by
      rw [← IsCplAt.map_pow_eq R p B hB n, Ideal.map_map, hψ', Ideal.map_le_iff_le_comap]
      intro c hc
      exact hpI n c hc
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 (hmap (Ideal.mem_map_of_mem _ hb))
    have e : ∀ x, ψ' (algebraMap R B x) = φ x := fun x => by rw [← RingHom.comp_apply, hψ']
    rw [map_sub, map_mul, e, e, map_sub, map_mul, sub_eq_zero] at h0
    exact h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagNeZero
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.aeval_mulVec_eigen {k ι : Type} [CommRing k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (t : k) (v : ι → k) (hv : M *ᵥ v = t • v) (q : k[X]) :
    (aeval M q) *ᵥ v = q.eval t • v := by
  induction q using Polynomial.induction_on with
  | C c => simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  | add p q hp hq => rw [map_add (f := _), Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n c h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, h,
      eval_mul (q := X), eval_X, smul_smul, mul_comm]

private theorem UpperTheory.V.AlgebraTools.lag_ne_zero_field {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι]
    (a : ι → k) (P : Matrix ι ι k) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hP : P.charpoly = ∏ i, (X - C (a i))) (i : ι) : lag a P i ≠ 0 := by
  intro h0
  have h1 := (eq_lag_iff a P i (fun j hj => hu i j hj.symm) (lag a P i)).1 rfl
  rw [h0, smul_zero] at h1
  have hroot : P.charpoly.eval (a i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hv' : P *ᵥ v = a i • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  have h2 := UpperTheory.V.AlgebraTools.aeval_mulVec_eigen P (a i) v hv' (∏ j ∈ Finset.univ.erase i, (X - C (a j)))
  rw [← h1, Matrix.zero_mulVec, eval_prod] at h2
  rcases smul_eq_zero.1 h2.symm with h | h
  · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.1 h
    have := (hu i j (Finset.ne_of_mem_erase hj).symm).ne_zero
    apply this
    simpa using hj0
  · exact hv0 h

theorem UpperTheory.V.AlgebraTools.lag_ne_zero :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → R) (P : Matrix ι ι R), (∀ i j, i ≠ j → IsUnit (a i - a j)) → P.charpoly.map (residue R) = ∏ i, (X - C (residue R (a i))) → ∀ i, lag a P i ≠ 0 := by
  intro R _ _ ι _ _ a P hu hP i h0
  have h := lag_map (residue R) (residue R).mapMatrix a P
    (fun c => by
      ext x y
      by_cases hxy : x = y <;> simp [Matrix.algebraMap_matrix_apply, hxy]) hu i
  rw [h0, map_zero] at h
  refine UpperTheory.V.AlgebraTools.lag_ne_zero_field (fun j => residue R (a j)) ((residue R).mapMatrix P)
    (fun i j hij => by simpa only [map_sub] using (hu i j hij).map (residue R)) ?_ i h.symm
  rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, hP]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagTriangular
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem left_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ f * x = u • f) :
    ∃ u : R, IsUnit u ∧ f * L.prod = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨u * v, hu.mul hv, by
      rw [List.prod_cons, ← mul_assoc, e, smul_mul_assoc, e', smul_smul]⟩

private theorem right_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ x * f = u • f) :
    ∃ u : R, IsUnit u ∧ L.prod * f = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨v * u, hv.mul hu, by
      rw [List.prod_cons, mul_assoc, e', mul_smul_comm, e, smul_smul]⟩

private theorem mid_zero {R E : Type} [CommRing R] [Ring E] [Algebra R E] {n : ℕ} (f g : E)
    (F : Fin n → E) (i : Fin n)
    (hf : ∀ j, j < i → ∃ u : R, IsUnit u ∧ f * F j = u • f)
    (hg : ∀ j, i < j → ∃ u : R, IsUnit u ∧ F j * g = u • g)
    (h0 : (List.ofFn F).prod = 0) : f * F i * g = 0 := by
  have hlen : (List.ofFn F).length = n := List.length_ofFn
  have hsplit : List.ofFn F = (List.ofFn F).take i ++ F i :: (List.ofFn F).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn F)]
    congr 1
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact i.2)]
    simp
  have hT : ∀ x ∈ (List.ofFn F).take i, ∃ u : R, IsUnit u ∧ f * x = u • f := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, hlen] at hk
    rw [List.getElem_take, List.getElem_ofFn]
    exact hf ⟨k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  have hD : ∀ x ∈ (List.ofFn F).drop (i + 1), ∃ u : R, IsUnit u ∧ x * g = u • g := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_drop, hlen] at hk
    rw [List.getElem_drop, List.getElem_ofFn]
    exact hg ⟨i + 1 + k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  obtain ⟨u, hu, hA⟩ := left_unit (R := R) f _ hT
  obtain ⟨v, hv, hB⟩ := right_unit (R := R) g _ hD
  have key : f * (List.ofFn F).prod * g = (u * v) • (f * F i * g) := by
    rw [hsplit, List.prod_append, List.prod_cons]
    calc f * (((List.ofFn F).take i).prod * (F i * ((List.ofFn F).drop (i + 1)).prod)) * g
        = (f * ((List.ofFn F).take i).prod) * F i * (((List.ofFn F).drop (i + 1)).prod * g) := by
          simp only [mul_assoc]
      _ = (u • f) * F i * (v • g) := by rw [hA, hB]
      _ = (u * v) • (f * F i * g) := by
          rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h0, mul_zero, zero_mul] at key
  exact ((hu.mul hv).smul_eq_zero).1 key.symm

theorem UpperTheory.V.AlgebraTools.lag_triangular :
    ∀ {R Λ E : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Ring E] [Algebra R E] {n : ℕ} (ρ : Λ →ₐ[R] E) (χ : Fin n → Λ →ₐ[R] R) (z : Λ), (∀ y : Fin n → Λ, (List.ofFn fun i => ρ (y i) - algebraMap R E (χ i (y i))).prod = 0) → (∀ i j, i ≠ j → IsUnit (χ i z - χ j z)) → CompleteOrthogonalIdempotents (lag (fun i => χ i z) (ρ z)) ∧ (∀ (y : Λ) (a b : Fin n), b < a → lag (fun i => χ i z) (ρ z) a * ρ y * lag (fun i => χ i z) (ρ z) b = 0) ∧ ∀ (y : Λ) (i : Fin n), lag (fun i => χ i z) (ρ z) i * ρ y * lag (fun i => χ i z) (ρ z) i = χ i y • lag (fun i => χ i z) (ρ z) i := by
  intro R Λ E _ _ _ _ _ n ρ χ z hprod hu
  have hzero : aeval (ρ z) (∏ i, (X - C ((fun i => χ i z) i))) = 0 := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simpa [Function.comp_def] using hprod (fun _ => z)
  obtain ⟨hcoi, hP, -, hcomm⟩ := lag_coi (fun i => χ i z) (ρ z) hu hzero
  have hl : ∀ c j, lag (fun i => χ i z) (ρ z) c * (ρ z - algebraMap R E (χ j z)) =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [mul_sub, ← (hcomm (ρ z) c (Commute.refl _)).eq, hP, ← Algebra.commutes,
      ← Algebra.smul_def, sub_smul]
  have hr : ∀ c j, (ρ z - algebraMap R E (χ j z)) * lag (fun i => χ i z) (ρ z) c =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [sub_mul, hP, ← Algebra.smul_def, sub_smul]
  have key : ∀ (y : Λ) (c d i : Fin n), (∀ j, j < i → j ≠ c) → (∀ j, i < j → j ≠ d) →
      lag (fun i => χ i z) (ρ z) c * (ρ y - algebraMap R E (χ i y)) *
        lag (fun i => χ i z) (ρ z) d = 0 := by
    intro y c d i h1 h2
    have h := mid_zero (R := R) (lag (fun i => χ i z) (ρ z) c) (lag (fun i => χ i z) (ρ z) d)
      (fun j => ρ (Function.update (fun _ => z) i y j) -
        algebraMap R E (χ j (Function.update (fun _ => z) i y j))) i ?_ ?_ (hprod _)
    · simpa using h
    · intro j hj
      refine ⟨_, hu c j (h1 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_lt hj)]
      exact hl c j
    · intro j hj
      refine ⟨_, hu d j (h2 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_gt hj)]
      exact hr d j
  have hmid : ∀ (r : R) (c d : Fin n), lag (fun i => χ i z) (ρ z) c * algebraMap R E r *
      lag (fun i => χ i z) (ρ z) d =
        r • (lag (fun i => χ i z) (ρ z) c * lag (fun i => χ i z) (ρ z) d) := by
    intro r c d
    rw [← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc]
  refine ⟨hcoi, ?_, ?_⟩
  · intro y a b hba
    have h := key y a b a (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt (hba.trans hj))
    rw [mul_sub, sub_mul, hmid, hcoi.ortho (ne_of_gt hba), smul_zero, sub_zero] at h
    exact h
  · intro y i
    have h := key y i i i (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt hj)
    rw [mul_sub, sub_mul, hmid, (hcoi.idem i).eq, sub_eq_zero] at h
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Imports
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_diag :
    ∀ (F : Filter ℕ), F ≤ atTop → ∀ P : ℕ → ℕ → Prop, (∀ j, ∀ᶠ N in F, P j N) →
      ∃ ν : ℕ → ℕ, Tendsto ν F atTop ∧ ∀ᶠ N in F, ∀ j ≤ ν N, P j N := by
  classical
  intro F hF P hP
  have hall : ∀ j, ∀ᶠ N in F, ∀ i ≤ j, P i N := fun j =>
    (Filter.eventually_all_finite (Set.finite_Iic j)).2 (fun i _ => hP i)
  refine ⟨fun N => Nat.findGreatest (fun j => ∀ i ≤ j, P i N) N, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro j
    filter_upwards [hall j, hF (eventually_ge_atTop j)] with N h1 h2
    exact Nat.le_findGreatest (P := fun j => ∀ i ≤ j, P i N) h2 h1
  · filter_upwards [hall 0] with N h1
    exact Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, P i N) (Nat.zero_le N) h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualExp
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem dual_symm {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) : IsDual b a := by
  intro w
  have h2 := congrArg (rename ⇑w) (h w⁻¹)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rename_rename] at h2
  have hc : (⇑w ∘ ⇑w⁻¹ : Fin n → Fin n) = id := by
    funext k
    simp
  simp only [hc, rename_id, AlgHom.id_apply] at h2
  simp_rw [mul_comm (b _)]
  rw [h2]
  by_cases hw : w = 1
  · subst hw
    simp
  · have hw' : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
    simp [hw, hw']

private theorem dual_exp {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) (x : MvPolynomial (Fin n) R) :
    ∑ i, a i * dd (b i * x) = x := by
  obtain ⟨hD, -, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  apply mul_left_cancel₀ hD
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (De R n), UpperTheory.V.AlgebraTools.hkDdSpec, alt, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  have key : ∀ y : Perm (Fin n), ∑ i, a i * Perm.sign y • ((rename ⇑y) (b i) * (rename ⇑y) x) =
      Perm.sign y • ((if y = 1 then De R n else 0) * (rename ⇑y) x) := by
    intro y
    rw [← h y, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, mul_assoc]
  rw [Finset.sum_congr rfl fun y _ => key y]
  simp

theorem UpperTheory.V.AlgebraTools.hkDualExp :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) R), IsDual a b →
      ∀ x, ∑ i, a i * dd (b i * x) = x ∧ ∑ i, b i * dd (a i * x) = x := by
  intro R _ _ n ι _ a b h x
  exact ⟨dual_exp h x, dual_exp (dual_symm h) x⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.KerMapPowerSeriesQuotient
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem ker_map_power_series_quotient (R : Type) [CommRing R] (a : Ideal R) (ha : a.FG) :
    RingHom.ker (PowerSeries.map (Ideal.Quotient.mk a)) = a.map (PowerSeries.C : R →+* PowerSeries R) := by
  classical
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨s, rfl⟩ := ha
    have hc : ∀ n, PowerSeries.coeff n f ∈ Ideal.span (s : Set R) := by
      intro n
      have := congrArg (PowerSeries.coeff n) hf
      rw [PowerSeries.coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have hc' : ∀ n, ∃ c : R → R, ∑ x ∈ s, c x * x = PowerSeries.coeff n f := by
      intro n
      obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 (hc n)
      exact ⟨c, by simpa [smul_eq_mul] using hc⟩
    choose c hc' using hc'
    have : f = ∑ x ∈ s, PowerSeries.mk (fun n => c n x) * PowerSeries.C x := by
      ext n
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hc' n]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mk]
    rw [this]
    refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

theorem UpperTheory.V.AlgebraTools.powerSeries_ker_map :
    ∀ (R : Type) [CommRing R] (a : Ideal R), a.FG →
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk a)) = a.map (PowerSeries.C : R →+* PowerSeries R) ∧
      Function.Surjective (PowerSeries.map (Ideal.Quotient.mk a)) ∧
      (a.IsPrime → (a.map (PowerSeries.C : R →+* PowerSeries R)).IsPrime) ∧
      (a.map (PowerSeries.C : R →+* PowerSeries R)).comap (PowerSeries.C : R →+* PowerSeries R) = a := by
  intro R _ a ha
  have hk := ker_map_power_series_quotient R a ha
  refine ⟨hk, ?_, ?_, ?_⟩
  · intro g
    choose c hc using fun n => Ideal.Quotient.mk_surjective (I := a) (PowerSeries.coeff n g)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hc]
  · intro hp
    rw [← hk]
    exact RingHom.ker_isPrime _
  · rw [← hk]
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      exact PowerSeries.C_injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegScal
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem mem_map_smul_top_iff {S R M : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M] (K : Ideal S) (m : M) :
    m ∈ (K.map (algebraMap S R) • ⊤ : Submodule R M) ↔ m ∈ (K • ⊤ : Submodule S M) := by
  have h := Submodule.restrictScalars_map_smul_eq K (⊤ : Submodule R M)
  rw [Submodule.restrictScalars_top] at h
  rw [← h, Submodule.restrictScalars_mem]

private theorem map_mem_smul_top {S M M' : Type} [CommRing S] [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') (K : Ideal S) {m : M}
    (h : m ∈ (K • ⊤ : Submodule S M)) : f m ∈ (K • ⊤ : Submodule S M') := by
  have h2 : f m ∈ (K • ⊤ : Submodule S M).map f := Submodule.mem_map_of_mem h
  rw [Submodule.map_smul''] at h2
  exact Submodule.smul_mono (le_refl K) le_top h2

private theorem mem_of_smul_mem {S M M' : Type} [CommRing S] (T : Submonoid S) [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f] (K : Ideal S) (t : T) {x : M'}
    (h : (t : S) • x ∈ (K • ⊤ : Submodule S M')) : x ∈ (K • ⊤ : Submodule S M') := by
  have hu := IsLocalizedModule.map_units f t
  have e := LinearMap.congr_fun hu.unit.inv_mul x
  rw [Module.End.mul_apply, IsUnit.unit_spec, Module.End.one_apply, Module.algebraMap_end_apply] at e
  rw [← e]
  exact map_mem_smul_top _ K h

private theorem exists_smul_mem {S M M' : Type} [CommRing S] (T : Submonoid S) [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f] (K : Ideal S) {m : M}
    (h : f m ∈ (K • ⊤ : Submodule S M')) : ∃ t : T, (t : S) • m ∈ (K • ⊤ : Submodule S M) := by
  have key : ∀ x ∈ (K • ⊤ : Submodule S M'), ∃ (s : T) (m' : M),
      m' ∈ (K • ⊤ : Submodule S M) ∧ (s : S) • x = f m' := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro k hk x _
      obtain ⟨⟨m0, s⟩, hs⟩ := IsLocalizedModule.surj T f x
      simp only at hs
      refine ⟨s, k • m0, Submodule.smul_mem_smul hk Submodule.mem_top, ?_⟩
      rw [map_smul, ← hs, Submonoid.smul_def, smul_comm]
    · intro x y hx hy
      obtain ⟨s1, m1, hm1, h1⟩ := hx
      obtain ⟨s2, m2, hm2, h2⟩ := hy
      refine ⟨s1 * s2, (s2 : S) • m1 + (s1 : S) • m2,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hm1) (Submodule.smul_mem _ _ hm2), ?_⟩
      rw [map_add (f := _), map_smul, map_smul, ← h1, ← h2, smul_add, Submonoid.coe_mul, mul_smul, mul_smul,
        smul_comm (s1 : S) (s2 : S) x]
  obtain ⟨s, m', hm', he⟩ := key _ h
  rw [← map_smul] at he
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) he
  refine ⟨c * s, ?_⟩
  simp only [Submonoid.smul_def] at hc
  rw [Submonoid.coe_mul, mul_smul, hc]
  exact Submodule.smul_mem _ _ hm'

theorem UpperTheory.V.AlgebraTools.qRegAt_map :
    ∀ (S R σ : Type) [CommRing S] [CommRing R] [Algebra S R] [Finite σ] (y : σ → S) (J : Ideal S) (a : ℕ),
      (∀ (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M],
        QRegAt M y J a ↔ QRegAt M (fun s => algebraMap S R (y s)) (J.map (algebraMap S R)) a) ∧
      (∀ (T : Submonoid S) (M : Type) [AddCommGroup M] [Module S M] (M' : Type) [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f], QRegAt M y J a → QRegAt M' y J a) := by
  intro S R σ _ _ _ _ y J a
  constructor
  · intro M _ _ _ _
    have hv : ∀ α, GlobalTheory.monoVal (fun s => algebraMap S R (y s)) α = algebraMap S R (GlobalTheory.monoVal y α) :=
      fun α => (GlobalTheory.map_monoVal _ _ _).symm
    have e1 : Ideal.span (Set.range fun s => algebraMap S R (y s)) =
        (Ideal.span (Set.range y)).map (algebraMap S R) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    unfold QRegAt
    simp only [hv, algebraMap_smul, e1, ← Ideal.map_pow, ← Ideal.map_sup, mem_map_smul_top_iff]
  · intro T M _ _ M' _ _ f _ hM
    unfold QRegAt at hM ⊢
    intro c' hc' α
    obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite T f c'
    have hs' : ∀ i, ∃ m, f m = (s : S) • c' i := fun i => LinearMap.mem_range.1 (hs i)
    choose c hc using hs'
    have h1 : f (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • c β) ∈
        ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule S M') := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hc]
      have e : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • ((s : S) • c' β)) =
          (s : S) • ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • c' β := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun β _ => smul_comm _ _ _
      rw [e]
      exact Submodule.smul_mem _ _ hc'
    obtain ⟨t, ht⟩ := exists_smul_mem T f _ h1
    rw [Finset.smul_sum] at ht
    have h2 := hM (fun β => (t : S) • c β) (by
      rw [show (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • ((t : S) • c β)) =
          ∑ β : GlobalTheory.MonoDeg σ a, (t : S) • (GlobalTheory.monoVal y (β : σ →₀ ℕ) • c β) from
        Finset.sum_congr rfl fun β _ => smul_comm _ _ _]
      exact ht)
    have h3 := map_mem_smul_top f _ (h2 α)
    rw [map_smul, hc, smul_smul] at h3
    exact mem_of_smul_mem T f _ (t * s) (by rwa [Submonoid.coe_mul])
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilMapMem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnFree
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnIdem
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  have : Module.Finite R S := by
    have : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  have : IsMulCommutative S := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hT i j)
  let _ : CommRing S := by
    open scoped IsMulCommutative in
    exact inferInstance
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
end

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.topNil_free :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      (∃ C : Submodule R M, IsCompl (topNil (IsLocalRing.maximalIdeal R) T) C ∧ ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
        (∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T) ∧ ∀ x ∈ C, φ x ∈ C) ∧
      (∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (∀ i, ∃ r : ℕ, ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, (T i ^ r) x ∈ (IsLocalRing.maximalIdeal R) • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (Module.Free R M → Module.Free R (topNil (IsLocalRing.maximalIdeal R) T) ∧ Module.finrank R (topNil (IsLocalRing.maximalIdeal R) T) ≤ Module.finrank R M) := by
  intro R _ _ _ _ κ M _ _ _ T hT
  obtain ⟨e, he, hid, hr⟩ := UpperTheory.V.AlgebraTools.exists_idem_topNil R κ M T hT
  have hee : ∀ x, e (e x) = e x := fun x => by
    have h := congrArg (fun f : Module.End R M => f x) hid.eq
    simpa using h
  have hfix : ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, e x = x := by
    rw [← hr]
    rintro _ ⟨y, rfl⟩
    exact hee y
  have hmem : ∀ x, e x ∈ topNil (IsLocalRing.maximalIdeal R) T := fun x => by
    rw [← hr]; exact ⟨x, rfl⟩
  have hcomm : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x, φ (e x) = e (φ x) := by
    intro φ hφ x
    have h : Commute φ e := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute he ?_
      rintro _ ⟨i, rfl⟩
      exact hφ i
    have h2 := congrArg (fun f : Module.End R M => f x) h.eq
    simpa using h2
  have hstab : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
      ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T := by
    intro φ hφ x hx
    rw [← hfix x hx, hcomm φ hφ]
    exact hmem _
  have hI : ∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T =
      I • topNil (IsLocalRing.maximalIdeal R) T := by
    intro I
    refine le_antisymm ?_ (le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right)
    rintro x ⟨hx1, hx2⟩
    have h1 : e x ∈ Submodule.map e (I • ⊤ : Submodule R M) := ⟨x, hx1, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, hr, hfix x hx2] at h1
    exact h1
  refine ⟨⟨LinearMap.ker e, ?_, fun φ hφ => ⟨hstab φ hφ, ?_⟩⟩, hI, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hk
      rw [← hfix x hx]
      exact hk
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.2 ⟨e x, hmem x, x - e x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hee, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hcomm φ hφ, hx, map_zero]
  · intro i
    obtain ⟨S, hS⟩ := IsNoetherian.noetherian (topNil (IsLocalRing.maximalIdeal R) T)
    have hev : ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
        (T i ^ r) x ∈ ((IsLocalRing.maximalIdeal R) ^ 1 • ⊤ : Submodule R M) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hx' : x ∈ topNil (IsLocalRing.maximalIdeal R) T := hS ▸ Submodule.subset_span hx
      exact mem_topNil.1 hx' i 1
    obtain ⟨r, hr'⟩ := hev.exists
    refine ⟨r, fun x hx => ?_⟩
    rw [← hI]
    refine ⟨?_, hstab _ (fun j => (hT i j).pow_left r) x hx⟩
    have hle : Submodule.span R (S : Set M) ≤
        Submodule.comap (T i ^ r) ((IsLocalRing.maximalIdeal R) • ⊤ : Submodule R M) := by
      rw [Submodule.span_le]
      intro y hy
      have h := hr' y hy
      rw [pow_one] at h
      exact h
    rw [hS] at hle
    exact hle hx
  · intro hF
    refine ⟨?_, Submodule.finrank_le _⟩
    have hP : Module.Projective R (topNil (IsLocalRing.maximalIdeal R) T) :=
      Module.Projective.of_split (topNil (IsLocalRing.maximalIdeal R) T).subtype
        (LinearMap.codRestrict _ e hmem) (by
          ext x
          simpa using hfix x.1 x.2)
    exact Module.free_of_flat_of_isLocalRing
end

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem topNil_map_mem {R M M' κ : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (T : κ → Module.End R M)
    (T' : κ → Module.End R M') (f : M →ₗ[R] M') (hf : ∀ i x, f (T i x) = T' i (f x))
    {x : M} (hx : x ∈ topNil I T) : f x ∈ topNil I T' := by
  change ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) x ∈ (I ^ j • ⊤ : Submodule R M) at hx
  change ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T' i ^ r) (f x) ∈ (I ^ j • ⊤ : Submodule R M')
  intro i j
  have hpow : ∀ r : ℕ, f ((T i ^ r) x) = (T' i ^ r) (f x) := by
    intro r
    induction r with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]
  have hle : Submodule.map f (I ^ j • (⊤ : Submodule R M)) ≤ I ^ j • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  filter_upwards [hx i j] with r hr
  rw [← hpow]
  exact hle ⟨_, hr, rfl⟩

theorem UpperTheory.V.AlgebraTools.topNil_map :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] (M' : Type) [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] (T : κ → Module.End R M) (T' : κ → Module.End R M'),
      (∀ i j, Commute (T i) (T j)) → (∀ i j, Commute (T' i) (T' j)) → ∀ f : M →ₗ[R] M', (∀ i x, f (T i x) = T' i (f x)) →
      (topNil (IsLocalRing.maximalIdeal R) T).map f = topNil (IsLocalRing.maximalIdeal R) T' ⊓ LinearMap.range f ∧
      ∀ I : Ideal R, LinearMap.ker f = I • ⊤ → LinearMap.ker f ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ M' _ _ _ _ T T' hT hT' f hf
  have hsmul := (topNil_free R κ M T hT).2.1
  refine ⟨le_antisymm ?_ ?_, fun I hI => by rw [hI]; exact hsmul I⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact ⟨topNil_map_mem _ T T' f hf hx, x, rfl⟩
  · rintro y ⟨hy, x, rfl⟩
    have hTx : ∀ i j x, T i (T j x) = T j (T i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply]
    have hT'x : ∀ i j x, T' i (T' j x) = T' j (T' i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT' i j).eq, Module.End.mul_apply]
    let S : κ → Module.End R (M × M') := fun i => (T i).prodMap (T' i)
    have hS : ∀ i j, Commute (S i) (S j) := by
      intro i j
      show S i * S j = S j * S i
      apply LinearMap.ext
      intro p
      simp [S, Module.End.mul_apply, hTx i j, hT'x i j]
    obtain ⟨⟨C, hC, hstab⟩, -⟩ := topNil_free R κ (M × M') S hS
    let φ : Module.End R (M × M') := (LinearMap.inr R M M').comp (f.comp (LinearMap.fst R M M'))
    have hφ : ∀ i, Commute φ (S i) := by
      intro i
      show φ * S i = S i * φ
      apply LinearMap.ext
      intro p
      simp [φ, S, Module.End.mul_apply, hf]
    have hmem : ((x, 0) : M × M') ∈ topNil (IsLocalRing.maximalIdeal R) S ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp hmem
    have hn1 : n.1 ∈ topNil (IsLocalRing.maximalIdeal R) T :=
      topNil_map_mem _ S T (LinearMap.fst R M M') (fun i p => rfl) hn
    have hφc : φ c ∈ C := (hstab φ hφ).2 c hc
    have hx : x = n.1 + c.1 := by
      have := congrArg Prod.fst hnc
      simpa using this.symm
    have hfc : f c.1 ∈ topNil (IsLocalRing.maximalIdeal R) T' := by
      have : f c.1 = f x - f n.1 := by
        rw [hx]
        simp
      rw [this]
      exact Submodule.sub_mem _ hy (topNil_map_mem _ T T' f hf hn1)
    have hφn : φ c ∈ topNil (IsLocalRing.maximalIdeal R) S := by
      have := topNil_map_mem _ T' S (LinearMap.inr R M M') (fun i y => by simp [S]) hfc
      simpa [φ] using this
    have h0 : φ c = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hφn hφc
    have hfc0 : f c.1 = 0 := by
      have := congrArg Prod.snd h0
      simpa [φ] using this
    refine ⟨n.1, hn1, ?_⟩
    rw [hx, map_add (f := _), hfc0, add_zero]
end

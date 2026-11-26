module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenVan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DivPowInteg
open MvPolynomial

namespace PI

namespace DivPowInteg

noncomputable def delta {K I J : Type} [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) :
    MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

end DivPowInteg

def DivPowInteg : Prop :=
  ∀ (A K I J : Type) [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
    [Fintype I] [Fintype J] (L : Submodule A K) (κ : I → J → K),
    (∀ i j, κ i j ∈ L) →
    ∀ (P : MvPolynomial (I ⊕ J) A) (n : ℕ),
      (∀ m, (((n.factorial : ℚ)⁻¹ •
          (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P)).coeff m) ∈ L ^ n) ∧
      (((∀ m ∈ P.support, ∑ i, m (Sum.inl i) < n) ∨ (∀ m ∈ P.support, ∑ j, m (Sum.inr j) < n)) →
        (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P) = 0)

end PI
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.DivPowInteg
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenPow
open MvPolynomial

namespace PI.DivPowInteg.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem pderiv_comm (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have hc : ∀ (c d : I ⊕ J) (n : I ⊕ J),
      pderiv c (Pi.single (M := fun _ => MvPolynomial (I ⊕ J) K) d 1 n) = 0 := by
    intro c d n
    rw [Pi.single_apply]
    split_ifs <;> simp
  induction p using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), hc, hp, mul_zero, zero_add]
    ring

noncomputable abbrev pd (a : I ⊕ J) : Module.End K (MvPolynomial (I ⊕ J) K) :=
  (pderiv a).toLinearMap

private theorem gdelta_apply' (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta]

theorem commute_gdelta_pd (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by
  refine LinearMap.ext fun R => ?_
  show gdelta κ (pderiv c R) = pderiv c (gdelta κ R)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gdelta_apply', map_sum, map_smul, Derivation.map_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_comm c (Sum.inl i), pderiv_comm c (Sum.inr j)]

private theorem dL_apply' (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  simp [dL]

private theorem dR_apply' (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  simp [dR]

private theorem gdelta_pderiv_comm (κ : I → J → K) (c : I ⊕ J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (pderiv c S) = pderiv c (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_pd κ c).eq S

theorem commute_gdelta_dL (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dL κ i S) = dL κ i (gdelta κ S)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dL_apply', dL_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]

theorem commute_gdelta_dR (κ : I → J → K) (j : J) : Commute (gdelta κ) (dR κ j) := by
  refine LinearMap.ext fun S => ?_
  show gdelta κ (dR κ j S) = dR κ j (gdelta κ S)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dR_apply', dR_apply', map_sum]
  simp only [map_smul, gdelta_pderiv_comm]

theorem gdelta_dL_apply (κ : I → J → K) (i : I) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dL κ i S) = dL κ i (gdelta κ S) := LinearMap.congr_fun (commute_gdelta_dL κ i).eq S

theorem gdelta_dR_apply (κ : I → J → K) (j : J) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dR κ j S) = dR κ j (gdelta κ S) := LinearMap.congr_fun (commute_gdelta_dR κ j).eq S

theorem gdelta_pow_succ_apply (κ : I → J → K) (m : ℕ) (S : MvPolynomial (I ⊕ J) K) :
    (gdelta κ ^ (m + 1)) S = gdelta κ ((gdelta κ ^ m) S) := by
  rw [pow_succ']
  rfl

theorem dL_apply (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  exact dL_apply' κ i R

theorem dR_apply (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    dR κ j R = ∑ i, κ i j • pderiv (Sum.inl i) R := by
  exact dR_apply' κ j R

theorem gdelta_X_inl (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ j, pderiv (Sum.inr j) (X (Sum.inl i) * R) = X (Sum.inl i) * pderiv (Sum.inr j) R := by
    intro j
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inl_ne_inr, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inl i') (X (Sum.inl i) * S) =
      X (Sum.inl i) * pderiv (Sum.inl i') S + if i' = i then S else 0 := by
    intro i' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : i' = i
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inl_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have hΔ : ∀ S : MvPolynomial (I ⊕ J) K,
      gdelta κ S = ∑ j, ∑ i', κ i' j • pderiv (Sum.inl i') (pderiv (Sum.inr j) S) := by
    intro S
    rw [gdelta_apply, Finset.sum_comm]
  rw [hΔ, hΔ, dL_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, Finset.mul_sum]
  simp only [h2, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem gdelta_X_inr (κ : I → J → K) (j : J) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inr j) * R) = X (Sum.inr j) * gdelta κ R + dR κ j R := by
  classical
  have h1 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K),
      pderiv (Sum.inl i') (X (Sum.inr j) * S) = X (Sum.inr j) * pderiv (Sum.inl i') S := by
    intro i' S
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inr_ne_inl, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (j' : J) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inr j') (X (Sum.inr j) * S) =
      X (Sum.inr j) * pderiv (Sum.inr j') S + if j' = j then S else 0 := by
    intro j' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : j' = j
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inr_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have h3 : ∀ (i' : I) (j' : J), pderiv (Sum.inl i') (pderiv (Sum.inr j') (X (Sum.inr j) * R)) =
      X (Sum.inr j) * pderiv (Sum.inl i') (pderiv (Sum.inr j') R) +
        if j' = j then pderiv (Sum.inl i') R else 0 := by
    intro i' j'
    rw [h2, map_add (f := _), h1]
    split_ifs <;> simp
  rw [gdelta_apply, gdelta_apply, dR_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.mul_sum]
  simp only [h3, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

theorem powXL_holds : PowXL := by
  unfold PowXL
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add (f := _), map_nsmul, gdelta_X_inl, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']

theorem powXR_holds : PowXR := by
  unfold PowXR
  intro K I J _ _ _ κ j R n
  induction n with
  | zero => simp [gdelta_X_inr]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add (f := _), map_nsmul, gdelta_X_inr, gdelta_dR_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']

section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]

end

end PI.DivPowInteg.Gen
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.NatMulFactorialBound
open MvPolynomial

namespace PI.DivPowInteg.Top

open PI.DivPowInteg.Gen

section

variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]

noncomputable def dpow (κ : I → J → K) (n : ℕ) (R : MvPolynomial (I ⊕ J) K) :
    MvPolynomial (I ⊕ J) K :=
  ((n.factorial : ℚ)⁻¹) • (gdelta κ ^ n) R

theorem dpow_zero (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) : dpow κ 0 R = R := by
  simp [dpow]

theorem dpow_add (κ : I → J → K) (n : ℕ) (p q : MvPolynomial (I ⊕ J) K) :
    dpow κ n (p + q) = dpow κ n p + dpow κ n q := by
  simp [dpow, map_add (f := _), smul_add]

theorem gdelta_C (κ : I → J → K) (c : K) : gdelta κ (C c) = 0 := by
  simp [gdelta]

theorem dpow_C_succ (κ : I → J → K) (k : ℕ) (c : K) : dpow κ (k + 1) (C c) = 0 := by
  rw [dpow, pow_succ, Module.End.mul_apply, gdelta_C, map_zero, smul_zero]

theorem nat_mul_factorial_bound (k : ℕ) :
    ((k + 1).factorial : ℚ)⁻¹ * ((k + 1 : ℕ) : ℚ) = (k.factorial : ℚ)⁻¹ := by
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem dpow_X_mul (κ : I → J → K) (s : I ⊕ J)
    (D : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K) (R : MvPolynomial (I ⊕ J) K)
    (k : ℕ)
    (h : (gdelta κ ^ (k + 1)) (X s * R) =
      X s * (gdelta κ ^ (k + 1)) R + (k + 1) • D ((gdelta κ ^ k) R)) :
    dpow κ (k + 1) (X s * R) = X s * dpow κ (k + 1) R + D (dpow κ k R) := by
  unfold dpow
  rw [h, smul_add, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, nat_mul_factorial_bound,
    LinearMap.map_smul_of_tower]

def Good (L : Submodule A K) (n : ℕ) (Q : MvPolynomial (I ⊕ J) K) : Prop :=
  ∀ m, Q.coeff m ∈ L ^ n

theorem good_X_mul (L : Submodule A K) (n : ℕ) (s : I ⊕ J) (Q : MvPolynomial (I ⊕ J) K)
    (hQ : Good L n Q) : Good L n (X s * Q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact hQ _
  · exact Submodule.zero_mem _

theorem good_smul_pderiv (L : Submodule A K) (k : ℕ) (c : K) (hc : c ∈ L) (s : I ⊕ J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) (m : (I ⊕ J) →₀ ℕ) :
    c * (AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) * ((m s : K) + 1)) ∈ L ^ (k + 1) := by
  have hy : AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) * ((m s : K) + 1) ∈ L ^ k := by
    have e : AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) * ((m s : K) + 1) =
        (m s + 1) • AddMonoidAlgebra.coeff Q (m + Finsupp.single s 1) := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    exact nsmul_mem (hQ _) _
  rw [pow_succ']
  exact Submodule.mul_mem_mul hc hy

theorem good_dL (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (i : I)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dL κ i Q) := by
  intro m
  have e : (dL κ i Q).coeff m = ∑ j, κ i j * AddMonoidAlgebra.coeff (pderiv (Sum.inr j) Q) m := by
    simp [dL, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m

theorem good_dR (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (j : J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dR κ j Q) := by
  intro m
  have e : (dR κ j Q).coeff m = ∑ i, κ i j * AddMonoidAlgebra.coeff (pderiv (Sum.inl i) Q) m := by
    simp [dR, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m

theorem integ (h1 : PowXL) (h2 : PowXR) (L : Submodule A K) (κ : I → J → K)
    (hκ : ∀ i j, κ i j ∈ L) (P : MvPolynomial (I ⊕ J) A) :
    ∀ n, Good L n (dpow κ n (map (algebraMap A K) P)) := by
  classical
  have h0 : ∀ P : MvPolynomial (I ⊕ J) A, Good L 0 (map (algebraMap A K) P) := by
    intro P m
    rw [MvPolynomial.coeff_map, pow_zero]
    exact Submodule.algebraMap_mem _
  refine MvPolynomial.induction_on
    (motive := fun P => ∀ n, Good L n (dpow κ n (map (algebraMap A K) P))) P ?_ ?_ ?_
  · intro a n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (C a)
    | succ k =>
      rw [MvPolynomial.map_C, dpow_C_succ]
      intro m
      rw [MvPolynomial.coeff_zero]
      exact Submodule.zero_mem _
  · intro p q hp hq n m
    rw [map_add (f := _), dpow_add, MvPolynomial.coeff_add]
    exact Submodule.add_mem _ (hp n m) (hq n m)
  · intro p s hp n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (p * X s)
    | succ k =>
      rw [map_mul, MvPolynomial.map_X, mul_comm]
      cases s with
      | inl i =>
        rw [dpow_X_mul κ (Sum.inl i) (dL κ i) (map (algebraMap A K) p) k
          (h1 K I J κ i (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dL L κ hκ k i _ (hp k) m)
      | inr j =>
        rw [dpow_X_mul κ (Sum.inr j) (dR κ j) (map (algebraMap A K) p) k
          (h2 K I J κ j (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dR L κ hκ k j _ (hp k) m)

end

theorem divPowInteg_of (h1 : PowXL) (h2 : PowXR) (h3 : VanL) (h4 : VanR) : PI.DivPowInteg := by
  intro A K I J _ _ _ _ _ _ L κ hκ P n
  have hd : PI.DivPowInteg.delta κ = gdelta κ := rfl
  rw [hd]
  refine ⟨fun m => integ h1 h2 L κ hκ P n m, fun hv => ?_⟩
  rcases hv with hv | hv
  · exact h3 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)
  · exact h4 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)

end PI.DivPowInteg.Top
end

theorem divided_power_integrality : PI.DivPowInteg :=
  PI.DivPowInteg.Top.divPowInteg_of PI.DivPowInteg.Gen.powXL_holds PI.DivPowInteg.Gen.powXR_holds
    PI.DivPowInteg.Gen.vanL_holds PI.DivPowInteg.Gen.vanR_holds
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXEqRename
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem expS_zero' {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem cc_expS {n : ℕ} (F : PS k n d) (hF : constantCoeff F = 0) : constantCoeff (FB.expS k F) = 1 := by
  have ha : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  have h2 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by simp
  unfold FB.expS
  rw [h1, ← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, map_add (f := _), PowerSeries.coe_substAlgHom ha,
    PowerSeries.constantCoeff_subst_eq_zero hF _ h2, map_one, add_zero]

def embX (d : ℕ) : Fin 1 × Fin d ↪ Fin d ⊕ Fin d :=
  ⟨fun p => Sum.inl p.2, fun p q hpq => by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only [Sum.inl.injEq] at hpq
    rw [Subsingleton.elim a b, hpq]⟩

theorem liftX_eq_rename (f : PS k 1 d) : liftX k f = rename (embX d) f := by
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem cc_liftX (f : PS k 1 d) : constantCoeff (liftX k f) = constantCoeff f := by
  rw [liftX_eq_rename, MvPowerSeries.constantCoeff_rename]

theorem intAA_liftX (f : PS k 1 d) (hf : IntAA (R := R) k f) : IntAA (R := R) k (liftX k f) := by
  rw [liftX_eq_rename]
  intro n
  rw [MvPowerSeries.coeff_rename]
  exact Subring.sum_mem _ fun u _ => hf u

def GoodE (R : Type) [CommRing R] [Algebra R k] (E0 X : AA k d) : Prop :=
  ∃ G : AA k d, IntAA (R := R) k G ∧ X = E0 * G

theorem good_pow (E0 : AA k d) (T : Module.End k (AA k d)) (hT : ∀ X, GoodE R E0 X → GoodE R E0 (T X))
    (n : ℕ) : ∀ X, GoodE R E0 X → GoodE R E0 ((T ^ n) X) := by
  induction n with
  | zero =>
    intro X hX
    rw [pow_zero]
    exact hX
  | succ n ih =>
    intro X hX
    rw [pow_succ]
    exact ih (T X) (hT X hX)

theorem good_prod (E0 : AA k d) (L : List (Module.End k (AA k d)))
    (hL : ∀ T ∈ L, ∀ X, GoodE R E0 X → GoodE R E0 (T X)) : ∀ X, GoodE R E0 X → GoodE R E0 (L.prod X) := by
  induction L with
  | nil =>
    intro X hX
    rw [List.prod_nil]
    exact hX
  | cons T L ih =>
    intro X hX
    rw [List.prod_cons]
    exact hL T (by simp) _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) X hX)

theorem good_ofFn (E0 : AA k d) {r : ℕ} (a : Fin r → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (e : Fin r → ℕ) :
    ∀ X, GoodE R E0 X → GoodE R E0 ((List.ofFn fun i => a i ^ e i).prod X) := by
  refine good_prod E0 _ ?_
  intro T hT
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact good_pow E0 (a i) (ha i) (e i)

theorem cc_ordEval_mem (J : Submodule R k) (e : ℕ) (E0 : AA k d) (hE0 : constantCoeff E0 = 1) {r q : ℕ}
    (a : Fin r → Module.End k (AA k d)) (a' : Fin q → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (ha' : ∀ j X, GoodE R E0 X → GoodE R E0 (a' j X))
    (σ : AA k d) (hσ : GoodE R E0 σ) (Q : MvPolynomial (Fin r ⊕ Fin q) k) (hQ : ∀ mo, Q.coeff mo ∈ J ^ e) :
    constantCoeff (PI.WickFormula.ordEval a a' Q σ) ∈ J ^ e := by
  unfold PI.WickFormula.ordEval
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun mo _ => ?_
  have hgood : GoodE R E0 (((List.ofFn fun i => a i ^ mo (Sum.inl i)).prod *
      (List.ofFn fun j => a' j ^ mo (Sum.inr j)).prod) σ) :=
    good_ofFn E0 a ha _ _ (good_ofFn E0 a' ha' _ σ hσ)
  obtain ⟨G, hGi, hGe⟩ := hgood
  rw [LinearMap.smul_apply, hGe, MvPowerSeries.smul_eq_C_mul, map_mul, map_mul,
    MvPowerSeries.constantCoeff_C, hE0, one_mul]
  obtain ⟨r, hr⟩ := hGi 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hr, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hQ mo)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem cc_hL (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have h0 : constantCoeff h = 0 := by
    have e := WickVanishing.coeff_ev_zero_left h 0
    rw [hc.ax0, Finsupp.embDomain_zero] at e
    rw [← coeff_zero_eq_constantCoeff_apply, ← e, map_zero]
  unfold FB.hL
  rw [WickVanishing.gt_const_ev_eq _ ?_ h, h0]
  intro j
  fin_cases j
  · exact WickVanishing.gp_pt 0
  · exact WickVanishing.gp_comp1 _ _ (fun i => by simp [FB.actK, B.A.const]) (WickVanishing.gp_pt 0)

theorem sc_of (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCSt := by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 P hPint e he f hf
  set x := (m : k) • B.hL k h w0 with hx
  have hx0 : constantCoeff x = 0 := by
    rw [hx, smul_eq_C_mul, map_mul, constantCoeff_C, cc_hL B h hcg w0, mul_zero]
  set E0 := liftX k (FB.expS k x) with hE0def
  set E1 := liftX k (FB.expS k (-x)) with hE1def
  have hE : E0 * E1 = 1 := by
    rw [hE0def, hE1def, ← liftX_mul, ← WickVanishing.gt_expS_add _ _ hx0 (by rw [map_neg, hx0, neg_zero]),
      add_neg_cancel, expS_zero', liftX_eq_rename, map_one]
  have hE0 : constantCoeff E0 = 1 := by rw [hE0def, cc_liftX, cc_expS _ hx0]
  have hgood : ∀ l X, GoodE R E0 X → GoodE R E0 (nabla k B h m (ξh l).1 (ξh l).2 X) := by
    rintro l X ⟨G, hG, rfl⟩
    refine ⟨E1 * nabla k B h m (ξh l).1 (ξh l).2 (E0 * G),
      hN1 R d O k hRQ B h hcg w0 hw0 m (ξh l) (hH l) G hG, ?_⟩
    rw [← mul_assoc, hE, one_mul]
  have hσ : GoodE R E0 (liftX k (FB.expS k x * f)) := ⟨liftX k f, intAA_liftX f hf, liftX_mul _ _⟩
  have haa : ∀ l l', s l = s l' → betaH k (ξh l) (ξh l') = 0 := fun l l' e' => h11 l l' fun hh => hh.2 e'
  have hab : ∀ l l', s l = s l' → betaH k (ξh l) (0, ψ l') = 0 := fun l l' e' => h12 l l' fun hh => hh.2 e'
  have hκ : ∀ l l', kapW m s ξh (fun l => (0, ψ l)) l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false := by
    intro l l' hne
    obtain ⟨hs, hs'⟩ := kapW_supp m s ξh _ l l' hne
    refine ⟨?_, hs, hs'⟩
    by_contra hc
    apply hne
    unfold kapW
    rw [if_pos ⟨hs, hs'⟩, h21 l l' (fun hh => hc hh.1), mul_zero]
  have hκJ : ∀ i j, kapE s (kapW m s ξh (fun l => (0, ψ l))) i j ∈ J := by
    intro i j
    unfold kapE kapW
    split_ifs
    · obtain ⟨u, φ, hu⟩ := hH ((sideE s).symm (Sum.inr j))
      rw [hu]
      unfold betaH
      simp only [Pi.zero_apply, mul_zero, zero_sub]
      rw [← nsmul_eq_mul]
      refine J.toAddSubmonoid.nsmul_mem (J.sum_mem fun t _ => J.neg_mem ?_) m
      rw [mul_comm, ← Algebra.smul_def]
      exact J.smul_mem _ (hψ _ t)
    · exact J.zero_mem
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (MvPolynomial.map (algebraMap R k)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha => ?_
    obtain ⟨n', _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    exact RingHom.mem_range.mp (hPint n')
  have ordNabla_wick (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
      [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
      (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
      (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
      ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
        ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
          PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
            (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
            (liftX k f) := by
    have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
      rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
      exact betaH_zero_zero _ _
    have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
      rw [betaH_antisymm, hab l' l e.symm, neg_zero]
    have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
    have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
    have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
    have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
    have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
        nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
      nablaL_add B h m _ _ _ _
    have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
        (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
      rw [hsum, hsum]
      exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
    rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
    have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
    have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
    have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
      (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
      (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
        cB _ _⟩)
      (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
        cB _ _⟩)
      (fun i j => cB _ _)
      (fun i j => by
        rw [nablaL_bracket hN2 B h m]
        unfold kapE kapW
        rw [if_pos ⟨side_inl s i, side_inr s j⟩])
      (fun i => by
        rw [Module.End.smul_def, opL, hb0]
        exact hN3 R d O k B h m _ f)
      (fun j => by
        rw [Module.End.smul_def, opR, hb0]
        exact hN3 R d O k B h m _ f)
      (MvPolynomial.rename (sideE s) P)
    rw [hL, hR, ← Module.End.smul_def, key]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ordNabla_wick hN2 hN3 B h m s ξh (fun l => (0, ψ l)) (fun _ => rfl) haa hab P (FB.expS k x * f), map_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  refine cc_ordEval_mem J e E0 hE0 (opL B h m s ξh) (opR B h m s ξh) (fun i => hgood _) (fun j => hgood _) _ hσ _
    fun mo => ?_
  by_cases hne : n ≤ e
  · refine pow_le_pow_right' (Submodule.one_le.mpr hJ1) hne ?_
    have key := (_root_.divided_power_integrality R k _ _ J _ hκJ (MvPolynomial.rename (sideE s) P0) n).1 mo
    rw [← delta_pow_rename s _ (kapW_supp m s ξh _) n P, ← hP0, ← MvPolynomial.map_rename]
    exact key
  · rw [secondOrder_iterate_eq_zero c s _ hκ P e he n (by omega), map_zero, smul_zero, MvPolynomial.coeff_zero]
    exact Submodule.zero_mem _

end ReciprocityTheory.ChartRestriction.G.TB.SCPf

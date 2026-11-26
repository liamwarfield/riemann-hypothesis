module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionEmbedding
section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYGenCoefHom
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem midI_val (r : ℕ) (j : Fin r) : (midI r j).val = j.val + 1 := by
  simp [midI]

theorem midI_inj (r : ℕ) (i j : Fin r) : midI r i = midI r j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [midI_val, midI_val] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

theorem midI_lt (r : ℕ) {i j : Fin r} (h : i < j) : midI r i < midI r j := by
  rw [Fin.lt_iff_val_lt_val, midI_val, midI_val]
  have := Fin.lt_iff_val_lt_val.mp h
  omega

theorem midOf_midI (r : ℕ) (j : Fin r) : midOf (midI r j) = some j := by
  have hv := midI_val r j
  have hj := j.isLt
  unfold midOf
  rw [dite_eq_left (by rw [hv]; exact ⟨Nat.succ_pos _, by omega⟩)]
  congr 1

theorem midOf_cases {r : ℕ} (t : Fin (r + 1 + 1)) :
    (∃ j, t = midI r j) ∨ (midOf t = none ∧ (t = 0 ∨ t = Fin.last (r + 1))) := by
  have ht := t.isLt
  by_cases h : 0 < t.val ∧ t.val < r + 1
  · left
    refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
    ext
    rw [midI_val]
    dsimp only
    omega
  · right
    refine ⟨by unfold midOf; rw [dite_eq_right h], ?_⟩
    by_cases h0 : t.val = 0
    · left
      exact Fin.ext (by simp [h0])
    · right
      exact Fin.ext (by simp; omega)

theorem midOf_none_ne {r : ℕ} {t : Fin (r + 1 + 1)} (h : midOf t = none) (j : Fin r) : midI r j ≠ t := by
  rintro rfl
  rw [midOf_midI] at h
  exact Option.some_ne_none _ h

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

theorem subY_X_none (A : Type) [CommRing A] (r : ℕ) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    subY A r (X (a, t)) = X (a, t) := by
  simp only [subY, aeval_X, h]

theorem subY_C (A : Type) [CommRing A] (r : ℕ) (a : A) : subY A r (C a) = C (C a) := by
  simp [subY]

section MAH

variable {R S1 S2 σ : Type} [CommRing R] [CommRing S1] [CommRing S2] [Algebra R S1] [Algebra R S2]

theorem mAH_coeff (f : S1 →ₐ[R] S2) (p : MvPolynomial σ S1) (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (mapAlgHom f p) u = f (AddMonoidAlgebra.coeff p u) := by
  show AddMonoidAlgebra.coeff (map (f : S1 →+* S2) p) u = _
  rw [coeff_map]
  rfl

theorem mAH_C (f : S1 →ₐ[R] S2) (b : S1) : mapAlgHom f (C b : MvPolynomial σ S1) = C (f b) := by
  show map (f : S1 →+* S2) (C b) = _
  rw [map_C]
  rfl

theorem mAH_X (f : S1 →ₐ[R] S2) (w : σ) : mapAlgHom f (X w : MvPolynomial σ S1) = X w := by
  show map (f : S1 →+* S2) (X w) = _
  rw [map_X]

end MAH

theorem mAH_subY_mid {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a : Fin (r + 1 + 1)) (j : Fin r) :
    mapAlgHom f (subY A r (X (a, midI r j))) = ∑ i : Fin r, C (f (X (i, j))) * X (a, midI r i) := by
  rw [subY_X_mid]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, mAH_C, mAH_X]

theorem mAH_subY_none {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    mapAlgHom f (subY A r (X (a, t))) = X (a, t) := by
  rw [subY_X_none A r a t h, mAH_X]

section Coef

variable {A : Type} [CommRing A] {r : ℕ} {σ : Type}

def CoefHom (μ : Fin r → ℕ) (h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) : Prop :=
  ∀ u, IsWeightedHomogeneous (colW r r) (AddMonoidAlgebra.coeff h u) μ

theorem CoefHom.sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) (μ : Fin r → ℕ)
    (h : ∀ i ∈ s, CoefHom μ (f i)) : CoefHom μ (∑ i ∈ s, f i) := by
  intro u
  rw [coeff_sum]
  exact IsWeightedHomogeneous.sum _ _ _ (fun i hi => h i hi u)

theorem CoefHom.mul {μ μ' : Fin r → ℕ} {h1 h2 : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)}
    (a : CoefHom μ h1) (b : CoefHom μ' h2) : CoefHom (μ + μ') (h1 * h2) := by
  classical
  intro u
  rw [coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (a x.1).mul (b x.2))

theorem CoefHom.ofC {μ : Fin r → ℕ} {b : MvPolynomial (Fin r × Fin r) A} (hb : IsWeightedHomogeneous (colW r r) b μ) :
    CoefHom (σ := σ) μ (C b) := by
  classical
  intro u
  rw [coeff_C]
  split_ifs
  · exact hb
  · exact isWeightedHomogeneous_zero _ _ _

theorem CoefHom.ofX (w : σ) : CoefHom (A := A) (r := r) 0 (X w) := by
  classical
  intro u
  rw [coeff_X']
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem CoefHom.one : CoefHom (A := A) (r := r) (σ := σ) 0 1 := by
  classical
  intro u
  rw [coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · intro d hd
    simp at hd

theorem CoefHom.pow {μ : Fin r → ℕ} {h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)} (a : CoefHom μ h) (n : ℕ) :
    CoefHom (n • μ) (h ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact CoefHom.one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul a

theorem CoefHom.prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A))
    (μ : ι → Fin r → ℕ) (h : ∀ i ∈ s, CoefHom (μ i) (f i)) : CoefHom (∑ i ∈ s, μ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact CoefHom.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end Coef

theorem subY_gen_coefHom (A : Type) [CommRing A] (r : ℕ) (w : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    CoefHom (fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) (subY A r (X w)) := by
  obtain ⟨a, t⟩ := w
  rcases midOf_cases t with ⟨j, rfl⟩ | ⟨hn, -⟩
  · rw [subY_X_mid]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, midI r j) (midI r j')) = colW r r (j, j) := by
      funext j'
      simp only [colW, Pi.single_apply, midI_inj]
    rw [hf]
    apply CoefHom.sum
    intro i _
    have h := (CoefHom.ofC (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (isWeightedHomogeneous_X A (colW r r) (i, j))).mul (CoefHom.ofX (A := A) (r := r) (a, midI r i))
    rw [add_zero] at h
    exact h
  · rw [subY_X_none _ _ _ _ hn]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, t) (midI r j')) = 0 := by
      funext j'
      simp [colW, Pi.single_apply, midOf_none_ne hn j']
    rw [hf]
    exact CoefHom.ofX _

theorem subY_coefHom (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν) :
    CoefHom (fun j => ν (midI r j)) (subY A r v) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [v.as_sum, map_sum]
  apply CoefHom.sum
  intro m hm
  have hw : Finsupp.weight (colW (r + 1 + 1) (r + 1 + 1)) m = ν := hv (mem_support_iff.mp hm)
  rw [monomial_eq, map_mul, subY_C, Finsupp.prod, map_prod]
  have hP : CoefHom (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j))
      (∏ w ∈ m.support, subY A r (X w ^ m w)) := by
    apply CoefHom.prod
    intro w _
    rw [map_pow]
    exact (subY_gen_coefHom A r w).pow _
  have hC : CoefHom (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1)) (0 : Fin r → ℕ) (C (C (AddMonoidAlgebra.coeff v m))) := by
    apply CoefHom.ofC
    intro d hd
    rw [coeff_C] at hd
    split_ifs at hd with h0
    · subst h0
      simp
    · exact absurd rfl hd
  have h := hC.mul hP
  rw [zero_add] at h
  have hsum : (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) =
      fun j => ν (midI r j) := by
    funext j
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [hsum] at h
  exact h

theorem subY_inv (A : Type) [CommRing A] (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v) (l j : Fin r) (hlj : l < j)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    colAddGen A l j (AddMonoidAlgebra.coeff (subY A r v) u) = rename some (AddMonoidAlgebra.coeff (subY A r v) u) := by
  classical
  let Φ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (colAddGen A l j)
  let Ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (rename some)
  let θ : MvPolynomial (Option (Fin (r + 1 + 1) × Fin (r + 1 + 1))) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    aeval fun o => Option.elim o (C (X none)) fun w => Ψ (subY A r (X w))
  have hθn : θ (X none) = C (X none) := by
    simp [θ]
  have hθs : ∀ w, θ (X (some w)) = Ψ (subY A r (X w)) := fun w => by
    simp [θ]
  have h1 : Φ.comp (subY A r) = θ.comp (colAddGen A (midI r l) (midI r j)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp only [AlgHom.comp_apply, colAddGen_X]
    rcases midOf_cases t with ⟨j', rfl⟩ | ⟨hn, -⟩
    · rw [mAH_subY_mid]
      by_cases hj : j' = j
      · subst hj
        rw [if_pos rfl, map_add (f := _), map_mul, hθn, hθs, hθs, mAH_subY_mid, mAH_subY_mid, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_true, rename_X, map_add (f := _), map_mul]
        ring
      · rw [if_neg (fun h => hj ((midI_inj r j' j).mp h)), hθs, mAH_subY_mid]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_neg hj, rename_X]
    · rw [if_neg (midOf_none_ne hn j).symm, hθs, mAH_subY_none _ _ _ _ hn, mAH_subY_none _ _ _ _ hn]
  have h2 : Ψ.comp (subY A r) = θ.comp (rename some) := by
    apply MvPolynomial.algHom_ext
    intro w
    simp only [AlgHom.comp_apply, rename_X, hθs]
  have h3 : Φ (subY A r v) = Ψ (subY A r v) := by
    have e1 := congrArg (fun F => F v) h1
    have e2 := congrArg (fun F => F v) h2
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hv _ _ (midI_lt r hlj)]
  have h4 := congrArg (AddMonoidAlgebra.coeff · u) h3
  simp only [Φ, Ψ, mAH_coeff] at h4
  exact h4

theorem subCoeffP : SubCoeffP := by
  intro A _ r ν v hv u
  rw [lsat_mem_dualWeyl] at hv ⊢
  exact ⟨subY_coefHom A r ν v hv.1 u, fun l j hlj => subY_inv A r v hv.2 l j hlj u⟩

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def th (K : Type) [Field K] (r : ℕ) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom (blockEmb K (k := r) (n := r) b)).comp (subY K r)

theorem blockEmb_X (K : Type) [Field K] {k n : ℕ} (b : Bool) (x : Fin k × Fin n) :
    blockEmb K b (X x) = (X (b, x) : MvPolynomial (Bool × (Fin k × Fin n)) K) := by
  show rename _ (X x) = _
  rw [rename_X]

theorem th_C (K : Type) [Field K] (r : ℕ) (b : Bool) (a : K) : th K r b (C a) = C (C a) := by
  rw [th, AlgHom.comp_apply, subY_C, mAH_C, algHom_C, algebraMap_eq]

theorem th_X_mid (K : Type) [Field K] (r : ℕ) (b : Bool) (a : Fin (r + 1 + 1)) (j : Fin r) :
    th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
  rw [th, AlgHom.comp_apply, mAH_subY_mid]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockEmb_X]

theorem th_X_none (K : Type) [Field K] (r : ℕ) (b : Bool) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    th K r b (X (a, t)) = X (a, t) := by
  rw [th, AlgHom.comp_apply, mAH_subY_none r _ a t h]

theorem th_coeff (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (th K r b v) u = blockEmb K b (AddMonoidAlgebra.coeff (subY K r v) u) := by
  rw [th, AlgHom.comp_apply, mAH_coeff]

theorem block_substitution_embedding (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = th K r b v := by
  have : (sub2 K r).comp (blockEmb K (k := r + 1 + 1) (n := r + 1 + 1) b) = th K r b := by
    apply algHom_ext
    intro w
    rw [AlgHom.comp_apply, blockEmb_X]
    unfold sub2
    rw [aeval_X]
    rfl
  exact AlgHom.congr_fun this v

theorem lam_eq (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    lamOf K r L (blockEmb K true v * blockEmb K false t) = lcoef L (th K r true v * th K r false t) := by
  unfold lamOf
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, block_substitution_embedding, block_substitution_embedding]

section Psi

variable {K B σ : Type} [Field K] [CommRing B] [Algebra K B]

def psiB (B : Type) [CommRing B] [Algebra K B] (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ B →+* MvPolynomial σ B :=
  eval₂Hom C (fun w => map (algebraMap K B) (ψ (X w)))

theorem psiB_C (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (b : B) : psiB B ψ (C b) = C b := by
  show eval₂ _ _ (C b) = _
  rw [eval₂_C]

theorem psiB_X (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (w : σ) :
    psiB B ψ (X w) = map (algebraMap K B) (ψ (X w)) := by
  show eval₂ _ _ (X w) = _
  rw [eval₂_X]

theorem psiB_map (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (G : MvPolynomial σ K) :
    psiB B ψ (map (algebraMap K B) G) = map (algebraMap K B) (ψ G) := by
  have : (psiB B ψ).comp (map (algebraMap K B)) = (map (algebraMap K B)).comp (ψ : MvPolynomial σ K →+* MvPolynomial σ K) := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_C, psiB_C, algHom_C, algebraMap_eq]
    · intro w
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_X, psiB_X]
  exact RingHom.congr_fun this G

theorem lcoef_C_mul_map (L : B →ₗ[K] K) (b : B) (G : MvPolynomial σ K) :
    lcoef L (C b * map (algebraMap K B) G) = L b • G := by
  ext u
  rw [coeff_lcoef, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul, mul_comm b, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

theorem lcoef_comm (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (L : B →ₗ[K] K) (h : MvPolynomial σ B) :
    ψ (lcoef L h) = lcoef L (psiB B ψ h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial u b =>
    have e : (monomial u b : MvPolynomial σ B) = C b * map (algebraMap K B) (monomial u 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, lcoef_C_mul_map, map_mul, psiB_map, psiB_C, lcoef_C_mul_map, map_smul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem hom_eq_on {S : Type} [CommRing S] (f g : MvPolynomial σ K →+* S) (hC : ∀ a, f (C a) = g (C a))
    (hX : ∀ w, f (X w) = g (X w)) (v : MvPolynomial σ K) : f v = g v := by
  rw [ringHom_ext hC hX]

end Psi

theorem pow_exp_inj {K : Type} [Field K] [Infinite K] (a b : ℕ) (h : ∀ c : K, c ≠ 0 → c ^ a = c ^ b) : a = b := by
  have h1 : (Polynomial.X ^ (a + 1) : Polynomial K) = Polynomial.X ^ (b + 1) := by
    apply Polynomial.funext
    intro c
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hc : c = 0
    · rw [hc, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.succ_ne_zero _)]
    · rw [pow_succ, pow_succ, h c hc]
  have h2 := congrArg Polynomial.natDegree h1
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h2
  omega

section Scale

variable {K : Type} [Field K]

theorem sc_monomial {σ : Type} (d : σ → K) (u : σ →₀ ℕ) (a : K) :
    aeval (fun w => C (d w) * X w) (monomial u a) = monomial u (a * u.prod fun w e => d w ^ e) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (d v) : MvPolynomial σ K) ^ e) = C (u.prod fun v e => d v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, monomial_eq, C_mul, algebraMap_eq]
  ring

theorem sc_coeff {σ : Type} (d : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun w => C (d w) * X w) f) m = AddMonoidAlgebra.coeff f m * m.prod fun w e => d w ^ e := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [sc_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

def scCol (K : Type) [Field K] (k : ℕ) (t0 : Fin k) (c : K) :
    MvPolynomial (Fin k × Fin k) K →ₐ[K] MvPolynomial (Fin k × Fin k) K :=
  aeval (fun w => C (if w.2 = t0 then c else 1) * X w)

theorem scCol_X {k : ℕ} (t0 : Fin k) (c : K) (w : Fin k × Fin k) :
    scCol K k t0 c (X w) = C (if w.2 = t0 then c else 1) * X w := by
  unfold scCol
  rw [aeval_X]

theorem sc_prod {k : ℕ} (t0 : Fin k) (c : K) (m : Fin k × Fin k →₀ ℕ) :
    (m.prod fun w e => (if w.2 = t0 then c else 1) ^ e) = c ^ (Finsupp.weight (colW k k) m t0) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, lccomp_weight_colW_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single t0]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem scCol_coeff {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (m : Fin k × Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (scCol K k t0 c f) m = AddMonoidAlgebra.coeff f m * c ^ (Finsupp.weight (colW k k) m t0) := by
  unfold scCol
  rw [sc_coeff, sc_prod]

theorem scCol_of_hom {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (ν : Fin k → ℕ)
    (hf : IsWeightedHomogeneous (colW k k) f ν) : scCol K k t0 c f = c ^ ν t0 • f := by
  ext m
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]
  by_cases h : AddMonoidAlgebra.coeff f m = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hf h]

theorem wt_of_scale [Infinite K] {k : ℕ} (t0 : Fin k) (n : ℕ) (f : MvPolynomial (Fin k × Fin k) K)
    (h : ∀ c : K, c ≠ 0 → scCol K k t0 c f = c ^ n • f) (m : Fin k × Fin k →₀ ℕ) (hm : AddMonoidAlgebra.coeff f m ≠ 0) :
    Finsupp.weight (colW k k) m t0 = n := by
  apply pow_exp_inj (K := K)
  intro c hc
  have := congrArg (AddMonoidAlgebra.coeff · m) (h c hc)
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm] at this
  exact mul_right_cancel₀ hm this

theorem colAdd_trivial {k : ℕ} (l j : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K)
    (hf : ∀ m, AddMonoidAlgebra.coeff f m ≠ 0 → Finsupp.weight (colW k k) m j = 0) : colAdd K l j c f = f := by
  classical
  have e : colAdd K l j c f = ∑ m ∈ f.support, colAdd K l j c (monomial m (AddMonoidAlgebra.coeff f m)) := by
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [e]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  unfold colAdd
  rw [aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro w hw
  have hwj : w.2 ≠ j := by
    intro h
    have h0 := hf m (mem_support_iff.1 hm)
    rw [lccomp_weight_colW_apply] at h0
    have h1 := Finset.sum_eq_zero_iff.1 h0 w.1 (Finset.mem_univ _)
    have e2 : w = (w.1, j) := Prod.ext rfl h
    apply Finsupp.mem_support_iff.1 hw
    rw [e2]
    exact h1
  rw [if_neg hwj]

end Scale

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.RowActTransv
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

variable {K : Type} [Field K] {r : ℕ}

theorem caseN (t0 : Fin (r + 1 + 1)) (h0 : midOf t0 = none) (c : K) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (scCol K (r + 1 + 1) t0 c) (th K r b v) =
      th K r b (scCol K (r + 1 + 1) t0 c v) := by
  have key := hom_eq_on
    ((psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (scCol K (r + 1 + 1) t0 c)).comp (th K r b).toRingHom)
    ((th K r b).toRingHom.comp (scCol K (r + 1 + 1) t0 c).toRingHom) ?_ ?_ v
  · simpa using key
  · intro a
    simp [th_C, psiB_C]
  · rintro ⟨a, t⟩
    rcases midOf_cases t with ⟨j, rfl⟩ | ⟨ht, -⟩
    · have hne : ∀ i : Fin r, midI r i ≠ t0 := fun i => midOf_none_ne h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [th_X_mid, psiB_X, scCol_X, hne, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiB_C]
    · simp [th_X_none _ _ _ _ _ ht, psiB_X, scCol_X]

theorem lam_scaleN (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (t0 : Fin (r + 1 + 1)) (h0 : midOf t0 = none)
    (c : K) (ν ν' : Fin (r + 1 + 1) → ℕ) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν)
    (ht : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) t ν') :
    scCol K (r + 1 + 1) t0 c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      c ^ (ν t0 + ν' t0) • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  rw [lam_eq, lcoef_comm, map_mul, caseN t0 h0, caseN t0 h0, scCol_of_hom _ _ _ _ hv, scCol_of_hom _ _ _ _ ht,
    map_smul, map_smul, smul_mul_smul_comm, ← pow_add, map_smul]

def thR (K : Type) [Field K] (r : ℕ) (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom ((blockEmb K (k := r) (n := r) b).comp ρ)).comp (subY K r)

theorem thR_coeff (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (thR K r ρ b v) u = blockEmb K b (ρ (AddMonoidAlgebra.coeff (subY K r v) u)) := by
  simp only [thR, AlgHom.comp_apply, mAH_coeff]

theorem caseM (ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K)
    (hgen : ∀ (b : Bool) (a : Fin (r + 1 + 1)) (j' : Fin r),
      ∑ i : Fin r, (C (X (b, (i, j'))) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)) *
          map (algebraMap K (MvPolynomial (Bool × (Fin r × Fin r)) K)) (ψ (X (a, midI r i))) =
        ∑ i : Fin r, C (blockEmb K b (ρ (X (i, j')))) * X (a, midI r i))
    (hnone : ∀ a t, midOf t = none → ψ (X (a, t)) = X (a, t)) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) ψ (th K r b v) = thR K r ρ b v := by
  have key := hom_eq_on
    ((psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) ψ).comp (th K r b).toRingHom)
    (thR K r ρ b).toRingHom ?_ ?_ v
  · simpa using key
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_C]
    rw [psiB_C]
    simp only [thR, AlgHom.comp_apply, subY_C, mAH_C, AlgHom.commutes]
    simp
  · rintro ⟨a, t⟩
    rcases midOf_cases t with ⟨j, rfl⟩ | ⟨ht, -⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_X_mid, map_sum, map_mul]
      simp only [thR, AlgHom.comp_apply, mAH_subY_mid]
      rw [← hgen b a j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiB_C, psiB_X]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_X_none _ _ _ _ _ ht]
      simp only [thR, AlgHom.comp_apply, mAH_subY_none _ _ _ _ ht]
      rw [psiB_X, hnone a t ht, map_X]

theorem lam_caseM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L)
    (ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (l : Matrix (Fin r) (Fin r) K) (hl : IsUnit l.det)
    (hgen : ∀ (b : Bool) (a : Fin (r + 1 + 1)) (j' : Fin r),
      ∑ i : Fin r, (C (X (b, (i, j'))) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)) *
          map (algebraMap K (MvPolynomial (Bool × (Fin r × Fin r)) K)) (ψ (X (a, midI r i))) =
        ∑ i : Fin r, C (blockEmb K b (rowAct K l (X (i, j')))) * X (a, midI r i))
    (hnone : ∀ a t, midOf t = none → ψ (X (a, t)) = X (a, t))
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, AddMonoidAlgebra.coeff (subY K r v) u ∈ dualWeyl K r r α) (ht : ∀ u, AddMonoidAlgebra.coeff (subY K r t) u ∈ dualWeyl K r r α') :
    ψ (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      l.det ^ N • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  have hc : ∀ (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K))
      (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ), AddMonoidAlgebra.coeff (lcoef L h) u = L (AddMonoidAlgebra.coeff h u) := by
    intro h u
    exact coeff_sum_monomial_linear L h u
  rw [lam_eq, lcoef_comm, map_mul, caseM ψ (rowAct K l) hgen hnone, caseM ψ (rowAct K l) hgen hnone]
  ext u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_smul, hc, hc, coeff_mul, coeff_mul, map_sum, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thR_coeff, thR_coeff, th_coeff, th_coeff]
  exact hInv l hl _ (hv p.1) _ (ht p.2)

theorem lam_scaleM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L) (j : Fin r) (c : K) (hc : c ≠ 0)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, AddMonoidAlgebra.coeff (subY K r v) u ∈ dualWeyl K r r α) (ht : ∀ u, AddMonoidAlgebra.coeff (subY K r t) u ∈ dualWeyl K r r α') :
    scCol K (r + 1 + 1) (midI r j) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      c ^ N • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  classical
  have hdet : (Matrix.diagonal (fun i : Fin r => if i = j then c else 1)).det = c := by
    rw [Matrix.det_diagonal, Finset.prod_ite_eq']
    simp
  have key := lam_caseM L N α α' hInv (scCol K (r + 1 + 1) (midI r j) c)
    (Matrix.diagonal (fun i : Fin r => if i = j then c else 1)) (by rw [hdet]; exact hc.isUnit) ?_ ?_ v t hv ht
  · rw [hdet] at key
    exact key
  · intro b a j'
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [scCol_X, midI_inj, rowAct, aeval_X, Matrix.diagonal_apply, blockEmb, map_mul, map_C, map_X,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, rename_C, rename_X]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_true, MvPolynomial.algebraMap_eq]
    ring
  · intro a t' ht'
    rw [scCol_X]
    have hne : t' ≠ midI r j := fun e => midOf_none_ne ht' j e.symm
    simp [hne]

theorem rowAct_transv (l j : Fin r) (c : K) (i t : Fin r) :
    rowAct K (Matrix.transvection l j c) (X (i, t)) = X (i, t) + if i = l then C c * X (j, t) else 0 := by
  classical
  simp only [rowAct, aeval_X, Matrix.transvection, Matrix.add_apply, Matrix.one_apply]
  simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, apply_ite C, ite_mul, map_one, map_zero, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  by_cases h : i = l
  · subst h
    simp only [Matrix.single_apply, true_and]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have h' : ¬ l = i := fun e => h e.symm
    simp [Matrix.single_apply, h, h']

theorem lam_addM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L) (l j : Fin r) (hlj : l ≠ j) (c : K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, AddMonoidAlgebra.coeff (subY K r v) u ∈ dualWeyl K r r α) (ht : ∀ u, AddMonoidAlgebra.coeff (subY K r t) u ∈ dualWeyl K r r α') :
    colAdd K (midI r l) (midI r j) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  classical
  have hdet : (Matrix.transvection l j c).det = 1 := Matrix.det_transvection_of_ne l j hlj c
  have key := lam_caseM L N α α' hInv (colAdd K (midI r l) (midI r j) c) (Matrix.transvection l j c)
    (by rw [hdet]; exact isUnit_one) ?_ ?_ v t hv ht
  · rw [hdet, one_pow, one_smul] at key
    exact key
  · intro b a j'
    simp only [rowAct_transv, colAdd, aeval_X, midI_inj]
    have e : ∀ i : Fin r, (if i = j then X (a, midI r i) + C c * X (a, midI r l) else X (a, midI r i) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) =
        X (a, midI r i) + if i = j then C c * X (a, midI r l) else 0 := by
      intro i
      split_ifs <;> simp
    simp only [e, map_add (f := _), map_mul, map_C, map_X, blockEmb, rename_X, rename_C, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite, map_zero, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hs : ∀ (k : Fin r)
        (f g : Fin r → MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)),
        (∑ x : Fin r, if x = k then f x + g x else f x + 0) = (∑ x : Fin r, f x) + g k := by
      intro k f g
      have h1 : ∀ x, (if x = k then f x + g x else f x + 0) = f x + if x = k then g x else 0 := by
        intro x
        split_ifs <;> simp
      simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hs j (fun x => C (X (b, x, j')) * X (a, midI r x))
        (fun x => C (X (b, x, j')) * (C ((algebraMap K (MvPolynomial (Bool × Fin r × Fin r) K)) c) * X (a, midI r l))),
      hs l (fun x => C (X (b, x, j')) * X (a, midI r x)) (fun x => C (C c) * C (X (b, j, j')) * X (a, midI r x))]
    simp only [MvPolynomial.algebraMap_eq]
    ring
  · intro a t' ht'
    have hne : t' ≠ midI r j := fun e => midOf_none_ne ht' j e.symm
    simp [colAdd, hne]

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamAddC
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem multiInv {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v)
    (θ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A] S) (e : Fin r → S) (J : Finset (Fin r)) :
    aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
      θ (X w) + (∑ j ∈ J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0))) v = θ v := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul, add_zero]
    exact (congrArg (fun ψ => ψ v) (MvPolynomial.aeval_unique θ)).symm
  | @insert j0 J hj0 ih =>
    have h0 := hv 0 (midI r j0) (Fin.succ_pos _)
    set f : Fin (r + 1 + 1) × Fin (r + 1 + 1) → S := fun w =>
      θ (X w) + (∑ j ∈ J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0)) with hf
    have hz : ∀ j : Fin r, ((0 : Fin (r + 1 + 1)) = midI r j) ↔ False :=
      fun j => ⟨fun h => Fin.succ_ne_zero _ h.symm, False.elim⟩
    have hφ : (aeval (Option.elim' (e j0) f)).comp (colAddGen A 0 (midI r j0)) =
        aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
          θ (X w) + (∑ j ∈ insert j0 J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0))) := by
      rw [colAddGen, MvPolynomial.comp_aeval]
      congr 1
      funext w
      by_cases hw : w.2 = midI r j0
      · simp [hw, hf, Finset.sum_insert hj0, hz]
        try ring
      · simp [hw, hf, Finset.sum_insert hj0, hz]
        try ring
    rw [← hφ, AlgHom.comp_apply, h0, MvPolynomial.aeval_rename]
    exact ih

variable {K : Type} [Field K] {r : ℕ}

theorem caseC (j0 : Fin r) (c : K) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j v = rename some v) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c) (th K r b v) = th K r b v := by
  classical

  have hmidOf_midI : ∀ j : Fin r, midOf (midI r j) = some j := by
    intro j
    unfold midOf midI
    rw [dite_eq_left (by first | (simp [Fin.val_succ]; done) | (simp [Fin.val_succ]; omega))]
    exact congrArg some (Fin.ext (by simp [Fin.val_succ]))
  have hsome : ∀ (t : Fin (r + 1 + 1)) (j : Fin r), midOf t = some j → t = midI r j := by
    intro t j h
    unfold midOf at h
    split_ifs at h with h1
    cases h
    apply Fin.ext
    simp [midI, Fin.val_succ]
    omega
  have hnone : ∀ (t : Fin (r + 1 + 1)) (j : Fin r), midOf t = none → t ≠ midI r j := by
    intro t j h ht
    rw [ht, hmidOf_midI] at h
    cases h
  have h00 : midOf (0 : Fin (r + 1 + 1)) = none := by
    unfold midOf
    rw [dite_eq_right (by simp)]
  have hth0 : ∀ a, th K r b (X (a, 0)) = X (a, 0) := by
    intro a
    simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, h00]
  let e : Fin r → MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
    fun j => C (C c * X (b, (j0, j)))
  have hmult := multiInv r v hv (th K r b) e Finset.univ
  have key : (psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c)).comp (th K r b).toRingHom =
      (aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
        th K r b (X w) + (∑ j ∈ Finset.univ, if w.2 = midI r j then e j else 0) * th K r b (X (w.1, 0)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [th, psiB, MvPolynomial.algebraMap_apply]
    · rintro ⟨a, t⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hth0]
      rcases hw : midOf t with _ | j
      · have e1 : th K r b (X (a, t)) = X (a, t) := by simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, hw]
        have hz : (∑ j ∈ Finset.univ, if t = midI r j then e j else 0) = 0 :=
          Finset.sum_eq_zero fun j _ => if_neg (hnone t j hw)
        rw [e1, hz, zero_mul, add_zero]
        simp [psiB, Formalism.GradedWeylDivisibility.colAdd, hnone t j0 hw]
      · have ht : t = midI r j := hsome t j hw
        subst ht
        have e1 : th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
          simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, hmidOf_midI, Formalism.GradedWeylDivisibility.blockEmb]
        have hz : (∑ j' ∈ Finset.univ, if midI r j = midI r j' then e j' else 0) = e j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro j' _ hj'
            rw [if_neg]
            intro h
            apply hj'
            have := congrArg midOf h
            rw [hmidOf_midI, hmidOf_midI] at this
            exact (Option.some_injective _ this).symm
          · simp
        have hmid : ∀ i : Fin r, i ≠ j0 → midI r i ≠ midI r j0 := by
          intro i hi h
          apply hi
          have h2 := congrArg midOf h
          rw [hmidOf_midI, hmidOf_midI] at h2
          exact Option.some_injective _ h2
        have hterm : ∀ i : Fin r, psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c)
            (C (X (b, (i, j))) * X (a, midI r i)) =
            C (X (b, (i, j))) * X (a, midI r i) + (if i = j0 then e j * X (a, 0) else 0) := by
          intro i
          simp only [psiB, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X, Formalism.GradedWeylDivisibility.colAdd, aeval_X]
          by_cases hi : i = j0
          · subst hi
            simp [e, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
            ring
          · simp [hmid i hi, hi]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e1, hz, map_sum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
        simp
  exact (RingHom.congr_fun key v).trans hmult

theorem lam_addC (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (j0 : Fin r) (c : K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j v = rename some v)
    (ht : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j t = rename some t) :
    colAdd K 0 (midI r j0) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  rw [lam_eq, lcoef_comm, map_mul, caseC j0 c true v hv, caseC j0 c false t ht]

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.flipOneThree.Pf.QB

theorem lamMemP : LamMemP := by
  intro K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht
  have hsv := fun u => subCoeffP K r ν v hv u
  have hst := fun u => subCoeffP K r ν' t ht u
  obtain ⟨hvw, hvi⟩ := mem_dualWeyl_iff.mp hv
  obtain ⟨htw, hti⟩ := mem_dualWeyl_iff.mp ht
  set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF
  have hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 →
      scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F := by
    intro t0 c hc
    rcases midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩
    · rw [hνpm j]
      exact lam_scaleM L N _ _ hPh j c hc v t hsv hst
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst h0
      rw [hνp0]
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst hl
      rw [hνl, hν'l, hνpl]
  have hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F := by
    intro l j hlj c
    rcases midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩
    · rcases midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩
      · have hne : l' ≠ j' := by
          rintro rfl
          exact lt_irrefl _ hlj
        exact lam_addM L N _ _ hPh l' j' hne c v t hsv hst
      · subst h0'
        exact lam_addC L j' c v t hvi hti
      · subst hl'
        exact absurd hlj (not_lt.mpr (Fin.le_last _))
    · subst h0
      exact absurd hlj (Fin.not_lt_zero _)
    · subst hl
      apply colAdd_trivial
      intro m hm
      rw [wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]
  rw [mem_dualWeyl_iff]
  refine ⟨?_, ?_⟩
  · intro m hm
    funext t0
    exact wt_of_scale t0 (νp t0) F (hscale t0) m hm
  · intro l j hlj
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)
    simp only [AlgHom.comp_apply, hcol l j hlj] at h1
    simpa [MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval] using h1

theorem subCoeffP : SubCoeffP := QB.subCoeffP

end Formalism.MainNotions.flipOneThree.Pf

end

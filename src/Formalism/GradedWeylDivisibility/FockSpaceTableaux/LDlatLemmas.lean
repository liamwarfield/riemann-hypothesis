module

public import Formalism.GradedWeylDivisibility.StatementD

@[expose] public section

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma ldlat_rowAct_one {R : Type*} [CommRing R] {k n : ℕ} :
    rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1 (fun b _ hb => by simp [Matrix.one_apply_ne (Ne.symm hb)]) (by simp)]
  simp

lemma ldlat_rowAct_inv_left (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K g⁻¹ x) = x := by
  rw [← AlgHom.comp_apply, h K k n g g⁻¹, Matrix.nonsing_inv_mul g hg, ldlat_rowAct_one, AlgHom.id_apply]

lemma ldlat_rowAct_inv_right (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g x) = x := by
  rw [← AlgHom.comp_apply, h K k n g⁻¹ g, Matrix.mul_nonsing_inv g hg, ldlat_rowAct_one, AlgHom.id_apply]

lemma ldlat_map_bidet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (map φ : MvPolynomial (Fin r × Fin n) R → _) = ((map φ : MvPolynomial _ R →+* MvPolynomial _ S)) from rfl,
    RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

lemma ldlat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] {w : σ → M} {f : MvPolynomial σ R} {μ : M}
    (hf : IsWeightedHomogeneous w f μ) : IsWeightedHomogeneous w (map φ f) μ := by
  intro m hm
  apply hf
  intro h0
  apply hm
  rw [coeff_map, h0, map_zero]

lemma ldlat_linInd_field {F K : Type*} [Field F] [Field K] [Algebra F K] {σ ι : Type*}
    {v : ι → MvPolynomial σ F} (hv : LinearIndependent F v) :
    LinearIndependent K (fun i => map (algebraMap F K) (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul] at h1 ⊢
    change _ = 0 at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
      Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

lemma ldlat_linInd_base {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) {σ ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : LinearIndependent R b) : LinearIndependent K (fun i => map (algebraMap R K) (b i)) := by
  letI : Algebra (FractionRing R) K := (IsFractionRing.lift hinj).toAlgebra
  have h1 : LinearIndependent R (fun i => map (algebraMap R (FractionRing R)) (b i)) := by
    have := hb.map' (mapAlgHom (Algebra.ofId R (FractionRing R))).toLinearMap (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact map_injective _ (IsFractionRing.injective R (FractionRing R)) hxy)
    exact this
  have h2 : LinearIndependent (FractionRing R) (fun i => map (algebraMap R (FractionRing R)) (b i)) :=
    (LinearIndependent.iff_fractionRing R (FractionRing R)).mp h1
  have h3 := ldlat_linInd_field (K := K) h2
  have hc : (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)) = algebraMap R K := by
    ext r
    simp [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
  convert h3 using 2 with i
  rw [map_map, hc]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma ldrow_rowAct_diag_eq {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) :
    rowAct R (n := n) (Matrix.diagonal t) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
  unfold rowAct
  congr 1
  funext v
  simp [Matrix.diagonal_apply, apply_ite C, ite_mul]

lemma ldrow_prod_rowDeg {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) (u : Fin k × Fin n →₀ ℕ) :
    (u.prod fun v e => t v.1 ^ e) = ∏ a : Fin k, t a ^ rowDeg u a := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun v => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  show ∏ y, t a ^ u (a, y) = _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

lemma ldrow_aeval_monomial {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (u : Fin k × Fin n →₀ ℕ) (c : R) :
    aeval (fun v : Fin k × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin k, t a ^ rowDeg u a) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (t v.1) : MvPolynomial (Fin k × Fin n) R) ^ e) =
      C (∏ a : Fin k, t a ^ rowDeg u a) := by
    rw [← ldrow_prod_rowDeg]
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hC, algebraMap_eq, map_mul]
  ring

lemma ldrow_coeff_rowAct_diag {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (f : MvPolynomial (Fin k × Fin n) R) (m : Fin k × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowAct R (Matrix.diagonal t) f) m = AddMonoidAlgebra.coeff f m * ∏ a : Fin k, t a ^ rowDeg m a := by
  rw [ldrow_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [ldrow_aeval_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

lemma ldrow_weight_rowW {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) (a : Fin k) :
    Finsupp.weight (rowW k n) m a = rowDeg m a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW k n i) (fun i => zero_smul ℕ _),
    Finset.sum_apply,
    Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    simp [rowW]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro s _
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem ldbasis_linearIndependent {σ R ι : Type*} [CommRing R] (o : MonomialOrder σ)
    (v : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => o.degree (v i))
    (hlc : ∀ i, o.leadingCoeff (v i) = 1) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have htne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hjmax⟩ :=
    (s.filter fun j => g j ≠ 0).exists_max_image (fun j => o.toSyn (o.degree (v j))) htne
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · (o.degree (v j))) hsum
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, MvPolynomial.coeff_sum,
    Finset.sum_eq_single j] at hcoeff
  · rw [coeff_smul, smul_eq_mul] at hcoeff
    have hone : (v j).coeff (o.degree (v j)) = 1 := hlc j
    rw [hone, mul_one] at hcoeff
    exact (Finset.mem_filter.mp hj).2 hcoeff
  · intro k hk hkj
    rw [coeff_smul]
    by_cases hgk : g k = 0
    · rw [hgk, zero_smul]
    · have hle := hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
      have hne : o.degree (v k) ≠ o.degree (v j) := fun h => hkj (hinj h)
      have hlt : o.toSyn (o.degree (v k)) < o.toSyn (o.degree (v j)) :=
        lt_of_le_of_ne hle (fun h => hne (o.toSyn.injective h))
      rw [o.coeff_eq_zero_of_lt hlt, smul_zero]
  · intro hj'
    exact absurd (Finset.mem_filter.mp hj).1 hj'

theorem ldbasis_sum_single_perm {r s : ℕ} (I : Fin s → Fin r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (I (σ q)) 1 : Fin r → ℕ)) = ∑ p : Fin s, Pi.single (I p) 1 := by
  exact Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))

theorem ldbasis_initMinor_rowHom (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hprod : IsWeightedHomogeneous (rowW r n)
      (∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (∑ p, Pi.single (I p) 1) := by
    rw [← ldbasis_sum_single_perm I σ]
    exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R (rowW r n) _)
  intro d hd
  apply hprod
  intro h0
  apply hd
  show AddMonoidAlgebra.coeff ((Equiv.Perm.sign σ) •
    ∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) d = 0
  rw [Units.smul_def, coeff_smul, h0, smul_zero]

theorem ldbasis_bidet_rowHom (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    IsWeightedHomogeneous (rowW r n) (bideterminant R sz hsz I)
      (∑ k : Fin K, ∑ p : Fin (sz k), Pi.single (I k p) 1) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ (fun k _ => ldbasis_initMinor_rowHom R (I k) (hsz k))

theorem ldbasis_rowWt_bidetExp {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    rowWt (bidetExp sz hsz I) = ∑ k : Fin K, ∑ p : Fin (sz k), (Pi.single (I k p) 1 : Fin r → ℕ) := by
  classical
  funext a
  simp only [rowWt, rowDeg, bidetExp, Finsupp.finsetSum_apply, Finset.sum_apply,
    Finsupp.single_apply, Pi.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : I k p = a
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h, Ne.symm h]

end Formalism.GradedWeylDivisibility
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldtwist_map_rowAct {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    map φ (rowAct K g F) = rowAct L (g.map φ) (map φ F) := by
  induction F using MvPolynomial.induction_on
  · rename_i a
    simp [rowAct]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq]
  · rename_i p v hp
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.map_apply]

end Formalism.GradedWeylDivisibility
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem ldtensor_prod_mem_prod {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {S : Type*}
    (T : Finset S) (N : S → Submodule R A) (x : S → A) (hx : ∀ s ∈ T, x s ∈ N s) :
    ∏ s ∈ T, x s ∈ ∏ s ∈ T, N s := by
  classical
  revert hx
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp le_rfl
  · intro s T hs ih hx
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact Submodule.mul_mem_mul (hx s (Finset.mem_insert_self s T))
      (ih fun t ht => hx t (Finset.mem_insert_of_mem ht))

theorem ldtensor_span_prod (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S]
    {k n : ℕ} {ι : S → Type*}
    (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K) (F : S → MvPolynomial (Fin k × Fin n) K)
    (hF : ∀ s, F s ∈ Submodule.span R (Set.range (b s))) :
    ∏ s, blockEmb K s (F s) ∈
      Submodule.span R (Set.range fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by
  have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (Set.range fun j => blockEmb K s (b s j)) := by
    intro s
    have h := Submodule.mem_map_of_mem (f := ((blockEmb K s).toLinearMap.restrictScalars R)) (hF s)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  have h2 := ldtensor_prod_mem_prod Finset.univ _ _ fun s _ => h1 s
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro y hy
  rw [Set.mem_finsetProd] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  choose i hi using fun s => hg (Finset.mem_univ s)
  exact ⟨i, Finset.prod_congr rfl fun s _ => hi s⟩

section Field

variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem ldtensor_glue_apply (α : S → (Fin k × Fin n →₀ ℕ)) (s : S) (v : Fin k × Fin n) :
    (∑ t, (α t).mapDomain (Prod.mk t)) (s, v) = α s v := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => by simpa using h) _ v
  · intro t _ hts
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w, hw⟩
    exact hts (congrArg Prod.fst hw)
  · simp

theorem ldtensor_glue_injective :
    Function.Injective (fun α : S → (Fin k × Fin n →₀ ℕ) => ∑ t, (α t).mapDomain (Prod.mk t)) := by
  intro α β h
  funext s
  ext v
  have e := congrArg (fun f => f (s, v)) h
  simpa [ldtensor_glue_apply] using e

theorem ldtensor_prod_monomial (α : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ s, blockEmb K s (monomial (α s) (1 : K)) = monomial (∑ t, (α t).mapDomain (Prod.mk t)) 1 := by
  simp only [blockEmb, rename_monomial]
  rw [monomial_sum_one]

def ldtensor_psi : PiTensorProduct K (fun _ : S => MvPolynomial (Fin k × Fin n) K) →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × (Fin k × Fin n)) K)).compLinearMap
    (fun s => (blockEmb K (k := k) (n := n) s).toLinearMap))

theorem ldtensor_psi_tprod (F : S → MvPolynomial (Fin k × Fin n) K) :
    ldtensor_psi K (tprod K F) = ∏ s, blockEmb K s (F s) := by
  unfold ldtensor_psi
  rw [PiTensorProduct.lift.tprod]
  simp [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem ldtensor_psi_injective : Function.Injective (ldtensor_psi K (S := S) (k := k) (n := n)) := by
  classical
  let B := Basis.piTensorProduct (fun _ : S => MvPolynomial.basisMonomials (Fin k × Fin n) K)
  have hB : ∀ α, B α = tprod K (fun s => monomial (α s) (1 : K)) := fun α => by
    simp [B, Basis.piTensorProduct_apply, MvPolynomial.coe_basisMonomials]
  have hli : LinearIndependent K (ldtensor_psi K ∘ B) := by
    have e : ldtensor_psi K ∘ B = fun α => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K) := by
      funext α
      simp only [Function.comp_apply, hB, ldtensor_psi_tprod, ldtensor_prod_monomial]
    rw [e]
    have h := (MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K).linearIndependent.comp _
      (ldtensor_glue_injective (S := S) (k := k) (n := n))
    have e2 : (fun α : S → (Fin k × Fin n →₀ ℕ) => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K)) =
        ⇑(MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K) ∘
          (fun α => ∑ t, (α t).mapDomain (Prod.mk t)) := by
      funext α
      simp [MvPolynomial.coe_basisMonomials]
    rw [e2]
    exact h
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← B.linearCombination_repr x] at hx ⊢
  rw [Finsupp.apply_linearCombination] at hx
  have h0 := (linearIndependent_iff.mp hli) _ hx
  rw [h0, map_zero]

theorem ldtensor_tprod_linInd {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) := by
  let E := fun s => Basis.extend (hb s).linearIndepOn_id
  let p : (∀ s, ι s) → ∀ s, ((hb s).linearIndepOn_id.extend (Set.subset_univ _) : Set _) :=
    fun i s => ⟨b s (i s), Basis.subset_extend _ (Set.mem_range_self _)⟩
  have hp : Function.Injective p := by
    intro i j h
    funext s
    have := congrArg (fun q => ((q s : _) : MvPolynomial (Fin k × Fin n) K)) h
    exact (hb s).injective this
  have := (Basis.piTensorProduct E).linearIndependent.comp p hp
  have e : (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) = (Basis.piTensorProduct E) ∘ p := by
    funext i
    simp [E, p, Basis.piTensorProduct_apply, Basis.coe_extend]
  rw [e]
  exact this

theorem ldtensor_prod_linInd_field {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by
  have h := (ldtensor_tprod_linInd K b hb).map' (ldtensor_psi K)
    (LinearMap.ker_eq_bot.mpr (ldtensor_psi_injective K))
  have e : (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) =
      ldtensor_psi K ∘ (fun i => tprod K fun s => b s (i s)) := by
    funext i
    simp [ldtensor_psi_tprod]
  rw [e]
  exact h

end Field

theorem tensor_power_basis : TensorBasis := by
  intro R K _ _ _ _ _ S _ _ k n ι M b hb hM
  have hK : ∀ s, LinearIndependent K (b s) := fun s => (LinearIndependent.iff_fractionRing R K).mp (hb s)
  refine ⟨(LinearIndependent.iff_fractionRing R K).mpr (ldtensor_prod_linInd_field K b hK), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun s => b s (i s), fun s => ?_, rfl⟩
    rw [← hM s]
    exact Submodule.subset_span ⟨i s, rfl⟩
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact ldtensor_span_prod R K b F fun s => by rw [hM s]; exact hF s

end Formalism.GradedWeylDivisibility
end
end

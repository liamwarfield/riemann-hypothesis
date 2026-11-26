module

public import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.DsInfCharCap
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EntriesZero
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RhoStrict
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MultTrOnBot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WeylEv
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem evT_ex' {n : ℕ} (θ x : Wt n) :
    evT θ (ex x) = Complex.exp (Complex.I * ∑ a, (θ a : ℂ) * (x a : ℂ)) := by
  simp [evT, ex, AddMonoidAlgebra.lift_single]

private theorem evT_alt' {n : ℕ} (θ x : Wt n) :
    evT θ (alt x) = (Matrix.of fun a b : Fin n => Complex.exp (Complex.I * ((θ a : ℂ) * (x b : ℂ)))).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [alt, map_sum, map_smul, evT_ex', smul_eq_mul, sg, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.exp_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
  rfl

private theorem den_ne {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde z).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [e, Matrix.det_permute']
  refine mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

private theorem first' {n : ℕ} (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ)
    (hz : ∀ a, z a = Complex.exp (Complex.I * θ a)) (hinj : Function.Injective z) :
    weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
  set c : Fin n → ℂ := fun a => Complex.exp (Complex.I * (θ a : ℂ) * ((1 - (n : ℂ)) / 2)) with hc
  have hcast : ∀ b : Fin n, (((n - 1 - (b : ℕ) : ℕ) : ℂ)) = (n : ℂ) - 1 - ((b : ℕ) : ℂ) := by
    intro b
    have := b.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hD : evT θ (alt (rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, hcast b]
    congr 1
    push_cast
    ring
  have hA : evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (lam j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c, Pi.add_apply]
    rw [← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    rw [hcast b]
    ring
  rw [hD, hA, weylChar]
  have hden := den_ne z hinj
  field_simp

theorem UpperTheory.RealTr.weylEv :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * θ a)) →
      (Function.Injective z → weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n))) ∧
      ((Function.Injective fun a => z a ^ 2) → weylChar lam (fun a => z a ^ 2) * evT θ (alt ((2 : ℝ) • rhoV n)) = evT θ (alt (twoL lam))) ∧
      ∏ a, ∏ b, (1 + z a / z b) = evT θ (∏ a, ∏ b, (1 + ex (rt a b))) ∧
      ∀ y : Fin n → ℂ, conj (weylChar lam fun a => conj (y a)) = weylChar lam y := by
  intro n lam θ z hz
  refine ⟨first' lam θ z hz, ?_, ?_, ?_⟩
  · intro hinj2
    have h := first' lam ((2 : ℝ) • θ) (fun a => z a ^ 2) (fun a => by
      rw [hz a, ← Complex.exp_nat_mul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring) hinj2
    have e1 : evT θ (alt ((2 : ℝ) • rhoV n)) = evT ((2 : ℝ) • θ) (alt (rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      push_cast
      ring
    have e2 : evT θ (alt (twoL lam)) = evT ((2 : ℝ) • θ) (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, twoL]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    exact h
  · simp only [map_prod, map_add (f := _), map_one, evT_ex']
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    congr 1
    rw [hz a, hz b, ← Complex.exp_sub]
    congr 1
    simp only [rt, Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
      apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro y
    simp only [weylChar, map_div₀, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1 <;> congr 1 <;> ext i j <;> simp [map_zpow₀]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LefForm
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ChiInj
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def chi {n : ℕ} (x : Wt n) : Multiplicative (Wt n) →* ℂ where
  toFun θ := Complex.exp (Complex.I * ∑ a, ((Multiplicative.toAdd θ a : ℝ) : ℂ) * (x a : ℂ))
  map_one' := by simp
  map_mul' s t := by
    simp [← Complex.exp_add, add_mul, mul_add, Finset.sum_add_distrib]

private theorem chi_inj {n : ℕ} : Function.Injective (chi (n := n)) := by
  intro x y hxy
  funext a
  by_contra hne
  have hd' : x a - y a ≠ 0 := sub_ne_zero.2 hne
  have e := congrArg (fun φ : Multiplicative (Wt n) →* ℂ =>
    φ (Multiplicative.ofAdd (Pi.single a (Real.pi / (x a - y a))))) hxy
  simp [chi, Pi.single_apply] at e
  rw [Complex.exp_eq_exp_iff_exists_int] at e
  obtain ⟨m, hm⟩ := e
  have hi := congrArg Complex.im hm
  simp at hi
  have hp : Real.pi / (x a - y a) * (x a - y a) = Real.pi := div_mul_cancel₀ _ hd'
  have h2 : Real.pi * 1 = Real.pi * (2 * m) := by linear_combination hi - hp
  have h3 := mul_left_cancel₀ Real.pi_ne_zero h2
  have h4 : (1 : ℤ) = 2 * m := by exact_mod_cast h3
  omega

private theorem evT_eq_sum_coeff_chi {n : ℕ} (θ : Wt n) (f : FR n) :
    evT θ f = ∑ x ∈ f.coeff.support, f.coeff x * chi x (Multiplicative.ofAdd θ) := by
  simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum, chi]

private theorem ev_zero {n : ℕ} (f : FR n) (h : ∀ θ : Wt n, evT θ f = 0) : f = 0 := by
  have hli : LinearIndependent ℂ (fun x : Wt n => ((chi x : Multiplicative (Wt n) → ℂ))) :=
    (linearIndependent_monoidHom (Multiplicative (Wt n)) ℂ).comp chi chi_inj
  apply AddMonoidAlgebra.ext
  apply linearIndependent_iff.1 hli
  ext θ
  have hθ := h (Multiplicative.toAdd θ)
  rw [evT_eq_sum_coeff_chi] at hθ
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simpa [Finset.sum_apply] using hθ

theorem UpperTheory.RealTr.evInj :
    ∀ (n : ℕ) (f : FR n), (∀ θ : Wt n, (Function.Injective fun a => Complex.exp (Complex.I * θ a) ^ 2) → evT θ f = 0) → f = 0 := by
  intro n f hf
  apply ev_zero f
  intro θ0
  let v : Wt n := fun a => ((a : ℕ) : ℝ)
  obtain ⟨bad, hbad, hmem⟩ : ∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, t ∉ S →
      Function.Injective fun a => Complex.exp (Complex.I * (((θ0 + t • v) a : ℝ) : ℂ)) ^ 2 := by
    refine ⟨⋃ p : Fin n × Fin n, ⋃ m : ℤ,
      {((m : ℝ) * Real.pi - (θ0 p.1 - θ0 p.2)) / (v p.1 - v p.2)}, ?_, ?_⟩
    · exact Set.countable_iUnion fun p => Set.countable_iUnion fun m => Set.countable_singleton _
    · intro t ht a b hab
      by_contra hne
      apply ht
      simp only at hab
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at hab
      obtain ⟨m, hm⟩ := hab
      have hi := congrArg Complex.im hm
      simp [Pi.add_apply, Pi.smul_apply] at hi
      have hv : v a - v b ≠ 0 := sub_ne_zero.2 (fun e => hne (Fin.ext (by simpa [v] using e)))
      refine Set.mem_iUnion.2 ⟨(a, b), Set.mem_iUnion.2 ⟨m, Set.mem_singleton_iff.2 ?_⟩⟩
      rw [eq_div_iff hv]
      linarith
  have hφ : (fun t : ℝ => evT (θ0 + t • v) f) = fun t => ∑ x ∈ f.coeff.support,
      f.coeff x * Complex.exp (Complex.I * ∑ a, (((θ0 a + t * v a : ℝ)) : ℂ) * (x a : ℂ)) := by
    funext t
    simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  have hcont : Continuous fun t : ℝ => evT (θ0 + t • v) f := by
    rw [hφ]
    fun_prop
  have hzero := Continuous.ext_on (hbad.dense_compl ℝ) hcont continuous_const
    (fun t ht => hf (θ0 + t • v) (hmem t ht))
  simpa using congrFun hzero 0
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem lefschetz_form_identities {A : Type*} [CommRing A] [NoZeroDivisors A]
    (D R D2 P q L T χ c₁ cT : A) (hR : R ≠ 0) (hD : D ≠ 0) (hD2 : D2 = D * R)
    (hP : P = q * (R * R)) (hχ : D * χ = L) (h1 : D2 * cT - P * T = 0)
    (h2 : D * D * c₁ - P * (L * L) = 0) :
    D * cT = q * (R * T) ∧ D * c₁ = q * (R * (D2 * (χ * χ))) := by
  subst hD2 hP hχ
  constructor
  · have h : R * (D * cT - q * (R * T)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hR
    · linear_combination h
  · have h : D * (D * c₁ - q * (R * (D * R * (χ * χ)))) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hD
    · linear_combination h

set_option maxHeartbeats 800000 in
theorem UpperTheory.RealTr.lefForm :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (c₁ cT χ : FR n), alt (rhoV n) * χ = alt ((fun a => (lam a : ℝ)) + rhoV n) →
      (∀ (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * θ a)) → (Function.Injective fun a => z a ^ 2) →
        evT θ c₁ = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2 ∧
        evT θ cT = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam fun a => z a ^ 2) →
      alt (rhoV n) * cT = (2 : ℂ) ^ n • (chR n * alt (twoL lam)) ∧
        alt (rhoV n) * c₁ = (2 : ℂ) ^ n • (chR n * (alt ((2 : ℝ) • rhoV n) * (χ * χ))) := by
  intro n lam c₁ cT χ hχ hev
  obtain ⟨hD2, hD, hR, -, -, -, hP, -⟩ := chRF n
  have hP' : (∏ a, ∏ b, (1 + ex (rt a b)) : FR n) = ((2:ℂ) ^ n • (1 : FR n)) * (chR n * chR n) := by
    rw [hP, smul_mul_assoc, one_mul]
  have h1 : alt ((2:ℝ) • rhoV n) * cT - (∏ a, ∏ b, (1 + ex (rt a b))) * alt (twoL lam) = 0 := by
    apply evInj
    intro θ hinj
    obtain ⟨-, hw2, hw3, -⟩ := weylEv n lam θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl)
    obtain ⟨-, hc⟩ := hev θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl) hinj
    rw [map_sub, map_mul, map_mul, hc, ← hw2 hinj, ← hw3, sub_eq_zero, mul_comm, mul_assoc]
  have h2 : alt (rhoV n) * alt (rhoV n) * c₁ - (∏ a, ∏ b, (1 + ex (rt a b)))
      * (alt ((fun a => (lam a : ℝ)) + rhoV n) * alt ((fun a => (lam a : ℝ)) + rhoV n)) = 0 := by
    apply evInj
    intro θ hinj
    have hz : Function.Injective (fun a => Complex.exp (Complex.I * θ a)) :=
      fun a b h => hinj (by simp only [h])
    obtain ⟨hw1, -, hw3, -⟩ := weylEv n lam θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl)
    obtain ⟨hc, -⟩ := hev θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl) hinj
    rw [map_sub, map_mul, map_mul, map_mul, map_mul, hc, ← hw1 hz, ← hw3]
    generalize (evT θ) (alt (rhoV n)) = A
    generalize (∏ a, ∏ b, (1 + Complex.exp (Complex.I * θ a) / Complex.exp (Complex.I * θ b))) = B
    generalize weylChar lam (fun a => Complex.exp (Complex.I * θ a)) = W
    ring
  obtain ⟨k1, k2⟩ := lefschetz_form_identities (alt (rhoV n)) (chR n) (alt ((2:ℝ) • rhoV n))
    (∏ a, ∏ b, (1 + ex (rt a b))) ((2:ℂ) ^ n • (1 : FR n))
    (alt ((fun a => (lam a : ℝ)) + rhoV n)) (alt (twoL lam)) χ c₁ cT hR hD hD2 hP' hχ h1 h2
  refine ⟨?_, ?_⟩
  · rw [k1, smul_mul_assoc, one_mul]
  · rw [k2, smul_mul_assoc, one_mul]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EvTSum
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem evT_sum {n : ℕ} (θ : Wt n) (c : FR n) :
    evT θ c = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by
  simp only [evT, ex, AddMonoidAlgebra.lift_single, one_smul]
  rw [AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, cf, smul_eq_mul]

theorem UpperTheory.RealTr.chEv :
    ∀ (n : ℕ) (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (σ : UK n →* (N →ₗ[ℂ] N))
      (F : Fin n → Fin n → Module.End ℂ N), UF F → IsDerivK σ F → ∀ B c, Cm F ⊤ B → IsCh F ⊤ B c → ∀ (θ : Wt n) (k : UK n),
      k.1 = diagonal (fun a => Complex.exp (Complex.I * θ a)) → LinearMap.trace ℂ N (σ k * B) = evT θ c := by
  intro n N _ _ _ σ F hF hσ B c hB hc θ k hk
  classical
  obtain ⟨s, hs0, hsup, hind⟩ := wtDec n N F hF ⊤ inferInstance (fun _ _ _ _ => Submodule.mem_top)
  set W : Wt n → Submodule ℂ N := fun μ => wsp F μ ⊓ ⊤ with hW
  have hBW : ∀ μ, ∀ v ∈ W μ, B v ∈ W μ := by
    intro μ v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨?_, Submodule.mem_top⟩
    have hv1 : IsWeight F μ v := hv.1
    show IsWeight F μ (B v)
    intro a
    have h1 := congrArg (fun T : Module.End ℂ N => T v) (hB.1 a a)
    simp only [Module.End.mul_apply] at h1
    rw [← h1, hv1 a, map_smul]
  have hσW : ∀ μ, ∀ v ∈ W μ, σ k v = evT θ (ex μ) • v := fun μ v hv =>
    (derAt n N σ F hσ).1 μ θ k v hk (Submodule.mem_inf.1 hv).1
  have hfW : ∀ μ, Set.MapsTo (σ k * B) (W μ) (W μ) := by
    intro μ v hv
    show σ k (B v) ∈ W μ
    rw [hσW μ _ (hBW μ v hv)]
    exact (W μ).smul_mem _ (hBW μ v hv)
  have hint : DirectSum.IsInternal (fun i : s => W i) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep.comp hind Subtype.val_injective
    · rw [← hsup, iSup_subtype']
  have hterm : ∀ μ, LinearMap.trace ℂ (W μ) ((σ k * B).restrict (hfW μ)) = evT θ (ex μ) * cf c μ := by
    intro μ
    have hr : (σ k * B).restrict (hfW μ) = evT θ (ex μ) • B.restrict (hBW μ) := by
      ext v
      simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Module.End.mul_apply,
        Submodule.coe_smul]
      exact hσW μ _ (hBW μ v v.2)
    rw [hr, map_smul, smul_eq_mul, hc μ]
    unfold trOn
    rw [dite_eq_left (hBW μ)]
  have hz : ∀ μ, μ ∉ s → cf c μ = 0 := by
    intro μ hμ
    rw [hc μ, hs0 μ hμ]
    unfold trOn
    split_ifs with h
    · have h0 : B.restrict h = 0 := by
        ext x
      rw [h0, map_zero]
    · rfl
  rw [LinearMap.trace_eq_sum_trace_restrict hint (fun i => hfW i)]
  simp only [hterm]
  rw [Finset.sum_coe_sort s (fun μ => evT θ (ex μ) * cf c μ)]
  calc ∑ μ ∈ s, evT θ (ex μ) * cf c μ
        = ∑ μ ∈ s ∪ c.coeff.support, evT θ (ex μ) * cf c μ := by
          apply Finset.sum_subset Finset.subset_union_left
          intro μ _ hμ
          rw [hz μ hμ, mul_zero]
    _ = ∑ μ ∈ s ∪ c.coeff.support, cf c μ * evT θ (ex μ) :=
          Finset.sum_congr rfl (fun μ _ => mul_comm _ _)
    _ = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by
          symm
          apply Finset.sum_subset Finset.subset_union_right
          intro μ _ hμ
          rw [show cf c μ = 0 from Finsupp.notMem_support_iff.1 hμ, zero_mul]
    _ = evT θ c := (evT_sum θ c).symm
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewHermitianOfUnitaryExp
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.KD

variable {n : ℕ}

private abbrev tt (n : ℕ) : Fin n → Bool := fun _ => true

private abbrev UU (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := PI.UpqRep.UJset (tt n)

private theorem jm_tt : Formalism.REAL.Jm (tt n) = 1 := by
  simp [Formalism.REAL.Jm]

private theorem mem_UU {g : Matrix (Fin n) (Fin n) ℂ} : g ∈ UU n ↔ g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show Formalism.REAL.inUJ (tt n) g ↔ _
  unfold Formalism.REAL.inUJ
  rw [jm_tt, Matrix.mul_one, Matrix.star_eq_conjTranspose]

open scoped Norms.Operator in
private theorem skew_hermitian_of_unitary_exp (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ) : Xᴴ = -X := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ∀ (t : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ), (t : ℂ) • Y = t • Y := fun t Y => by
    ext a b
    simp
  have e : ∀ t : ℝ, NormedSpace.exp (t • Xᴴ) = NormedSpace.exp (t • (-X)) := by
    intro t
    have hu := h t
    have h1 : NormedSpace.exp (t • Xᴴ) = star (NormedSpace.exp ((t : ℂ) • X)) := by
      rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul]
      simp [hsm]
    have h2 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (t • (-X)) = 1 := by
      rw [hsm, smul_neg, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right t).neg_right]
      simp
    have h3 := Unitary.star_mul_self_of_mem hu
    calc NormedSpace.exp (t • Xᴴ) = star (NormedSpace.exp ((t : ℂ) • X)) * 1 := by rw [h1, mul_one]
      _ = star (NormedSpace.exp ((t : ℂ) • X)) * (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (t • (-X))) := by
        rw [h2]
      _ = NormedSpace.exp (t • (-X)) := by rw [← mul_assoc, h3, one_mul]
  have d1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ (0 : ℝ)
  have d2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
  have hu := (d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (e t).symm)).unique d2
  simpa using hu

private theorem skew_of (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.REAL.inG (tt n) X := by
  show Xᴴ * Formalism.REAL.Jm (tt n) + Formalism.REAL.Jm (tt n) * X = 0
  rw [jm_tt, Matrix.mul_one, Matrix.one_mul, skew_hermitian_of_unitary_exp X h]
  simp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Sub

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def rs (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (W : Submodule ℂ H)
    (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) (g : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  ((σ g).comp W.subtypeL).codRestrict W (fun v => hW g v v.2)

private theorem rs_coe (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (W : Submodule ℂ H)
    (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) (g : Matrix (Fin n) (Fin n) ℂ) (v : W) :
    ((rs σ W hW g v : W) : H) = σ g v := rfl

private theorem rs_rep {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsURepOn (UU n) σ)
    (W : Submodule ℂ H) (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) : PI.UpqRep.IsURepOn (UU n) (rs σ W hW) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · ext v
    rw [rs_coe, hσ.1.1]
    rfl
  · ext v
    rw [rs_coe, hσ.1.2 a ha b hb]
    rfl
  · exact hσ.2.1 g hg (v : H)
  · exact (Topology.IsInducing.subtypeVal.continuousOn_iff).2 (hσ.2.2 (v : H))

private theorem rs_smooth {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Hm : Matrix (Fin n) (Fin n) ℂ}
    (W : Submodule ℂ H) (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) (v : W)
    (hv : v ∈ PI.PhMeasCore.smoothVecs Hm (rs σ W hW)) : (v : H) ∈ PI.PhMeasCore.smoothVecs Hm σ := by
  intro g₀ hg
  obtain ⟨U, F, hU, hg0, hF, h⟩ := hv g₀ hg
  refine ⟨U, fun g => ((F g : W) : H), hU, hg0, ?_, fun g hgU hgH => congrArg Subtype.val (h g hgU hgH)⟩
  exact (W.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF

private theorem inner_rep {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsURepOn (UU n) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UU n) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), fun v => hσ.2.1 g hg v⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

private theorem orth_stable {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsURepOn (UU n) σ)
    (hz : ∀ g, g ∉ UU n → σ g = 0) {S : Submodule ℂ H} (hS : ∀ g ∈ UU n, ∀ v ∈ S, σ g v ∈ S) :
    ∀ g, ∀ v ∈ Sᗮ, σ g v ∈ Sᗮ := by
  intro g v hv
  by_cases hg : g ∈ UU n
  · have hg' := mem_UU.1 hg
    have hs : star g ∈ UU n := mem_UU.2 (Unitary.star_mem hg')
    rw [Submodule.mem_orthogonal]
    intro s hs'
    have h1 : σ (star g) (σ g v) = v := by
      have := hσ.1.2 _ hs _ hg
      rw [Unitary.star_mul_self_of_mem hg', hσ.1.1] at this
      exact (congrArg (fun T : H →L[ℂ] H => T v) this).symm
    rw [← inner_rep hσ hs, h1]
    exact (Submodule.mem_orthogonal _ _).1 hv _ (hS _ hs _ hs')
  · rw [hz g hg]
    exact Sᗮ.zero_mem

private theorem top_of [FiniteDimensional ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsURepOn (UU n) σ) (hz : ∀ g, g ∉ UU n → σ g = 0) {S : Submodule ℂ H}
    (hS : ∀ g ∈ UU n, ∀ v ∈ S, σ g v ∈ S)
    (hmem : ∀ v, v ∈ S ↔ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (tt n)) σ) : S = ⊤ := by
  by_contra hne
  have hT : Sᗮ ≠ ⊥ := fun h => hne ((Submodule.orthogonal_eq_bot_iff).1 h)
  obtain ⟨W, ⟨hW0, hWT, hWs⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ H)).has_min
    {W | W ≠ ⊥ ∧ W ≤ Sᗮ ∧ ∀ g, ∀ v ∈ W, σ g v ∈ W} ⟨Sᗮ, hT, le_rfl, orth_stable hσ hz hS⟩
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hirr : PI.UpqRep.IsIrredOn (UU n) (rs σ W hWs) := by
    intro S' _ hS'
    by_cases h0 : S' = ⊥
    · exact Or.inl h0
    refine Or.inr ?_
    have hle : S'.map W.subtype ≤ W := Submodule.map_subtype_le W S'
    have hst : ∀ g, ∀ v ∈ S'.map W.subtype, σ g v ∈ S'.map W.subtype := by
      intro g v hv
      by_cases hg : g ∈ UU n
      · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
        exact Submodule.mem_map.2 ⟨_, hS' g hg x hx, rfl⟩
      · rw [hz g hg]
        exact Submodule.zero_mem _
    have hne' : S'.map W.subtype ≠ ⊥ := fun h => h0 (Submodule.map_injective_of_injective W.injective_subtype (h.trans (Submodule.map_bot _).symm))
    have heq : S'.map W.subtype = W := by
      by_contra hc
      exact hmin _ ⟨hne', hle.trans hWT, hst⟩ (lt_of_le_of_ne hle hc)
    rw [eq_top_iff]
    intro w _
    have : (w : H) ∈ S'.map W.subtype := by
      rw [heq]
      exact w.2
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.1 this
    rwa [← Subtype.ext hxw]
  have hWS : W ≤ S := by
    intro v hv
    refine (hmem v).2 (rs_smooth W hWs ⟨v, hv⟩ ?_)
    exact CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n (tt n) W (rs σ W hWs) (rs_rep hσ W hWs) hirr ⟨v, hv⟩
      ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  apply hW0
  rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot S]
  exact le_inf hWS hWT

end Sub

private def sgm (E : KMod n) (g : Matrix (Fin n) (Fin n) ℂ) : E.V →L[ℂ] E.V := by
  classical exact if h : g ∈ Matrix.unitaryGroup (Fin n) ℂ then E.ρ ⟨g, h⟩ else 0

private theorem sgm_coe (E : KMod n) (k : UK n) : sgm E k.1 = E.ρ k := by
  simp only [sgm]
  rw [dite_eq_left k.2]

private theorem sgm_zero (E : KMod n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∉ UU n) : sgm E g = 0 := by
  simp only [sgm]
  rw [dite_eq_right (fun h => hg (mem_UU.2 h))]

private theorem sgm_rep (E : KMod n) : PI.UpqRep.IsURepOn (UU n) (sgm E) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · exact (sgm_coe E 1).trans (map_one E.ρ)
  · have ha' := mem_UU.1 ha
    have hb' := mem_UU.1 hb
    have h := sgm_coe E (⟨a, ha'⟩ * ⟨b, hb'⟩)
    rw [map_mul, ← sgm_coe E ⟨a, ha'⟩, ← sgm_coe E ⟨b, hb'⟩] at h
    exact h
  · rw [show sgm E g = E.ρ ⟨g, mem_UU.1 hg⟩ from sgm_coe E ⟨g, mem_UU.1 hg⟩]
    exact E.iso _ v
  · rw [continuousOn_iff_continuous_restrict]
    have e : (fun u : UU n => sgm E u.1 v) = fun u : UU n => E.ρ ⟨u.1, mem_UU.1 u.2⟩ v := by
      funext u
      exact congrArg (fun T : E.V →L[ℂ] E.V => T v) (sgm_coe E ⟨u.1, mem_UU.1 u.2⟩)
    show Continuous (fun u : UU n => sgm E u.1 v)
    rw [e]
    exact (E.cont.comp (Continuous.subtype_mk continuous_subtype_val _)).clm_apply continuous_const

end UpperTheory.RealTr.KD

open UpperTheory.RealTr.KD in
theorem UpperTheory.RealTr.kDer :
    ∀ (n : ℕ) (E : KMod n), ∃ (σ : UK n →* (E.V →ₗ[ℂ] E.V)) (F : Fin n → Fin n → Module.End ℂ E.V), (∀ k v, σ k v = E.ρ k v) ∧ UF F ∧ IsDerivK σ F := by
  intro n E
  obtain ⟨S, F, hM⟩ := GlobalTheory.CompanionTheory.TransS.InfChar.hSmMod n (tt n) E.V (sgm E) (sgm_rep E)
  obtain rfl : S = ⊤ := top_of (sgm_rep E) (fun g hg => sgm_zero E hg) (fun g hg v hv => hM.stab g hg v hv) hM.mem
  let σ' : UK n →* (E.V →ₗ[ℂ] E.V) :=
    { toFun := fun k => (E.ρ k : E.V →ₗ[ℂ] E.V)
      map_one' := by ext v; simp
      map_mul' := fun a b => by ext v; simp }
  let F' : Fin n → Fin n → Module.End ℂ E.V := fun a b =>
    (⊤ : Submodule ℂ E.V).subtype ∘ₗ F a b ∘ₗ LinearMap.codRestrict ⊤ LinearMap.id (fun _ => trivial)
  have hF' : ∀ a b x, F' a b x = ((F a b ⟨x, trivial⟩ : (⊤ : Submodule ℂ E.V)) : E.V) := fun _ _ _ => rfl
  refine ⟨σ', F', fun _ _ => rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b c d
    ext x
    have h := congrArg (fun T : Module.End ℂ (⊤ : Submodule ℂ E.V) => ((T ⟨x, trivial⟩ : (⊤ : Submodule ℂ E.V)) : E.V)) (hM.gl a b c d)
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simpa [h1, h2, hF', Module.End.mul_apply] using h
  · intro a b x y
    have h := hM.unit a b ⟨x, trivial⟩ ⟨y, trivial⟩
    simpa [Formalism.REAL.sgn, hF'] using h
  · intro k x y
    exact (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V).inner_map_map x y
  · intro v
    refine ⟨⊤, inferInstance, trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial, ?_⟩
    intro X γ hγ w _
    have hX : Formalism.REAL.inG (tt n) X := skew_of X (fun t => by rw [← hγ t]; exact (γ t).2)
    have h := hM.real X hX ⟨w, trivial⟩
    have e : (fun t : ℝ => σ' (γ t) w) = fun t : ℝ => sgm E (NormedSpace.exp ((t : ℂ) • X)) w := by
      funext t
      rw [← hγ t, sgm_coe]
      rfl
    rw [e]
    exact h
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DualEx
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

private def eD : (V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ V i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp
  invFun y := ∑ i, y i • innerSL ℂ (stdOrthonormalBasis ℂ V i)
  left_inv ξ := by
    ext v
    have h := (stdOrthonormalBasis ℂ V).sum_repr' v
    conv_rhs => rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [sum_apply, map_sum, mul_comm]
  right_inv y := by
    ext j
    simp [sum_apply, OrthonormalBasis.inner_eq_ite]

private theorem eD_apply (ξ : V →L[ℂ] ℂ) (i) : eD ξ i = ξ (stdOrthonormalBasis ℂ V i) := rfl

private theorem norm_eD (ξ : V →L[ℂ] ℂ) : ‖eD ξ‖ = ‖ξ‖ := by
  set b := stdOrthonormalBasis ℂ V
  set u := (InnerProductSpace.toDual ℂ V).symm ξ
  have hu : ∀ v, ξ v = ⟪u, v⟫_ℂ := fun v => (InnerProductSpace.toDual_symm_apply).symm
  rw [← (InnerProductSpace.toDual ℂ V).symm.norm_map ξ, ← b.repr.norm_map u,
    EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eD_apply, hu, b.repr_apply_apply, ← inner_conj_symm, Complex.norm_conj]

private def pr (A : V →L[ℂ] V) :
    EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  ((eD (V := V)).toContinuousLinearEquiv : (V →L[ℂ] ℂ) →L[ℂ] _).comp
    (((ContinuousLinearMap.compL ℂ V V ℂ).flip A).comp
      ((eD (V := V)).toContinuousLinearEquiv.symm : _ →L[ℂ] (V →L[ℂ] ℂ)))

private theorem pr_apply (A : V →L[ℂ] V) (y) : pr A y = eD ((eD.symm y).comp A) := rfl

private theorem pr_eD (A : V →L[ℂ] V) (ξ : V →L[ℂ] ℂ) : pr A (eD ξ) = eD (ξ.comp A) := by
  rw [pr_apply, LinearEquiv.symm_apply_apply]

private theorem pr_one : pr (1 : V →L[ℂ] V) = 1 := by
  ext1 y
  rw [pr_apply, one_apply_eq_self]
  show eD ((eD.symm y).comp (ContinuousLinearMap.id ℂ V)) = y
  rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]

private theorem pr_mul (A B : V →L[ℂ] V) : pr (A * B) = pr B * pr A := by
  ext1 y
  rw [mul_apply_eq_comp, pr_apply, pr_apply, pr_apply, LinearEquiv.symm_apply_apply,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

private theorem continuous_pr : Continuous (pr (V := V)) := by
  unfold pr
  fun_prop

private theorem trace_pr (A : V →L[ℂ] V) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)))
      ((pr A : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
        EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) =
      LinearMap.trace ℂ V (A : V →ₗ[ℂ] V) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin (Module.finrank ℂ V)) ℂ).toBasis,
    LinearMap.trace_eq_matrix_trace ℂ (stdOrthonormalBasis ℂ V).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, pr_apply]
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, eD_apply, ContinuousLinearMap.comp_apply]
  show (∑ j, (EuclideanSpace.single i (1 : ℂ)) j • innerSL ℂ (stdOrthonormalBasis ℂ V j))
    (A (stdOrthonormalBasis ℂ V i)) = _
  simp [PiLp.single_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.dualEx :
    ∀ (n : ℕ) (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∃ (E' : KMod n) (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] E'.V) (T' : Module.End ℂ E'.V),
      (∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = E'.ρ k (e ξ)) ∧ (∀ ξ, e (dualT E T ξ) = T' (e ξ)) ∧
      ∀ k, LinearMap.trace ℂ E'.V (E'.ρ k : E'.V →ₗ[ℂ] E'.V) = LinearMap.trace ℂ E.V (E.ρ k⁻¹ : E.V →ₗ[ℂ] E.V) ∧
        LinearMap.trace ℂ E'.V ((E'.ρ k : E'.V →ₗ[ℂ] E'.V) * T') = LinearMap.trace ℂ E.V ((E.ρ k⁻¹ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  intro n E T hT
  have hnorm : ∀ (k : UK n) (ξ : E.V →L[ℂ] ℂ), ‖ξ.comp (E.ρ k)‖ ≤ ‖ξ‖ := by
    intro k ξ
    have hk : ‖E.ρ k‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [E.iso, one_mul]
    calc ‖ξ.comp (E.ρ k)‖ ≤ ‖ξ‖ * ‖E.ρ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ = ‖ξ‖ := mul_one _
  have hinv : Continuous (fun k : UK n => k⁻¹) := by
    exact continuous_inv
  let ρ' : UK n →* (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => pr (E.ρ k⁻¹)
      map_one' := by simp [pr_one]
      map_mul' := by
        intro k l
        simp only [_root_.mul_inv_rev, map_mul, pr_mul] }
  let E' : KMod n :=
    { V := EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))
      ρ := ρ'
      iso := by
        intro k y
        obtain ⟨ξ, rfl⟩ := eD.surjective y
        show ‖pr (E.ρ k⁻¹) (eD ξ)‖ = ‖eD ξ‖
        rw [pr_eD, norm_eD, norm_eD]
        apply le_antisymm (hnorm _ ξ)
        calc ‖ξ‖ = ‖(ξ.comp (E.ρ k⁻¹)).comp (E.ρ k)‖ := by
              rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, ← map_mul, inv_mul_cancel,
                map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
          _ ≤ ‖ξ.comp (E.ρ k⁻¹)‖ := hnorm _ _
      cont := continuous_pr.comp (E.cont.comp hinv) }
  refine ⟨E', eD, (pr T : E'.V →L[ℂ] E'.V), ?_, ?_, ?_⟩
  · intro k ξ
    exact (pr_eD _ ξ).symm
  · intro ξ
    exact (pr_eD T ξ).symm
  · intro k
    constructor
    · exact trace_pr (E.ρ k⁻¹)
    · show LinearMap.trace ℂ _ ((pr (E.ρ k⁻¹) : E'.V →ₗ[ℂ] E'.V) * (pr T : E'.V →ₗ[ℂ] E'.V)) = _
      rw [← ContinuousLinearMap.toLinearMap_mul, ← pr_mul, trace_pr, hT]
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trOn_top_one {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] : trOn S (1 : Module.End ℂ V) = (Module.finrank ℂ S : ℂ) := by
  unfold trOn
  rw [dite_eq_left (fun x hx => by simpa using hx)]
  have : (LinearMap.restrict (1 : Module.End ℂ V) (fun x hx => by simpa using hx) : Module.End ℂ S) = 1 := by
    ext x
    rfl
  rw [this, LinearMap.trace_one]

private theorem prod_swap {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a * conj (z a) = 1) :
    (∏ a, ∏ b, (1 + conj (z a) / conj (z b))) = ∏ a, ∏ b, (1 + z a / z b) := by
  have hne : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  have hc : ∀ a, conj (z a) = (z a)⁻¹ := fun a => (eq_inv_of_mul_eq_one_right (hz a))
  have key : ∀ a b, conj (z a) / conj (z b) = z b / z a := by
    intro a b
    rw [hc, hc]
    field_simp [hne a, hne b]
  simp_rw [key]
  exact Finset.prod_comm

theorem UpperTheory.RealTr.lefData :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
      ∃ (E' : KMod n) (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] E'.V) (T' : Module.End ℂ E'.V) (σ' : UK n →* (E'.V →ₗ[ℂ] E'.V)) (F : Fin n → Fin n → Module.End ℂ E'.V)
        (χ : FR n) (s : Finset (Wt n)), (∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = σ' k (e ξ)) ∧ (∀ ξ, e (dualT E T ξ) = T' (e ξ)) ∧ UF F ∧ IsDerivK σ' F ∧
        (∀ a b, T' * F a b = F a b * T') ∧ (∀ ν ∉ s, hw F ν = ⊥) ∧ alt (rhoV n) * χ = alt ((fun a => (lam a : ℝ)) + rhoV n) ∧
        ∀ ν : Wt n, StrictAnti (ν + rhoV n) → trOn (hw F ν) T' = 2 ^ n * cf (chR n * alt (twoL lam)) (ν + rhoV n) ∧
          (Module.finrank ℂ (hw F ν) : ℂ) = 2 ^ n * cf (chR n * (alt ((2 : ℝ) • rhoV n) * (χ * χ))) (ν + rhoV n) := by
  intro n lam hlam E T hL
  obtain ⟨hcomm, hTT, htrace⟩ := hL
  obtain ⟨E', e, T', he1, he2, he3⟩ := dualEx n E T hcomm
  obtain ⟨σ', F, hσ, hUF, hder⟩ := kDer n E'
  have hTρ : ∀ (k : UK n) (v : E'.V), T' (E'.ρ k v) = E'.ρ k (T' v) := by
    intro k v
    obtain ⟨ξ, rfl⟩ := e.surjective v
    rw [← he1, ← he2, ← he2, ← he1]
    congr 1
    ext x
    have hx := congrArg (fun f : E.V →L[ℂ] E.V => f x) (hcomm k⁻¹)
    simp only [ContinuousLinearMap.mul_apply] at hx
    show ξ (E.ρ k⁻¹ (T x)) = ξ (T (E.ρ k⁻¹ x))
    rw [hx]
  have hTF : ∀ a b, T' * F a b = F a b * T' := by
    have hmem : T' ∈ homL F F := by
      refine ((derAt n E'.V σ' F hder).2 E'.V σ' F hder T').1 ?_
      intro k x
      rw [hσ, hσ]
      exact hTρ k x
    intro a b
    ext x
    exact hmem a b x
  have hDom : Dom (fun a => (lam a : ℝ)) := by
    intro a b hab
    have hle := hlam hab.le
    refine ⟨(lam a - lam b).toNat, ?_⟩
    have h0 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have h1 : (((lam a - lam b).toNat : ℕ) : ℝ) = ((lam a - lam b : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1]
    push_cast
    ring
  obtain ⟨χ, -, hχ⟩ := divEx n _ hDom
  have hStop : Stb F (⊤ : Submodule ℂ E'.V) := fun a b x _ => trivial
  obtain ⟨s, hs, -, -⟩ := wtDec n E'.V F hUF ⊤ inferInstance hStop
  have hCm1 : Cm F ⊤ (1 : Module.End ℂ E'.V) :=
    ⟨fun a b => by rw [one_mul, mul_one], fun x _ => trivial⟩
  have hCmT : Cm F ⊤ T' := ⟨hTF, fun x _ => trivial⟩
  obtain ⟨c₁, hc₁⟩ := chEx n E'.V F hUF ⊤ inferInstance hStop 1
  obtain ⟨cT, hcT⟩ := chEx n E'.V F hUF ⊤ inferInstance hStop T'
  have hkey : ∀ (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * (θ a : ℂ))) →
      (Function.Injective fun a => z a ^ 2) →
      evT θ c₁ = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2 ∧
      evT θ cT = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
    intro θ z hz hinj
    have hzn : ∀ a, z a * conj (z a) = 1 := by
      intro a
      rw [Complex.mul_conj, hz a, Complex.normSq_eq_norm_sq, mul_comm, Complex.norm_exp_ofReal_mul_I]
      simp
    have hmemU : diagonal z ∈ unitaryGroup (Fin n) ℂ := by
      rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext a
      exact hzn a
    set k : UK n := ⟨diagonal z, hmemU⟩ with hkdef
    have hk : (k : Matrix (Fin n) (Fin n) ℂ) = diagonal fun a => Complex.exp (Complex.I * (θ a : ℂ)) := by
      show diagonal z = _
      congr 1
      funext a
      exact hz a
    have hkinv : ((k⁻¹ : UK n) : Matrix (Fin n) (Fin n) ℂ) = diagonal fun a => conj (z a) := by
      rw [UnitaryGroup.inv_val]
      show star (diagonal z) = _
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      rfl
    have hinj' : Function.Injective fun a => conj (z a) ^ 2 := by
      intro a b h
      apply hinj
      have h' := congrArg conj h
      simpa [map_pow] using h'
    have hσk : (σ' k : Module.End ℂ E'.V) = ((E'.ρ k : E'.V →L[ℂ] E'.V) : Module.End ℂ E'.V) := by
      ext v
      exact hσ k v
    have hw := (weylEv n lam θ z hz).2.2.2
    obtain ⟨t1, t2⟩ := htrace k⁻¹ (fun a => conj (z a)) hkinv hinj'
    constructor
    · rw [← chEv n E'.V σ' F hUF hder 1 c₁ hCm1 hc₁ θ k hk, mul_one, hσk, (he3 k).1, t1,
        prod_swap z hzn, hw z]
    · rw [← chEv n E'.V σ' F hUF hder T' cT hCmT hcT θ k hk, hσk, (he3 k).2, t2,
        prod_swap z hzn]
      have : (fun a => conj (z a) ^ 2) = fun a => conj (z a ^ 2) := by
        funext a
        rw [map_pow]
      rw [this, hw (fun a => z a ^ 2)]
  obtain ⟨hT, h1⟩ := lefForm n lam c₁ cT χ hχ hkey
  refine ⟨E', e, T', σ', F, χ, s, ?_, he2, hUF, hder, hTF, ?_, hχ, ?_⟩
  · intro k ξ
    rw [he1, hσ]
  · intro ν hν
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ wsp F ν ⊓ ⊤ := ⟨hx.1, trivial⟩
    rw [hs ν hν] at hx'
    exact hx'
  · intro ν hν
    have mT := mult n E'.V F hUF ⊤ inferInstance hStop T' cT hCmT hcT ν hν
    have m1 := mult n E'.V F hUF ⊤ inferInstance hStop 1 c₁ hCm1 hc₁ ν hν
    rw [inf_top_eq] at mT m1
    rw [hT] at mT
    rw [h1] at m1
    constructor
    · rw [← mT]
      simp [cf]
    · rw [← trOn_top_one, ← m1]
      simp [cf]

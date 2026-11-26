module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimplePotentialsAtNewformEigensystem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepresentationOfEigensystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentials
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruence
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KZero

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected

theorem eventually_ne_zero {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb0 : (b : Mero) ≠ 0) :
    ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
  have hA : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs
  obtain ⟨z0, hz0, hbz0⟩ : ∃ z0 ∈ Hs, b z0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb0 (Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) h))
  have h0 : analyticOrderAt b z0 ≠ ⊤ := by
    rw [(hA z0 hz0).analyticOrderAt_eq_zero.2 hbz0]; exact ENat.zero_ne_top
  filter_upwards [hA.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top,
    Filter.self_mem_codiscreteWithin Hs] with z hz hzH
  rcases hz with hz | hz
  · exact (hA z hzH).analyticOrderAt_eq_zero.1 hz
  · exact absurd hz (hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_Hs hz0 hzH h0)

theorem cast_of_mul {M M' : ℕ} {x : ℤ} {y : ℤ} (h : (x : ZMod (M * M')) = y) : (x : ZMod M) = y := by
  have := congrArg (ZMod.castHom (dvd_mul_right M M') (ZMod M)) h
  simpa using this

theorem gamma_mul_le {M M' : ℕ} : CongruenceSubgroup.Gamma (M * M') ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast cast_of_mul (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast cast_of_mul (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast cast_of_mul (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast cast_of_mul (y := 1) (by exact_mod_cast h4)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_pow_eq_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (G : X.Kˣ) : X.cls l n (G ^ (l ^ n)) = 0 := by
  rw [Tower.cls, Submodule.Quotient.mk_eq_zero, ofMul_pow]
  have e : (1 : ℤ_[l]) ⊗ₜ[ℤ] ((l ^ n) • Additive.ofMul G) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul G) := by
    rw [← natCast_zsmul, TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast
    rfl
  rw [e]
  have hl : (l : ℤ_[l]) ∈ idl l := Ideal.subset_span (Set.mem_singleton _)
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top

end GlobalTheory.KZ.H3.KZero

namespace GlobalTheory.KZ.H3


open KZero in
theorem kum_near_zero_eval : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  intro Ω _ _ ε X l _ n x χ hK hN
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hroot⟩, hχ⟩ := hK
  obtain ⟨M', hM', hz⟩ := hN
  have hmpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hne := eventually_ne_zero hb hb0
  obtain ⟨φ, hφ⟩ := Quot.exists_rep (X.an (f : X.K))
  have hφ' : X.an (f : X.K) = (φ : Mero) := hφ.symm
  rw [hφ', ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hroot

  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma (M * M'),
      ((fun z => a (mob (ofSL γ) z) * b z : ℂ → ℂ) : Mero) = ((fun z => a z * b (mob (ofSL γ) z) : ℂ → ℂ) : Mero) := by
    intro γ hγ
    have h1 : γ ∈ CongruenceSubgroup.Gamma M := gamma_mul_le hγ
    have h2 : γ ∈ CongruenceSubgroup.Gamma M' := gamma_mul_le (M := M') (M' := M) (by rw [mul_comm]; exact hγ)
    refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz' => ?_)
    have := hχ γ h1 z hz'
    rw [hz γ h2] at this
    simpa using this

  have hP : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ (l ^ n) - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hmpos _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ', sub_eq_zero, ← Filter.Germ.coe_pow,
      Filter.Germ.coe_eq]
    filter_upwards [hroot, hne] with z h1 h2
    simp only [Pi.pow_apply, Pi.div_apply, Pi.mul_apply] at h1 ⊢
    rw [div_pow, ← h1]
    field_simp
  obtain ⟨g, hg⟩ := X.sat a b (M * M') (Nat.mul_pos hM hM') ha hb hb0 hlev hP
  obtain ⟨ψ, hψ⟩ := Quot.exists_rep (X.an g)
  have hψ' : X.an g = (ψ : Mero) := hψ.symm
  rw [hψ', ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hg
  haveI : Nontrivial Mero := ⟨⟨(b : Mero), 0, hb0⟩⟩
  have hgm : g ^ (l ^ n) = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ', hφ', ← Filter.Germ.coe_pow, Filter.Germ.coe_eq]
    filter_upwards [hroot, hg, hne] with z h1 h2 h3
    simp only [Pi.pow_apply, Pi.mul_apply] at h1 h2 ⊢
    have h4 : ψ z ^ (l ^ n) * b z ^ (l ^ n) = φ z * b z ^ (l ^ n) := by rw [← mul_pow, h2, h1]
    exact mul_right_cancel₀ (pow_ne_zero _ h3) h4
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hmpos.ne'] at hgm
    exact f.ne_zero hgm.symm
  have hfG : f = (Units.mk0 g hg0) ^ (l ^ n) := by
    ext; simp [hgm]
  rw [hx, hfG]
  exact cls_pow_eq_zero X l n _

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruenceStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  first | exact @GlobalTheory.KZ.H3.kum_near_zero_eval | exact GlobalTheory.KZ.H3.kum_near_zero_eval | (intros; apply GlobalTheory.KZ.H3.kum_near_zero_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZero
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem relTriv_gamma_of_dvd {N M : ℕ} (h : N ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem toZModPow_eval_mulVec {l : ℕ} [Fact l.Prime] (n : ℕ) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) (q : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval
      (((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℤ_[l]) *ᵥ u) q) =
      PadicInt.toZModPow n (MvPolynomial.eval u q) := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  obtain ⟨a, b, c, d⟩ := hδ
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval]
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  have e : ∀ x : ℤ, PadicInt.toZModPow n ((x : ℤ_[l])) = (x : ZMod (l ^ n)) := fun x => map_intCast _ x
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e, a, b, c, d]

theorem rel_triv_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ →
      ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  intro Ω _ _ ε X l _ w Γ M₀ hM₀ hΓ b F hR hF
  obtain ⟨ψ, p, hψ, hFψ⟩ := hF
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, hK, M₁, hM₁, hχ⟩ := hR u n
  change AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n ((0 : X.Fn l) u)
  rw [Pi.zero_apply, map_zero]
  refine GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence Ω ε X l n (b u) χ hK ⟨M₁ * M₀ * l ^ n, ?_, fun δ hδ => ?_⟩
  · have : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    positivity
  have h1 : δ ∈ CongruenceSubgroup.Gamma M₁ := relTriv_gamma_of_dvd ⟨M₀ * l ^ n, by ring⟩ hδ
  have h0 : δ ∈ Γ := hΓ (relTriv_gamma_of_dvd ⟨M₁ * l ^ n, by ring⟩ hδ)
  have hl : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := relTriv_gamma_of_dvd ⟨M₁ * M₀, by ring⟩ hδ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hδI : mob (ofSL δ) Complex.I ∈ Hs := (GlobalTheory.T.glTwoPosRatMobius_basic_laws).1 _ _ hI
  have key := hχ δ h1 Complex.I hI
  beta_reduce at key
  rw [← key, hFψ _ hδI, hFψ _ hI, ← hψ δ h0 Complex.I hI]
  simp only [map_add (f := _), GlobalTheory.KZ.Betti.eval_slP, add_sub_add_right_eq_sub, map_sub,
    toZModPow_eval_mulVec n hl, sub_self, Pi.zero_apply]

end GlobalTheory.KZ.H3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZeroStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  first | exact @GlobalTheory.KZ.H3.rel_triv_eq_zero | exact GlobalTheory.KZ.H3.rel_triv_eq_zero | (intros; apply GlobalTheory.KZ.H3.rel_triv_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishes
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.LamZero

theorem map_slP {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (Q : MvPolynomial (Fin 2) R) : MvPolynomial.map f (slP m Q) = slP m (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_coef_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (Q : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (c • Q) = f c • MvPolynomial.map f Q := by
  simp [MvPolynomial.smul_eq_C_mul]

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

theorem eq_zero_of_sum {k : ℕ} {v : Fin k → E} (hv : LinearIndependent ℤ_[l] v)
    (Q : Fin k → MvPolynomial (Fin 2) ℤ_[l])
    (h : ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) = 0) (a : Fin k) : Q a = 0 := by
  ext m
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
    smul_eq_mul] at h1
  have := Fintype.linearIndependent_iff.1 hv (fun a => AddMonoidAlgebra.coeff (Q a) m) (by
    simpa [Algebra.smul_def, mul_comm] using h1)
  simpa using this a

theorem exists_basis (hinj : Function.Injective (algebraMap ℤ_[l] E)) (S : Finset E) :
    ∃ (k : ℕ) (v : Fin k → E) (r : E → Fin k → ℤ_[l]), LinearIndependent ℤ_[l] v ∧
      ∀ x ∈ S, x = ∑ a, r x a • v a := by
  classical
  let L := Submodule.span ℤ_[l] (S : Set E)
  haveI : Module.Finite ℤ_[l] L := Module.Finite.span_finset _ _
  haveI : NoZeroSMulDivisors ℤ_[l] E := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h⟩
  haveI : Module.Free ℤ_[l] L := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] L
  refine ⟨_, fun a => (b a : E), fun x => if h : x ∈ L then b.repr ⟨x, h⟩ else 0, ?_, ?_⟩
  · exact b.linearIndependent.map' L.subtype (by simp)
  · intro x hx
    have hxL : x ∈ L := Submodule.subset_span hx
    have h2 : ((∑ i, (b.repr ⟨x, hxL⟩) i • b i : L) : E) = x := congrArg Subtype.val (b.sum_repr _)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    simp only [dif_pos hxL]
    exact h2.symm

theorem poly_decomp {k : ℕ} (v : Fin k → E) (r : E → Fin k → ℤ_[l]) (P : MvPolynomial (Fin 2) E)
    (hr : ∀ m ∈ P.support, P.coeff m = ∑ a, r (P.coeff m) a • v a) :
    ∃ Q : Fin k → MvPolynomial (Fin 2) ℤ_[l], P = ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) := by
  classical
  refine ⟨fun a => ∑ m ∈ P.support, MvPolynomial.monomial m (r (P.coeff m) a), ?_⟩
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial,
    smul_eq_mul, map_sum]
  by_cases hn : n ∈ P.support
  · simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_pos hn]
    refine (hr n hn).trans ?_
    simp [Algebra.smul_def, mul_comm]
  · rw [MvPolynomial.notMem_support_iff.1 hn]
    simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_neg hn, mul_zero,
      Finset.sum_const_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

theorem sum_reorg {n k : ℕ} (f : Fin n → E) (v : Fin k → E) (c : Fin n → Fin k → ℤ_[l])
    (hf : ∀ i, f i = ∑ a, c i a • v a) (F : Fin n → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (∑ i, c i a • F i) =
      ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_coef_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf i, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Algebra.smul_def]
  exact mul_comm _ _

theorem sum_slP {k : ℕ} (v : Fin k → E) (m : Matrix (Fin 2) (Fin 2) ℤ) (A B : Fin k → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (slP m (A a) - B a) =
      slP m (∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (A a)) -
        ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (B a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, RingHom.map_sub, map_slP, smul_sub]

theorem tmul_sum_zero {M : Type} [AddCommGroup M] [Module ℤ_[l] M] {n k : ℕ} (f : Fin n → E) (v : Fin k → E)
    (c : Fin n → Fin k → ℤ_[l]) (hf : ∀ i, f i = ∑ a, c i a • v a) (b : Fin n → M)
    (hb : ∀ a, ∑ i, c i a • b i = 0) : ∑ i, f i ⊗ₜ[ℤ_[l]] b i = 0 := by
  have : ∀ i, f i ⊗ₜ[ℤ_[l]] b i = ∑ a, v a ⊗ₜ[ℤ_[l]] (c i a • b i) := by
    intro i
    rw [hf i, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← TensorProduct.tmul_sum, hb a, TensorProduct.tmul_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem rel_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n : ℕ} (b : Fin n → X.Fn l)
    (F : Fin n → ℂ → MvPolynomial (Fin 2) ℤ_[l]) (hR : ∀ j, Rel X l (b j) (F j)) (c : Fin n → ℤ_[l]) :
    Rel X l (∑ j, c j • b j) (∑ j, c j • F j) := by
  obtain ⟨hadd, hzero, hsmul, -, -⟩ := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have : ∀ s : Finset (Fin n), Rel X l (∑ j ∈ s, c j • b j) (∑ j ∈ s, c j • F j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact hadd _ _ _ _ (hsmul _ _ _ (hR j)) ih
  exact this Finset.univ

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3


open LamZero in
theorem lam_fst_eq_zero_of_triv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  intro Ω _ _ ε X l _ E _ _ hinj w Γ M₀ hM₀ hΓ p hp hT
  classical
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hp
  choose b F hRel hg using fun i => (g i).2
  obtain ⟨ψ, P, hψ, hP⟩ := hT
  obtain ⟨k, v, r, hv, hr⟩ := exists_basis hinj (Finset.univ.image f ∪ P.support.image (fun m => P.coeff m))
  have hf : ∀ i, f i = ∑ a, r (f i) a • v a := fun i =>
    hr _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  obtain ⟨Q, hQ⟩ := poly_decomp v r P (fun m hm =>
    hr _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)))
  let c : Fin n → Fin k → ℤ_[l] := fun i a => r (f i) a
  let G : Fin k → ℂ → MvPolynomial (Fin 2) ℤ_[l] := fun a z => ∑ i, c i a • F i z
  have hp1 : p.1 = ∑ i, f i ⊗ₜ[ℤ_[l]] b i := by
    rw [← hfg]
    simp [Prod.fst_sum, hg, TensorProduct.smul_tmul']
  have hp2 : ∀ z, p.2 z = ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i z) := by
    intro z
    rw [← hfg]
    simp [Prod.snd_sum, Finset.sum_apply, hg]
  have hkey : ∀ z, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a z) = p.2 z := fun z =>
    (sum_reorg f v c hf (fun i => F i z)).trans (hp2 z).symm
  have e1 : ∀ y, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a y - Q a) = p.2 y - P := by
    intro y
    simp only [RingHom.map_sub, smul_sub, Finset.sum_sub_distrib, hkey, ← hQ]
  have hGT : ∀ a, (fun z => G a z) ∈ Triv ℤ_[l] w Γ := by
    intro a
    refine ⟨fun z => G a z - Q a, Q a, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have hγz : mob (ofSL γ) z ∈ Hs := GlobalTheory.KZ.MobLaws.mob_mem _ hz
    have h0 := eq_zero_of_sum hv (fun a => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (G a (mob (ofSL γ) z) - Q a) -
      (G a z - Q a)) (by
        rw [sum_slP, e1, e1, hP _ hγz, hP _ hz, add_sub_cancel_right, add_sub_cancel_right, hψ γ hγ z hz, sub_self]) a
    exact sub_eq_zero.1 h0
  have hb : ∀ a, ∑ i, c i a • b i = 0 := by
    intro a
    have hR := rel_sum X l b F hRel (fun i => c i a)
    have hG : (∑ i, c i a • F i) = fun z => G a z := by
      funext z; simp [G, Finset.sum_apply]
    rw [hG] at hR
    exact GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero Ω ε X l w Γ M₀ hM₀ hΓ _ _ hR (hGT a)
  rw [hp1]
  exact tmul_sum_zero f v c hf b hb

end GlobalTheory.KZ.H3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishesStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_eigenvalue_congruence_vanishes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  first | exact @GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivial
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3.LamInj

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] [CharZero E] :
    Function.Injective (algebraMap ℤ_[l] E) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have e := PadicInt.unitCoeff_spec h0
  rw [e, map_mul, map_pow, map_natCast] at hx
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[l] E)).ne_zero h
  · exact pow_ne_zero _ hl h

theorem gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem gamma_le_gam (N l : ℕ) : CongruenceSubgroup.Gamma (N * l) ≤ Gam N l := by
  intro δ hδ
  have h1 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro l rfl : N ∣ N * l) hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro_left N rfl : l ∣ N * l) hδ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩

theorem fst_eq_zero_of_triv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E →
    ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) →
    y = 0 := by
  intro Ω _ _ _ ε X _ _ N l w _ hN E _ _ hE y G hp hG
  exact GlobalTheory.T.trivial_eigenvalue_congruence_vanishes Ω ε X l E (algebraMap_injective l E) w (Gam N l) (N * l)
    (Nat.mul_pos hN (Fact.out : l.Prime).pos) (gamma_le_gam N l) (y, G) hp hG

end GlobalTheory.KZ.H3.LamInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivialStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E → ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) → y = 0 := by
  first | exact @GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStable
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.H3.LamStab

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, Betti.slP_X, map_add (f := _), map_smul]
    simp [MvPolynomial.smul_eq_C_mul]

theorem opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opP S m (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opP R m F z) := by
  funext z
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, polySlash_map]

theorem sum_opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} (s : Finset ι)
    (m : ι → Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    (∑ j ∈ s, opP S (m j)) (fun z => MvPolynomial.map φ (F z)) =
      fun z => MvPolynomial.map φ ((∑ j ∈ s, opP R (m j)) F z) := by
  funext z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, Finset.sum_apply, opP_map, map_sum]

theorem opL_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (N l : ℕ) (T : Letter)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opL S N l T (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opL R N l T F z) := by
  cases T with
  | T q =>
    simp only [opL, LinearMap.add_apply, sum_opP_map, opP_map]
    funext z; simp
  | U => simp only [opL, sum_opP_map]
  | D d => simp only [opL, opP_map]

end GlobalTheory.KZ.H3.LamStab


open GlobalTheory.KZ.H3 GlobalTheory.KZ.H3.LamStab in
theorem GlobalTheory.KZ.H3.lam_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)),
    p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l _ E _ _ T p hp
  let Φ : ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) →ₗ[E]
      ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
    LinearMap.prodMap (X.opV N l E T) (opL E N l T)
  have key : abelian₂ X l E ≤ (abelian₂ X l E).comap Φ := by
    unfold abelian₂
    rw [Submodule.span_le]
    rintro q ⟨b, F, hR, rfl⟩
    refine Submodule.subset_span ⟨X.op N l T b, opL ℤ_[l] N l T F,
      (GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l).2.2.2.2 N T b F hR, ?_⟩
    simp only [Φ, LinearMap.prodMap_apply, Tower.opV, LinearMap.baseChange_tmul, opL_map]
  exact key hp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStableStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)), p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.lam_stable | exact GlobalTheory.KZ.H3.lam_stable | (intros; apply GlobalTheory.KZ.H3.lam_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVB
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVB
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_mem_pot {E : Type} [CommRing E] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] E] {w : ℕ}
    {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (hF : F ∈ Pot ℤ_[l] w Γ) :
    (fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z)) ∈ Pot E w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map _, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map (algebraMap ℤ_[l] E) p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, polySlash_map]

theorem exists_pot_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E],
    (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) →
      ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l w _ E _ _ hB
  let S : Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
    { carrier := {x | ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ abelian₂ X l E}
      add_mem' := by
        rintro x y ⟨G, hG, hx⟩ ⟨G', hG', hy⟩
        exact ⟨G + G', (Betti.potSub E w (Gam N l)).add_mem hG hG', (abelian₂ X l E).add_mem hx hy⟩
      zero_mem' := ⟨0, (Betti.potSub E w (Gam N l)).zero_mem, (abelian₂ X l E).zero_mem⟩
      smul_mem' := by
        rintro c x ⟨G, hG, hx⟩
        exact ⟨c • G, (Betti.potSub E w (Gam N l)).smul_mem c hG, (abelian₂ X l E).smul_mem c hx⟩ }
  have h1 : ∀ b ∈ X.B N l w, (1 : E) ⊗ₜ[ℤ_[l]] b ∈ S := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨F, hF, hR⟩ := hB b hb
      exact ⟨_, map_mem_pot hF, Submodule.subset_span ⟨b, F, hR, rfl⟩⟩
    | zero => simpa using S.zero_mem
    | add b b' _ _ h h' => simpa [TensorProduct.tmul_add] using S.add_mem h h'
    | smul r b _ h =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul E r]
      exact S.smul_mem _ h
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  show _ ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simpa using S.zero_mem
  | tmul c b =>
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
    have : c ⊗ₜ[ℤ_[l]] (b : X.Fn l) = c • ((1 : E) ⊗ₜ[ℤ_[l]] (b : X.Fn l)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact S.smul_mem c (h1 b b.2)
  | add y y' h h' => rw [map_add (f := _)]; exact S.add_mem h h'

end GlobalTheory.KZ.H3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVBStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E], (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) → ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_mem_VB | exact GlobalTheory.KZ.H3.exists_pot_of_mem_VB | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_mem_VB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquiv
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.Transport

variable {R S : Type} [CommRing R] [CommRing S]

def mapF (φ : R →+* S) (F : ℂ → MvPolynomial (Fin 2) R) : ℂ → MvPolynomial (Fin 2) S :=
  fun z => MvPolynomial.map φ (F z)

theorem map_smul' (φ : R →+* S) (c : R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (c • p) = φ c • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_slP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (slP m p) = slP m (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, Betti.slP_X, MvPolynomial.map_X, map_add (f := _), map_smul', map_intCast]

theorem mapF_add (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F + G) = mapF φ F + mapF φ G := by
  funext z; simp [mapF]

theorem mapF_sub (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F - G) = mapF φ F - mapF φ G := by
  funext z; simp [mapF]

theorem mapF_smul (φ : R →+* S) (c : R) (F : ℂ → MvPolynomial (Fin 2) R) : mapF φ (c • F) = φ c • mapF φ F := by
  funext z; simp [mapF, map_smul']

theorem mapF_sum {ι : Type} (φ : R →+* S) (s : Finset ι) (F : ι → ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (∑ j ∈ s, F j) = ∑ j ∈ s, mapF φ (F j) := by
  funext z; simp [mapF, Finset.sum_apply, map_sum]

theorem mapF_opP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opP R m F) = opP S m (mapF φ F) := by
  funext z; simp [mapF, opP, map_slP]

theorem mapF_opL (φ : R →+* S) (N l : ℕ) (T : Letter) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opL R N l T F) = opL S N l T (mapF φ F) := by
  cases T with
  | T q => simp only [opL, LinearMap.add_apply, LinearMap.sum_apply, mapF_add, mapF_sum, mapF_opP]
  | U => simp only [opL, LinearMap.sum_apply, mapF_sum, mapF_opP]
  | D d => simp only [opL, mapF_opP]

theorem mapF_mem_pot (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Pot R w Γ) : mapF φ F ∈ Pot S w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map φ, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map φ p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, map_slP]; rfl

theorem mapF_mem_triv (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Triv R w Γ) : mapF φ F ∈ Triv S w Γ := by
  obtain ⟨ψ, p, h1, h2⟩ := hF
  refine ⟨mapF φ ψ, MvPolynomial.map φ p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
  · simp only [mapF]; rw [← map_slP, h1 γ hγ z hz]
  · simp only [mapF]; rw [h2 z hz, map_add (f := _)]

theorem exists_preimage (ι : R ≃+* S) (N l : ℕ) (lam : Letter → R) {P : FreeAlgebra S Letter} (hP : P ∈ admissibleLettersSubalgebra S N l) :
    ∃ Q ∈ admissibleLettersSubalgebra R N l, ι (FreeAlgebra.lift R lam Q) = FreeAlgebra.lift S (fun T => ι (lam T)) P ∧
      ∀ F, mapF (ι : R →+* S) (FreeAlgebra.lift R (opL R N l) Q F) =
        FreeAlgebra.lift S (opL S N l) P (mapF (ι : R →+* S) F) := by
  unfold admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact ⟨FreeAlgebra.ι R T, Algebra.subset_adjoin ⟨T, hT, rfl⟩, by simp, fun F => by simp [mapF_opL]⟩
  | algebraMap r =>
    refine ⟨algebraMap R _ (ι.symm r), Subalgebra.algebraMap_mem _ _, by simp, fun F => ?_⟩
    simp [Module.algebraMap_end_apply, mapF_smul]
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q + Q', add_mem hQ hQ', by simp [h1, h1'], fun F => by simp [mapF_add, h2, h2']⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q * Q', mul_mem hQ hQ', by simp [h1, h1'], fun F => by simp [h2, h2']⟩

theorem mapF_symm_mapF (ι : R ≃+* S) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF (ι.symm : S →+* R) (mapF (ι : R →+* S) F) = F := by
  funext z
  simp only [mapF, MvPolynomial.map_map]
  rw [RingEquiv.symm_comp, MvPolynomial.map_id]

end GlobalTheory.KZ.Transport


open GlobalTheory.KZ.Transport in
theorem GlobalTheory.KZ.ssPot_transport : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E),
    SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧
      ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T →
        (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  intro N l w E _ ι lam ⟨P, hP, h1, h2⟩
  obtain ⟨Q, hQ, e1, e2⟩ := exists_preimage ι N l lam hP
  refine ⟨Q, hQ, ι.injective (by rw [e1, h1, map_one]), fun F hF T hT => ?_⟩
  have h := mapF_mem_triv (ι.symm : ℂ →+* E) (h2 _ (mapF_mem_pot (ι : E →+* ℂ) hF) T hT)
  rw [← e2] at h
  rw [← mapF_symm_mapF ι ((opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) Q F))]
  convert h using 2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, mapF_sub, mapF_smul, mapF_opL]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquivStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T → (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E))) (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  first | exact @GlobalTheory.KZ.ssPot_transport | exact GlobalTheory.KZ.ssPot_transport | (intros; apply GlobalTheory.KZ.ssPot_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentials
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.Comp

theorem lift_mem_lam {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (P : FreeAlgebra E Letter) :
    ∀ p ∈ H3.abelian₂ X l E,
      (FreeAlgebra.lift E (X.opV N l E) P p.1, FreeAlgebra.lift E (opL E N l) P p.2) ∈ H3.abelian₂ X l E := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro p hp
    convert (H3.abelian₂ X l E).smul_mem r hp using 1
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  | grade1 T =>
    intro p hp
    simpa using GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T p hp
  | mul a b ha hb =>
    intro p hp
    simpa using ha _ (hb p hp)
  | add a b ha hb =>
    intro p hp
    simpa using (H3.abelian₂ X l E).add_mem (ha p hp) (hb p hp)

theorem ssbb_of_ssPotB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ ι lam hSS
  haveI : CharZero E := RingHom.charZero ι.toRingHom
  obtain ⟨P, hPA, hP1, hP⟩ := GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv N l w ι lam hSS
  refine ⟨P, hPA, hP1, fun x hx T hT => ?_⟩
  obtain ⟨G, hG, hxG⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB ε X N l w (GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer ε X hε hj N l w hl2 hN hNl hw) x hx
  have h1 := lift_mem_lam ε X N l P (x, G) hxG
  have h2 := GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T _ h1
  have h3 := (H3.abelian₂ X l E).sub_mem h2 ((H3.abelian₂ X l E).smul_mem (lam T) h1)
  have h4 : ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        (FreeAlgebra.lift E (X.opV N l E) P x),
      (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
        (FreeAlgebra.lift E (opL E N l) P G)) ∈ H3.abelian₂ X l E := by
    simpa using h3
  exact GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial ε X hε hj N l w (by omega) inferInstance _ _ h4 (hP G hG T hT)

end GlobalTheory.KZ.Comp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentialsStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_tensor_of_semisimple_potentials : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  first | exact @GlobalTheory.KZ.Comp.ssbb_of_ssPotB | exact GlobalTheory.KZ.Comp.ssbb_of_ssPotB | (intros; apply GlobalTheory.KZ.Comp.ssbb_of_ssPotB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProjectorNewformGaloisImage
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeProj

theorem heckeProj_newform : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) [Fact l.Prime], l ≠ 2 → g.M ∣ N → 5 ≤ N → Nat.Coprime N l → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lamC : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lamC (Letter.T q) = g.a q) → lamC Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lamC (Letter.D d) = g.χ (d : ZMod g.M)) → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (ι : E ≃+* ℂ), let w := k - 2; let lam : Letter → E := fun T => ι.symm (lamC T); ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  intro Ω _ _ _ ε X hε han k g N l _ hl2 hgN hN5 hNl hk hk3 α hα hα1 hα2 lamC hT hU hD E _ _ _ hnorm ι
    w lam ρ S0 htr hdet hfrob hirr
  have hlp : l.Prime := Fact.out
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd hlp).1 hNl.symm
  have hpot : SSPotB N l (k - 2) lamC :=
    GlobalTheory.T.semisimple_potentials_at_newform_eigensystem k g N l hgN hN5 hlp hlN hk hk3 α hα hα1 hα2 lamC hT hU hD
  have hw : Odd w := by
    obtain ⟨j, rfl⟩ := hk
    refine ⟨j - 1, ?_⟩
    show 2 * j + 1 - 2 = 2 * (j - 1) + 1
    omega
  have hpot' : SSPotB N l w (fun T => ι (lam T)) := by
    have : (fun T => ι (lam T)) = lamC := by
      funext T; simp [lam]
    rw [this]; exact hpot
  have hbb : X.SSBB N l w E lam :=
    GlobalTheory.T.semisimple_tensor_of_semisimple_potentials ε X hε han N l w hl2 hN5 hNl hw ι lam hpot'
  exact GlobalTheory.T.galois_representation_of_eigensystem ε X hε han N l w hl2 hN5 hNl hw hnorm lam hbb ρ S0 htr hdet hfrob hirr

end GlobalTheory.KZ.HeckeProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProjectorNewformGaloisImageStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeProjector_newform_galoisImage : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) [Fact l.Prime], l ≠ 2 → g.M ∣ N → 5 ≤ N → Nat.Coprime N l → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lamC : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lamC (Letter.T q) = g.a q) → lamC Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lamC (Letter.D d) = g.χ (d : ZMod g.M)) → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (ι : E ≃+* ℂ), let w := k - 2; let lam : Letter → E := fun T => ι.symm (lamC T); ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  first | (exact @GlobalTheory.KZ.HeckeProj.heckeProj_newform) | (exact GlobalTheory.KZ.HeckeProj.heckeProj_newform) | (intros; apply GlobalTheory.KZ.HeckeProj.heckeProj_newform  <;> assumption)
end

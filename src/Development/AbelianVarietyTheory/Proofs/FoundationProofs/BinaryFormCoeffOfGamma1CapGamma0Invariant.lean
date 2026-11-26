module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFree
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFree
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem rootOfUnity_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  haveI : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

theorem khat_l_smul_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    [IsAlgClosed Ω] (x : X.Khat l) (hx : (l : ℤ_[l]) • x = 0) : x = 0 := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, -, -, -, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)
  obtain ⟨-, hker, hmul, hone, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  obtain ⟨-, -, -, -, -, -, hred⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

theorem khat_torsionFree (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    [IsAlgClosed Ω] (c : ℤ_[l]) (x : X.Khat l) (hc : c ≠ 0) (hcx : c • x = 0) : x = 0 := by
  have key : ∀ k : ℕ, ∀ y : X.Khat l, ((l : ℤ_[l]) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      apply khat_l_smul_eq_zero X l
      apply ih
      rw [smul_smul, ← pow_succ]; exact hy
  apply key c.valuation
  have h := PadicInt.unitCoeff_spec hc
  have : ((PadicInt.unitCoeff hc)⁻¹ : ℤ_[l]ˣ) • (c • x) = 0 := by rw [hcx, smul_zero]
  rw [Units.smul_def, smul_smul] at this
  nth_rw 2 [h] at this
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFreeStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (c : ℤ_[l]) (x : X.Khat l), c ≠ 0 → c • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.H3.khat_torsionFree | exact GlobalTheory.KZ.H3.khat_torsionFree | (intros; apply GlobalTheory.KZ.H3.khat_torsionFree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCoeffEqZero
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory

theorem homogeneous_poly_coeff_eq_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (htf : ∀ (c : ℤ_[l]) (x : M), c ≠ 0 → c • x = 0 → x = 0) (w : ℕ) (c : Fin (w + 1) → M)
    (hv : ∀ u : Fin 2 → ℤ_[l], ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i = 0) :
    c = 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] := Matrix.vandermonde (fun t : Fin (w + 1) => ((t : ℕ) : ℤ_[l])) with hVdef
  have hrow : ∀ t : Fin (w + 1), ∑ i, V t i • c i = 0 := by
    intro t
    have := hv ![((t : ℕ) : ℤ_[l]), 1]
    simpa [hVdef, Matrix.vandermonde_apply] using this
  have hdet : V.det ≠ 0 := by
    rw [hVdef, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    apply Fin.ext
    have hab' : ((a : ℕ) : ℤ_[l]) = ((b : ℕ) : ℤ_[l]) := hab
    exact_mod_cast hab'
  have key : ∀ j, V.det • c j = 0 := by
    intro j
    have h1 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = 0 := by simp [hrow]
    have h2 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = ∑ i, (V.adjugate * V) j i • c i := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
    rw [h2, Matrix.adjugate_mul] at h1
    simpa [Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq] using h1
  funext j
  exact htf _ _ hdet (key j)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.coef_of_inv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  intro Ω _ _ ε X l _ _ N w b c hb γ _ hinv
  obtain ⟨hslP, -, -, hev, -⟩ := mon_expand ℤ_[l] w
  have hk : ∀ (u : Fin 2 → ℤ_[l]) (k : Fin (w + 1)),
      (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 ^ (k : ℕ) * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 ^ (w - (k : ℕ)) =
        ∑ i, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) * (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) := by
    intro u k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hev, mZl, ← Betti.eval_slP, hslP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hev]
  have key : ∀ u : Fin 2 → ℤ_[l], b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) •
      ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
    intro u
    rw [← congrFun hinv u]
    show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Betti.toGQ_sl, hb, map_sum]
    simp_rw [map_smul, hk, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hz := GlobalTheory.homogeneous_poly_coeff_eq_zero l (X.Khat l)
    (fun a x ha hx => GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree Ω ε X l a x ha hx) w
    (fun i => c i - ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
    (by intro u; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, ← hb u, ← key u, sub_self])
  intro i
  exact sub_eq_zero.1 (congrFun hz i)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0InvariantStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  first | exact @GlobalTheory.KZ.H3.coef_of_inv | exact GlobalTheory.KZ.H3.coef_of_inv | (intros; apply GlobalTheory.KZ.H3.coef_of_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuation
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KronRatio

open GlobalTheory.KroneckerCongruence

variable {Ω : Type} [Field Ω]

theorem mem_of_isIntegral_int (V : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).1 h
  rw [← hy]; exact y.2

theorem valuation_natCast_eq_one (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) (hD : ¬ q ∣ D) : V.valuation (D : Ω) = 1 := by
  have hcop : IsCoprime (q : ℤ) (D : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 hD
  obtain ⟨a, b, hab⟩ := hcop
  have hle : ∀ n : ℤ, V.valuation (n : Ω) ≤ 1 := fun n => (V.valuation_le_one_iff _).2 (intCast_mem V n)
  have hq1 : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.1 hqV
  by_contra hne
  have hD1 : V.valuation (D : Ω) < 1 := lt_of_le_of_ne ((V.valuation_le_one_iff _).2 (natCast_mem V D)) hne
  have h1 : (1 : Ω) = (a : Ω) * (q : Ω) + (b : Ω) * (D : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this.symm
  have h2 : V.valuation (1 : Ω) < 1 := by
    rw [h1]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hq1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hD1
  simp at h2

theorem mem_of_bdd (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime) (hqV : ((q : ℕ) : Ω) ∈ V.nonunits)
    (hD : ¬ q ∣ D) {a : Ω} (h : ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * a)) : a ∈ V := by
  obtain ⟨k, hk⟩ := h
  have h1 := mem_of_isIntegral_int V hk
  have hv := valuation_natCast_eq_one V hq hqV hD
  rw [← V.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, map_pow, hv, one_pow, one_mul] at h1

theorem coeff_mul_mem (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V)
    (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V := by
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_pow_mem (V : ValuationSubring Ω) (x : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V) (n : ℕ)
    (r : ℚ) : (x ^ n).coeff r ∈ V := by
  have he : x ^ n = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx ^ n) := by
    rw [map_pow, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_mul_mem_nonunits (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω)
    (hx : ∀ r, x.coeff r ∈ V.nonunits) (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V.nonunits := by
  have hx' : ∀ r, x.coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hx r)))
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ z : V, ρ z = 0 ↔ V.valuation (z : Ω) < 1 := fun z => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hX : hahnSeriesCoeffRingHomMap ρ (liftV V x hx') = 0 := by
    ext t
    rw [hahnSeriesCoeffRingHomMap_coeff]
    exact (hρ0 _).2 (V.mem_nonunits_iff.1 (hx t))
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx' * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 ((liftV V x hx' * liftV V y hy).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, map_mul, hX, zero_mul]
  rfl

end GlobalTheory.KronRatio

namespace GlobalTheory.KZ


open GlobalTheory.KroneckerCongruence GlobalTheory.KronRatio in
theorem kronecker_ratio_reduces_to_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  intro Ω _ _ _ ε X hε hj M f hM hf
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let F : SL(2, ZMod M) → X.K := fun τ =>
    if h : ∃ σ, red σ = τ then X.sl (ofSL h.choose) (f : X.K) else (f : X.K)
  have hF : ∀ σ : SL(2, ℤ), X.sl (ofSL σ) (f : X.K) = F (red σ) := by
    intro σ
    have h : ∃ σ', red σ' = red σ := ⟨σ, rfl⟩
    have e : F (red σ) = X.sl (ofSL h.choose) (f : X.K) := dif_pos h
    have hσ' : red h.choose = red σ := h.choose_spec
    have hγ : σ * h.choose⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      have : σ * h.choose⁻¹ ∈ red.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ', mul_inv_cancel]
      exact this
    rw [e]
    calc X.sl (ofSL σ) (f : X.K) = X.sl (ofSL (σ * h.choose⁻¹ * h.choose)) (f : X.K) := by
          rw [inv_mul_cancel_right]
      _ = X.sl (ofSL h.choose) (X.sl (ofSL (σ * h.choose⁻¹)) (f : X.K)) := by rw [map_mul, X.sl_mul]
      _ = _ := by rw [hf _ hγ]
  choose D hD0 hD using X.bdd
  let P : X.K → Finset ℕ := fun g => (D g).primeFactors ∪ (D g⁻¹).primeFactors
  refine ⟨M.primeFactors ∪ P f ∪ Finset.univ.biUnion (fun τ => P (F τ)), ?_⟩
  intro q hq hqS V s hqV hs σ hσ W hW hdom
  have hn : ∀ h : X.K, q ∉ (D h).primeFactors → ∀ r, (X.exp h).coeff r ∈ V := fun h hh r =>
    mem_of_bdd V hq hqV (fun hd => hh (Nat.mem_primeFactors.2 ⟨hq, hd, (hD0 h).ne'⟩)) (hD h r)
  have hint : ∀ g : X.K, q ∉ P g → (∀ r, (X.exp g).coeff r ∈ V) ∧ (∀ r, (X.exp g⁻¹).coeff r ∈ V) := fun g hg =>
    ⟨hn g fun h => hg (Finset.mem_union_left _ h), hn _ fun h => hg (Finset.mem_union_right _ h)⟩
  have hqM : q ∉ M.primeFactors := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hqf : q ∉ P f := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hqF : q ∉ P (F (red σ)) := fun h =>
    hqS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  obtain ⟨hf1, hf2⟩ := hint _ hqf
  rw [← hF σ] at hqF
  obtain ⟨hs1, hs2⟩ := hint _ hqF
  have hcop : Nat.Coprime q M :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  have hK := kronecker_congruence_tower ε X hε hj M q (f : X.K) hM hq hcop hf σ ⟨hσ.2.1, hσ.2.2⟩ V s hqV hs hf1 hs1
  refine ⟨1, one_ne_zero, ?_⟩
  generalize (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
    X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = A at hK ⊢
  have hB0 : X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 f.ne_zero)
      (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero _).2 f.ne_zero)))
  have hBinv : ∀ r, (X.exp (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q)⁻¹).coeff r ∈ V := by
    intro r
    rw [mul_inv, ← inv_pow, ← map_inv₀, ← map_inv₀ (X.gal s.symm), map_mul, map_pow]
    refine coeff_mul_mem V _ _ (fun t => ?_) (coeff_pow_mem V _ (fun t => ?_) q) r
    · rw [X.gal_exp]; exact (hs _ (hf2 t)).1
    · rw [X.gal_exp]; exact (hs _ (hs2 t)).2.1
  generalize X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q = B at hK hB0 hBinv ⊢
  have hge : algebraMap Ω X.K 1 * A / B - 1 = (A - B) * B⁻¹ := by
    rw [map_one, one_mul]; field_simp
  rw [hge]
  have hgc : ∀ r, (X.exp ((A - B) * B⁻¹)).coeff r ∈ V.nonunits := by
    intro r; rw [map_mul]; exact coeff_mul_mem_nonunits V _ _ hK hBinv r
  generalize (A - B) * B⁻¹ = g at hgc ⊢
  have hgV : ∀ r, (X.exp g).coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hgc r)))
  have h1 := hdom g hgV fun r _ => hgc r
  have hcV := V.mem_nonunits_iff.1 (hgc 0)
  have hcm := hgV 0
  generalize (X.exp g).coeff 0 = c at h1 hcV hcm
  have h2 : W.valuation (algebraMap Ω X.K c) < 1 := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact zero_lt_one
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 ((hW c).2 hcm)) fun heq => ?_
    have hinv : algebraMap Ω X.K c⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have h3 : V.valuation c⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 ((hW _).1 hinv)
    have h4 : V.valuation (c⁻¹ * c) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) hcV
    rw [inv_mul_cancel₀ hc0, map_one] at h4
    exact lt_irrefl _ h4
  have h5 := lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt h1 h2)
  rwa [sub_add_cancel] at h5

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuationStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerRatio_reduces_to_const_mod_valuation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  first | exact @GlobalTheory.KZ.kronecker_ratio_reduces_to_const | exact GlobalTheory.KZ.kronecker_ratio_reduces_to_const | (intros; apply GlobalTheory.KZ.kronecker_ratio_reduces_to_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwisted
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem Datum.theta_ne_zero_of_mem {G : Type} [Group G] [TopologicalSpace G] {H : Set G} {θ : G → ℂ}
    (hD : Datum H θ) {j : G} (hj : j ∈ H) : θ j ≠ 0 := by
  intro h0
  have h := hD.val_mul j hj j⁻¹ (hD.inv j hj)
  rw [mul_inv_cancel, hD.val_one, h0, zero_mul] at h
  exact one_ne_zero h

theorem eig_compl_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  intro G V _ _ _ _ _ π hπ H θ hD
  refine ⟨fun u hu he => ?_, fun w => ?_⟩
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ H θ hD u hu
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    have hsum : ∑ j ∈ R, (θ j)⁻¹ • π j u = (R.card : ℂ) • u := by
      rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
      intro j hj
      rw [he j (hRH j hj), smul_smul, inv_mul_cancel₀ (hD.theta_ne_zero_of_mem (hRH j hj)), one_smul]
    rw [hsum] at hs
    exact (smul_eq_zero.mp hs).resolve_left hc
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ H θ hD w
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    refine ⟨(R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w, ?_, ?_⟩
    · intro h hh
      rw [(π h).map_smul, hs h hh]
      exact smul_comm _ _ _
    · have e : w - (R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w
          = (R.card : ℂ)⁻¹ • ∑ j ∈ R, (w - (θ j)⁻¹ • π j w) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
      have hθ := hD.theta_ne_zero_of_mem (hRH j hj)
      have e2 : w - (θ j)⁻¹ • π j w = -(θ j)⁻¹ • (π j w - θ j • w) := by
        rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hθ, one_smul, neg_sub]
      rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hRH j hj, w, rfl⟩)

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwistedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  first | exact @GlobalTheory.PsType.eig_compl_aug | exact GlobalTheory.PsType.eig_compl_aug | (intros; apply GlobalTheory.PsType.eig_compl_aug <;> assumption)
end
end

module

public import Formalism.SatakeDualWeyl.Statement
public import Lemmata.NearbyExistence.ExistsNear

@[expose] public section

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]

theorem glint_mem_range_of_integral (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have inj : Function.Injective (RingHom.mapMatrix (m := n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext : 1
  simp only [bc, Units.coe_map]
  exact hA

theorem glint_conj_integral (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h : GL n O) (hh : redGL (n := n) (Ideal.span {c * c}) h = 1) :
    ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) ∈
      (RingHom.mapMatrix (m := n) O.subtype).range := by
  have hm : RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) =
      RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by
    rw [map_one]; exact congrArg Units.val hh
  have hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c} := by
    intro a b
    rw [← Ideal.Quotient.eq]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm a) b
  choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)
  let E : Matrix n n O := Matrix.of e
  have hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) =
      (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L) := by
    intro a b
    have h1 := he a b
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hab
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
  have hkey : ((bc (n := n) O.subtype h : GL n L) : Matrix n n L) =
      1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by
    ext a b
    simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      E, Matrix.of_apply, Subring.coe_subtype]
    exact hL a b
  have hcalc : ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) =
      1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E *
        ((c : L) • (g : Matrix n n L)) := by
    rw [Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hcalc]
  exact add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)

theorem glint_princ_le_map_conj (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    princ (n := n) O.subtype (Ideal.span {c * c}) ≤
      (GLint n O).map (MulAut.conj g).toMonoidHom := by
  intro k hk
  simp only [princ, congPre] at hk
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hk
  have hh' : redGL (n := n) (Ideal.span {c * c}) h = 1 := by
    simpa only [Subgroup.mem_comap, Subgroup.mem_bot] using hh
  have hh'' : redGL (n := n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]
  refine Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩
  · apply glint_mem_range_of_integral
    · exact glint_conj_integral O g c hg hg' h hh'
    · have : (g⁻¹ * bc (n := n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by
        rw [map_inv]; group
      rw [this]
      exact glint_conj_integral O g c hg hg' h⁻¹ hh''
  · simp [MulAut.conj_apply, mul_assoc]

theorem glint_princ_relIndex_ne_zero (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by
  classical
  have : Finite (Matrix n n (O ⧸ I)) := inferInstanceAs (Finite (n → n → O ⧸ I))
  have hN : (redGL (n := n) I).ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hsup : ((redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by
    intro h
    apply hN
    have hd := Subgroup.index_dvd_of_le
      (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  have hprinc : princ (n := n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by
    unfold princ congPre
    rw [MonoidHom.comap_bot]
  rw [hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact hsup

theorem glint_exists_denom (A : ValuationSubring L) (g : GL n L) :
    ∃ c : A.toSubring, c ≠ 0 ∧
      (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) A.toSubring.subtype).range ∧
      (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈
        (RingHom.mapMatrix (m := n) A.toSubring.subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → L := fun i => match i with
    | .inl p => (g : Matrix n n L) p.1 p.2
    | .inr p => ((g⁻¹ : GL n L) : Matrix n n L) p.1 p.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) f
  have hmem : ∀ i, (b : L) * f i ∈ A := by
    intro i
    obtain ⟨y, hy⟩ := hb i
    rw [Algebra.smul_def] at hy
    have : (b : L) * f i = (y : L) := hy.symm
    rw [this]; exact y.2
  refine ⟨⟨(b : A), (b : A).2⟩, ?_, ?_, ?_⟩
  · intro h0
    apply nonZeroDivisors.ne_zero b.2
    exact Subtype.ext (congrArg Subtype.val h0)
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * (g : Matrix n n L) i j, hmem (.inl (i, j))⟩, ?_⟩
    ext i j
    simp
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * ((g⁻¹ : GL n L) : Matrix n n L) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j
    simp

end Generic

section Adic

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem glint_exists_approx (x : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v ((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  first | exact Bl.NearbyExistence.goal1 .. | (apply Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply @Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> first | assumption | infer_instance)

theorem glint_finite_residueField :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  have hs : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  exact Finite.of_surjective _ hs

theorem glint_finite_quotient_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : Finite (IsLocalRing.ResidueField R)) (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key : ∀ k : ℕ, Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Ideal.one_eq_top]
      exact Finite.of_fintype (R ⧸ ⊤)
    | succ k ih =>
      have hle : IsLocalRing.maximalIdeal R ^ (k + 1) ≤ IsLocalRing.maximalIdeal R ^ k :=
        Ideal.pow_le_pow_right (by simp)
      replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.toEquiv
      suffices Finite (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))
          (IsLocalRing.maximalIdeal R ^ k)) from
        .of_ideal_quotient (.map (Ideal.Quotient.mk _) (IsLocalRing.maximalIdeal R ^ k))
      exact @Finite.of_equiv _ _ h
        ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal _)
          (IsDiscreteValuationRing.not_a_field _) k).trans
          (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ k))
  have : I = IsLocalRing.maximalIdeal R ^ m := by
    rw [hm, hmax, Ideal.span_singleton_pow]
  rw [this]
  exact key m

end Adic

theorem GL_integral_hecke_commute : Formalism.UG.GLintComm := by
  intro F _ _ v n g
  obtain ⟨c, hc0, hg, hg'⟩ := glint_exists_denom (v.adicCompletionIntegers F) g
  have hP := glint_princ_le_map_conj (v.adicCompletionIntegers F).toSubring g c hg hg'
  have hres : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := glint_finite_residueField v
  have hI : Ideal.span {c * c} ≠ (⊥ : Ideal (v.adicCompletionIntegers F).toSubring) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hc0
  have hfin : Finite ((v.adicCompletionIntegers F).toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hres _ hI
  have hne := glint_princ_relIndex_ne_zero (n := Fin n) (v.adicCompletionIntegers F).toSubring
    (Ideal.span {c * c})
  have hd := Subgroup.relIndex_dvd_of_le_left (bc (n := Fin n) (v.adicCompletionIntegers F).toSubring.subtype).range hP
  intro h0
  apply hne
  unfold GLint at h0 hd
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

end Formalism.UG.P
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem bc_coe {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ :=
  by simp [bc]

theorem incl_cT_map {A B : Type} [CommRing A] [CommRing B] {m p : Type}
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ
  rw [bc_coe, incl_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem inclE_injective (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  intro x y hxy
  apply Algebra.TensorProduct.includeLeft_injective (S := F) (A := E) (B := R)
    (algebraMap F R).injective
  exact hxy

theorem UG_inclusion_injective : Formalism.UG.InclInj := by
  intro F E _ _ _ n _ _ R _ _ hR
  haveI := hR
  intro g g' hgg
  apply Units.ext
  have h1 := congrArg Units.val hgg
  rw [bc_coe, bc_coe] at h1
  ext i j
  exact inclE_injective F E R (congrFun (congrFun h1 i) j)

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
open Matrix

namespace Formalism.UG.P

open Formalism.UG

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

section Sig

variable {n : Type} [Fintype n] [DecidableEq n]

theorem sig_data (J : Matrix n n ℂ) (p q : ℕ) (h : HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e id, ?_⟩
  rw [cT_conj_eq] at hP

  have hJ : J = (J.reindex e e).submatrix e e := by
    ext i j; simp
  rw [hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact hP

theorem sig_quad {p q : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (x : Fin p ⊕ Fin q → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) =
      (∑ i, star (x (Sum.inl i)) * x (Sum.inl i)) - ∑ j, star (x (Sum.inr j)) * x (Sum.inr j) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hQ, ← Matrix.dotProduct_mulVec]
  simp [Jpq, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
    Matrix.neg_mulVec, Finset.sum_neg_distrib]

private lemma eq_zero_of_sum_star_mul_self_add_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (b : κ → ℂ)
    (h : (∑ i, star (a i) * a i) + ∑ j, star (b j) * b j = 0) : a = 0 ∧ b = 0 := by
  have hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [hz] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have h1 : 0 ≤ ∑ i, Complex.normSq (a i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 : 0 ≤ ∑ j, Complex.normSq (b j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hA : ∑ i, Complex.normSq (a i) = 0 := by linarith
  have hB : ∑ j, Complex.normSq (b j) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at hA hB
  exact ⟨funext fun i => Complex.normSq_eq_zero.1 (hA i (Finset.mem_univ _)),
    funext fun j => Complex.normSq_eq_zero.1 (hB j (Finset.mem_univ _))⟩

theorem sig_dim {p q p' q' : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (Q' : Matrix n (Fin p' ⊕ Fin q') ℂ)
    (hQ' : Q'ᴴ * J * Q' = Jpq p' q') :
    p + q' ≤ Fintype.card n := by
  classical

  let φ : ((Fin p → ℂ) × (Fin q' → ℂ)) →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun ab => Q *ᵥ Sum.elim ab.1 (0 : Fin q → ℂ) + Q' *ᵥ Sum.elim (0 : Fin p' → ℂ) ab.2
      map_add' := by
        intro x y
        have h1 : Sum.elim (x.1 + y.1) (0 : Fin q → ℂ) = Sum.elim x.1 (0 : Fin q → ℂ) + Sum.elim y.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (x.2 + y.2) = Sum.elim (0 : Fin p' → ℂ) x.2 + Sum.elim (0 : Fin p' → ℂ) y.2 := by
          ext (i | i) <;> simp
        simp only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.mulVec_add]
        abel
      map_smul' := by
        intro c x
        have h1 : Sum.elim (c • x.1) (0 : Fin q → ℂ) = c • Sum.elim x.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (c • x.2) = c • Sum.elim (0 : Fin p' → ℂ) x.2 := by
          ext (i | i) <;> simp
        simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.mulVec_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hw : Q *ᵥ Sum.elim a (0 : Fin q → ℂ) = Q' *ᵥ (-(Sum.elim (0 : Fin p' → ℂ) b)) := by
      rw [Matrix.mulVec_neg]
      exact eq_neg_of_add_eq_zero_left hab
    have e1 := sig_quad J Q hQ (Sum.elim a (0 : Fin q → ℂ))
    have e2 := sig_quad J Q' hQ' (-(Sum.elim (0 : Fin p' → ℂ) b))
    rw [← hw, e1] at e2
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply, star_zero, mul_zero,
      Finset.sum_const_zero, sub_zero, zero_sub, star_neg, neg_mul_neg] at e2
    have := eq_zero_of_sum_star_mul_self_add_eq_zero a b (by rw [e2]; ring)
    rw [this.1, this.2]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at this

end Sig

theorem signature_unique : Formalism.UG.SigUnique := by
  intro n _ _ J p q p' q' h h'
  obtain ⟨hc, Q, hQ⟩ := sig_data J p q h
  obtain ⟨hc', Q', hQ'⟩ := sig_data J p' q' h'
  have d1 := sig_dim J Q hQ Q' hQ'
  have d2 := sig_dim J Q' hQ' Q hQ
  omega

end Formalism.UG.P
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem base_change_mem_holds : Formalism.UG.BCMem := by
  intro A B _ _ n _ _ σ σ' φ h J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) =
    J.map φ
  have e : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ := rfl
  rw [e, cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem rational_points_le_holds : Formalism.UG.RatPtsLe := by
  intro F E _ _ _ n _ _ σ J R _ _ x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hc : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE (F := F) R) := by
    ext e
    simp [inclE, sigR, Algebra.TensorProduct.map_tmul]
  exact base_change_mem_holds E (E ⊗[F] R) n (σ : E →+* E) (sigR σ R) (inclE (F := F) R) hc J g hg

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
noncomputable section

namespace Formalism.UG.P

open Matrix

variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_stdLat_iff' (x : n → A) :
    x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, x i ∈ Set.range (algebraMap R A) := by
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
    LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range]

theorem map_mulVec_mem_stdLat (M : Matrix n n R) (x : n → A)
    (hx : x ∈ stdLat (n := n) (A := A) R) :
    (M.map (algebraMap R A)) *ᵥ x ∈ stdLat (n := n) (A := A) R := by
  rw [mem_stdLat_iff'] at hx ⊢
  choose y hy using hx
  have hxy : x = fun j => algebraMap R A (y j) := funext fun j => (hy j).symm
  subst hxy
  intro i
  refine ⟨(M *ᵥ y) i, ?_⟩

  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem entries_mem_of_mem_stabGL (h : GL n A)
    (hh : h ∈ Formalism.UG.stabGL (stdLat (n := n) (A := A) R))
    (i j : n) : (h : Matrix n n A) i j ∈ Set.range (algebraMap R A) := by
  have hmem : (Pi.single j 1 : n → A) ∈ stdLat (n := n) (A := A) R := by
    rw [mem_stdLat_iff']
    intro k
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hk]⟩
  have h2 := ((hh (Pi.single j 1)).1 hmem)
  rw [mem_stdLat_iff'] at h2
  have h3 := h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

theorem coe_bc (φ : R →+* A) (u : GL n R) :
    ((bc (n := n) φ u : GL n A) : Matrix n n A) = (u : Matrix n n R).map φ := by
  simp [bc, RingHom.mapMatrix_apply]

theorem stabilizer_standard_lattice : Formalism.UG.StabStd := by
  unfold Formalism.UG.StabStd
  intro A R _ _ _ n _ _ hinj
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Formalism.UG.stabGL (stdLat (n := n) (A := A) R) := inv_mem hg
    choose r hr using entries_mem_of_mem_stabGL (R := R) g hg
    choose r' hr' using entries_mem_of_mem_stabGL (R := R) g⁻¹ hg'
    let M : Matrix n n R := Matrix.of r
    let M' : Matrix n n R := Matrix.of r'
    have hM : M.map (algebraMap R A) = (g : Matrix n n A) := by
      ext i j; simp [M, hr]
    have hM' : M'.map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j; simp [M', hr']
    have h1 : M * M' = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.mul_inv g
    have h2 : M' * M = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.inv_mul g
    refine ⟨⟨M, M', h1, h2⟩, ?_⟩
    ext : 1
    rw [coe_bc]
    exact hM
  · rintro ⟨u, rfl⟩
    intro x
    constructor
    · intro hx
      rw [coe_bc]
      exact map_mulVec_mem_stdLat _ x hx
    · intro hx
      have hinv := map_mulVec_mem_stdLat (A := A) ((u⁻¹ : GL n R) : Matrix n n R) _ hx
      rw [← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.one_mulVec] at hinv
      exact hinv

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
namespace Formalism.UG.P

open Matrix

theorem sigex_cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  first
    | rfl
    | (ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply])

noncomputable def scal {n : Type} (ev : n → ℝ) : n → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)

theorem star_scal {n : Type} (ev : n → ℝ) : star (scal ev) = scal ev := by
  funext i
  simp only [Pi.star_apply, scal]
  exact Complex.conj_ofReal _

theorem scal_sq {n : Type} (ev : n → ℝ) (i : n) :
    scal ev i * (ev i : ℂ) * scal ev i = ((ev i / |ev i| : ℝ) : ℂ) := by
  have key : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = ev i / |ev i| := by
    set t := Real.sqrt |ev i| with ht
    have hs : t * t = |ev i| := Real.mul_self_sqrt (abs_nonneg _)
    rw [div_eq_mul_inv, ← hs]
    ring
  simp only [scal]
  rw [← key]
  push_cast
  ring

theorem herm_diag {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) :
    ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues))ᴴ * J *
        ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues)) =
      diagonal (fun i => ((hJ.eigenvalues i / |hJ.eigenvalues i| : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_scal]
  have hU : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hJ.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hJ.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (RCLike.ofReal ∘ hJ.eigenvalues) := by
    have h1 := congrArg (fun M => ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * M *
      (hJ.eigenvectorUnitary : Matrix n n ℂ)) hJ.spectral_theorem
    first
      | simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h1
      | simp only [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  calc _ = diagonal (scal hJ.eigenvalues) * (((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (scal hJ.eigenvalues) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact scal_sq _ i

theorem eig_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hdet : IsUnit J.det) (i : n) : hJ.eigenvalues i ≠ 0 := by
  intro h0
  apply hdet.ne_zero
  rw [hJ.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])

theorem sign_pos {x : ℝ} (h : 0 < x) : x / |x| = 1 := by
  rw [abs_of_pos h, div_self h.ne']

theorem sign_neg {x : ℝ} (h : x < 0) : x / |x| = -1 := by
  rw [abs_of_neg h, div_neg, div_self h.ne]

theorem signature_exists : Formalism.UG.SigExists := by
  unfold Formalism.UG.SigExists
  intro n _ _ J hJ hdet
  unfold Formalism.UG.IsHerm at hJ
  unfold Formalism.UG.HasSignature
  unfold Formalism.UG.Jpq
  have hH : J.IsHermitian := (sigex_cT_conj_eq J).symm.trans hJ
  have hU : ((hH.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ,
      Q = (hH.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hH.eigenvalues) := ⟨_, rfl⟩
  have hQ : Qᴴ * J * Q = diagonal (fun i => ((hH.eigenvalues i / |hH.eigenvalues i| : ℝ) : ℂ)) := by
    rw [hQdef]
    exact herm_diag hH
  obtain ⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card {i // 0 < hH.eigenvalues i}) ⊕
      Fin (Fintype.card {i // ¬ 0 < hH.eigenvalues i}),
      e = (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans
        (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)) := ⟨_, rfl⟩
  have hinl : ∀ a, e.symm (Sum.inl a) =
      ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hinr : ∀ a, e.symm (Sum.inr a) =
      ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hdetQ : IsUnit (reindex e e Q).det := by
    rw [Matrix.det_reindex_self, hQdef, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (Matrix.isUnit_det_of_left_inverse hU) ?_
    rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    have h1 : hH.eigenvalues i ≠ 0 := eig_ne_zero hH hdet i
    simp only [scal, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.mpr (abs_pos.mpr h1)).ne'
  refine ⟨_, _, e, Matrix.nonsingInvUnit _ hdetQ, ?_⟩
  change Formalism.UG.cT (starRingEnd ℂ) (reindex e e Q) * reindex e e J * reindex e e Q = _
  rw [sigex_cT_conj_eq]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hQ, Matrix.submatrix_diagonal_equiv]
  ext (a | a) (b | b)
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Function.comp_apply, hinl,
      Sum.inl.injEq, Matrix.one_apply]
    split_ifs
    · rw [sign_pos ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a).2, Complex.ofReal_one]
    · rfl
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Function.comp_apply, hinr,
      Sum.inr.injEq, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · have hx := ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a).2
      have hneg : hH.eigenvalues ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) < 0 :=
        lt_of_le_of_ne (not_lt.mp hx) (eig_ne_zero hH hdet _)
      rw [sign_neg hneg]
      push_cast
      ring
    · simp

end Formalism.UG.P
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem out_smul (K : Subgroup G) (c : G) (x : G ⧸ K) :
    ∃ κ : K, (c • x).out = c * x.out * (κ : G) := by
  have h : ((c * x.out : G) : G ⧸ K) = ((c • x).out : G ⧸ K) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [MulAction.Quotient.smul_mk]
    rfl
  refine ⟨⟨_, QuotientGroup.eq.1 h⟩, ?_⟩
  simp only [mul_inv_cancel_left]

theorem finsum_out_mul {M : Type} [AddCommMonoid M] (K : Subgroup G) (a : G) (F : G → M)
    (hF : ∀ (g : G) (c : K), F (g * c) = F g) :
    ∑ᶠ z : G ⧸ K, F (a * z.out) = ∑ᶠ y : G ⧸ K, F y.out := by
  have h : ∀ z : G ⧸ K, F (a * z.out) = F (a • z).out := by
    intro z
    obtain ⟨κ, hκ⟩ := out_smul K a z
    rw [hκ, hF]
  rw [finsum_congr h]
  exact finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun y => F y.out)

theorem finite_supp {k : Type} [CommRing k] (K : Subgroup G) (hK : IsCommensurated K)
    (f : G → k) (hf : f ∈ Hecke k K) : {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  obtain ⟨-, S, hS⟩ := hf'
  unfold IsCommensurated at hK
  have hfin : ∀ s : G, (Set.range fun k : K => ((↑k * s : G) : G ⧸ K)).Finite := by
    intro s
    let H : Subgroup K := (Subgroup.map (MulAut.conj s).toMonoidHom K).subgroupOf K
    haveI : H.FiniteIndex := ⟨hK s⟩
    haveI : Finite (K ⧸ H) := inferInstance
    let φ : K ⧸ H → G ⧸ K := Quotient.lift (fun k : K => ((↑k * s : G) : G ⧸ K)) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
      have h2 : ((a⁻¹ * b : K) : G) ∈ Subgroup.map (MulAut.conj s).toMonoidHom K :=
        Subgroup.mem_subgroupOf.1 hab'
      obtain ⟨c, hc, hcab⟩ := Subgroup.mem_map.1 h2
      have e : (a : G)⁻¹ * b = s * c * s⁻¹ := by
        rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← hcab]
        rfl
      apply QuotientGroup.eq.2
      have : ((a : G) * s)⁻¹ * ((b : G) * s) = c := by
        calc ((a : G) * s)⁻¹ * ((b : G) * s) = s⁻¹ * ((a : G)⁻¹ * b) * s := by group
          _ = c := by rw [e]; group
      rw [this]
      exact hc)
    refine (Set.finite_range φ).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : K ⧸ H), rfl⟩
  refine (S.finite_toSet.biUnion fun s _ => hfin s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' x]
  apply QuotientGroup.eq.2
  rw [hab]
  have : ((a : G) * s)⁻¹ * ((a : G) * s * b) = b := by group
  rw [this]
  exact b.2

theorem amf_right {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    {Γ K : Subgroup G} {ρ : Representation k Γ W} {φ : G → W} (hφ : φ ∈ AMF k Γ K ρ)
    (g : G) (c : K) : φ (g * c) = φ g := by
  have h : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  simpa using h 1 g c

theorem hecke_act_mem : Formalism.UG.HeckeActMem := by
  intro G _ Γ K k _ W _ _ ρ hK f hf φ hφ
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  have hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g := hf'.1
  have hφ' : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  have hfin := finite_supp K hK f hf
  show ∀ (γ : Γ) (g : G) (κ : K), hAct K f φ (↑γ * g * ↑κ) = ρ γ (hAct K f φ g)
  intro γ g κ
  simp only [hAct]
  have step1 : ∀ x : G ⧸ K, f x.out • φ (↑γ * g * ↑κ * x.out) =
      ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) := by
    intro x
    obtain ⟨κ', hκ'⟩ := out_smul K (κ : G) x
    have h1 : x.out = (κ : G)⁻¹ * ((κ : G) • x).out * (κ' : G)⁻¹ := by rw [hκ']; group
    have e1 : f x.out = f ((κ : G) • x).out := by
      rw [h1]
      have := hbi κ⁻¹ κ'⁻¹ ((κ : G) • x).out
      simpa using this
    have e2 : φ (↑γ * g * ↑κ * x.out) = ρ γ (φ (g * ((κ : G) • x).out)) := by
      have : (↑γ : G) * g * ↑κ * x.out = ↑γ * (g * ((κ : G) • x).out) * ↑(κ'⁻¹) := by
        rw [h1, Subgroup.coe_inv]
        group
      rw [this, hφ']
    rw [e1, e2, map_smul]
  rw [finsum_congr step1]
  have hre : ∑ᶠ x : G ⧸ K, ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) =
      ∑ᶠ y : G ⧸ K, ρ γ (f y.out • φ (g * y.out)) :=
    finsum_comp_equiv (MulAction.toPerm (κ : G) : Equiv.Perm (G ⧸ K))
      (f := fun y => ρ γ (f y.out • φ (g * y.out)))
  rw [hre]
  have hsupp : (Function.support fun y : G ⧸ K => f y.out • φ (g * y.out)).Finite :=
    hfin.subset fun y hy => by
      intro h0
      exact hy (by simp [h0])
  exact (map_finsum (ρ γ) hsupp).symm

private theorem finite_support_left_translate_of_biinvariant {k : Type} [CommRing k] (K : Subgroup G) (f : G → k)
    (hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g) (hfin : {x : G ⧸ K | f x.out ≠ 0}.Finite)
    (a : G) : {x : G ⧸ K | f (a * x.out) ≠ 0}.Finite := by
  refine (hfin.preimage (f := fun x : G ⧸ K => a • x)
    fun _ _ _ _ h => MulAction.injective a h).subset ?_
  intro x hx
  show f (a • x).out ≠ 0
  obtain ⟨κ, hκ⟩ := out_smul K a x
  rw [hκ]
  have e : f (a * x.out * ↑κ) = f (a * x.out) := by simpa using hbi 1 κ (a * x.out)
  rw [e]
  exact hx

theorem hecke_act_mul : Formalism.UG.HeckeActMul := by
  intro G _ Γ K k _ W _ _ ρ hK f₁ hf₁ f₂ hf₂ φ hφ
  have hbi₂ : ∀ (a b : K) (g : G), f₂ (↑a * g * ↑b) = f₂ g :=
    (show IsBiInv K f₂ ∧ FinDosetSupp K f₂ from hf₂).1
  have hfin₁ := finite_supp K hK f₁ hf₁
  have hfin₂ := finite_supp K hK f₂ hf₂
  funext g
  simp only [hAct, conv]
  have hA : ∀ y : G ⧸ K, ∑ᶠ z : G ⧸ K, f₂ z.out • φ (g * y.out * z.out) =
      ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    intro y
    have := finsum_out_mul K y.out (fun h => f₂ (y.out⁻¹ * h) • φ (g * h)) (by
      intro h c
      show f₂ (y.out⁻¹ * (h * ↑c)) • φ (g * (h * ↑c)) = f₂ (y.out⁻¹ * h) • φ (g * h)
      rw [(by simp [mul_assoc] : y.out⁻¹ * (h * ↑c) = ↑(1 : K) * (y.out⁻¹ * h) * ↑c), hbi₂,
        (by rw [mul_assoc] : g * (h * ↑c) = g * h * ↑c), amf_right hφ])
    simpa [mul_assoc] using this
  simp_rw [hA]
  set A := hfin₁.toFinset with hAdef
  have hB : ∀ y : G ⧸ K, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}.Finite :=
    fun y => finite_support_left_translate_of_biinvariant K f₂ hbi₂ hfin₂ y.out⁻¹
  have hX : (⋃ y ∈ A, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}).Finite :=
    A.finite_toSet.biUnion fun y _ => hB y
  set X := hX.toFinset with hXdef
  have hAsub : ∀ y : G ⧸ K, f₁ y.out ≠ 0 → y ∈ A := fun y hy => hfin₁.mem_toFinset.2 hy
  have hXsub : ∀ y x : G ⧸ K, f₁ y.out ≠ 0 → f₂ (y.out⁻¹ * x.out) ≠ 0 → x ∈ X := by
    intro y x h1 h2
    rw [hX.mem_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 (hAsub y h1)) h2
  have hL : ∀ x : G ⧸ K, ∑ᶠ y : G ⧸ K, f₁ y.out * f₂ (y.out⁻¹ * x.out) =
      ∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out) := by
    intro x
    apply finsum_eq_sum_of_support_subset
    intro y hy
    exact hAsub y (left_ne_zero_of_mul hy)
  simp_rw [hL]
  have eL : ∑ᶠ x : G ⧸ K, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) =
      ∑ x ∈ X, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) := by
    apply finsum_eq_sum_of_support_subset
    intro x hx
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_smul hx)
    exact hXsub y x (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)
  have eR : ∑ᶠ y : G ⧸ K, f₁ y.out • ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) =
      ∑ y ∈ A, f₁ y.out • ∑ x ∈ X, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    rw [finsum_eq_sum_of_support_subset (s := A) _ (fun y hy => hAsub y (left_ne_zero_of_smul hy))]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [finsum_eq_sum_of_support_subset (s := X) _
      (fun x hx => hXsub y x (hfin₁.mem_toFinset.1 hy) (left_ne_zero_of_smul hx))]
  rw [eL, eR]
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

end Formalism.UG.P
end
end

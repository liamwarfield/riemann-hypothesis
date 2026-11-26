module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.DenseSurj
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

def ball {l : ℕ} [Fact l.Prime] (K : FinExt l) : Subring ↥K.1 where
  carrier := {x | ‖((x : ↥K.1) : Om l)‖ ≤ 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, MulMemClass.coe_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, AddMemClass.coe_add] at *
    exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le ha hb)
  neg_mem' {a} ha := by simpa using ha

def PlaceProp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (φ : E →+* Om l),
    ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧
      ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal)

def KerProp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (φ : E →+* Om l)
    (v : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l →
    (∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal)) →
    ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ ‖((l : ℕ) : Om l)‖ ↔ x ∈ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ

def NormCard : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)),
    v ∈ placesOver E l →
    Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) = l ^ Formalism.MainNotions.N.locDeg E v

def BallCard : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    Nat.card (↥(ball K) ⧸ Ideal.span {((l : ℕ) : ↥(ball K))}) = l ^ finrank ℚ_[l] ↥K.1

def DenseSurj : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (φ : E →+* Om l) (K : FinExt l),
    (∀ x : E, φ x ∈ K.1) → ((K.1 : Set (Om l)) ⊆ closure (Set.range φ)) →
    ∀ y : Om l, y ∈ K.1 → ‖y‖ ≤ 1 → ∃ x : 𝓞 E, ‖y - φ (x : E)‖ ≤ ‖((l : ℕ) : Om l)‖

def LocDegOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (φ : E →+* Om l) (K : FinExt l),
    (∀ x : E, φ x ∈ K.1) → ((K.1 : Set (Om l)) ⊆ closure (Set.range φ)) →
    ∀ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l →
    (∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal)) →
    finrank ℚ_[l] ↥K.1 = Formalism.MainNotions.N.locDeg E v

end PI.CompDegEF
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem norm_natCast_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

theorem norm_natCast_pos (l : ℕ) [hl : Fact l.Prime] : 0 < ‖((l : ℕ) : Om l)‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast hl.out.pos)

theorem norm_le_one_of_integer {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (x : 𝓞 E) : ‖φ (x : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (Om l) NNReal)
  have h1 : IsIntegral ℤ (φ (x : E)) := (RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom
  have h2 : IsIntegral (Valued.v : Valuation (Om l) NNReal).integer (φ (x : E)) := h1.tower_top
  have h3 := (hv.isIntegral_iff_v_le_one).1 h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

def plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    Ideal (𝓞 E) where
  carrier := {x | ‖φ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    change ‖φ (algebraMap (𝓞 E) E b)‖ < 1 at hb
    rw [map_add (f := _), map_add (f := _)]
    exact lt_of_le_of_lt (PadicAlgCl.isNonarchimedean l _ _) (max_lt ha hb)
  smul_mem' c {a} ha := by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_integer φ c)) ha

theorem mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l)
    (x : 𝓞 E) : x ∈ plIdeal φ ↔ ‖φ (x : E)‖ < 1 := Iff.rfl

theorem natCast_mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : ((l : ℕ) : 𝓞 E) ∈ plIdeal φ := by
  rw [mem_plIdeal]
  simpa using norm_natCast_lt_one l

theorem plIdeal_isPrime {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : (plIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have : (1 : 𝓞 E) ∈ plIdeal φ := h ▸ Submodule.mem_top
    rw [mem_plIdeal] at this
    simp at this
  · intro a b hab
    simp only [mem_plIdeal, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at hab ⊢
    by_contra! h
    exact (not_le_of_gt hab) (by
      simpa only [one_mul] using mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _))

theorem plIdeal_ne_bot {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : plIdeal φ ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_plIdeal (E := E) φ
  rw [h, Ideal.mem_bot] at h1
  have : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact hl.out.ne_zero (by exact_mod_cast this)

def plOf {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    HeightOneSpectrum (𝓞 E) :=
  ⟨plIdeal φ, plIdeal_isPrime φ, plIdeal_ne_bot φ⟩

theorem placeProp : PlaceProp := by
  intro l _ E _ _ φ
  refine ⟨plOf φ, natCast_mem_plIdeal φ, fun x => ⟨norm_le_one_of_integer φ x, Iff.rfl⟩⟩

end PI.CompDegEF
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.SpanLIsMaximal
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem span_l_isMaximal (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := by
  refine Ideal.IsPrime.isMaximal ?_ ?_
  · exact (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  · simp [hl.out.ne_zero]

theorem liesOver_of_mem {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E l) :
    v.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  constructor
  refine (span_l_isMaximal l).eq_of_le ?_ ?_
  · intro h
    rw [Ideal.comap_eq_top_iff] at h
    exact v.isPrime.ne_top h
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change algebraMap ℤ (𝓞 E) ((l : ℕ) : ℤ) ∈ v.asIdeal
    simpa using (show ((l : ℕ) : 𝓞 E) ∈ v.asIdeal from hv)

theorem normCard : NormCard := by
  intro l _ E _ _ v hv
  have := liesOver_of_mem hv
  have hmax := span_l_isMaximal l
  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h1 : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Ideal.absNorm (v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h1, map_pow, Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver v.asIdeal
    (Ideal.span {((l : ℕ) : ℤ)}) hmax.isPrime (by simp [(Fact.out : l.Prime).ne_zero]),
    Ideal.absNorm_span_natCast, Module.finrank_self, pow_one,
    Ideal.inertiaDeg'_eq_inertiaDeg, Formalism.MainNotions.N.locDeg, ← pow_mul, mul_comm]

end PI.CompDegEF
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemSpanLIff
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem mem_span_l_iff {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) (y : ↥(ball K)) :
    y ∈ Ideal.span {((l : ℕ) : ↥(ball K))} ↔
      ‖((y : ↥K.1) : Om l)‖ ≤ ‖((l : ℕ) : Om l)‖ := by
  have hl0' : ((l : ℕ) : Om l) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  have hl0 : ((l : ℕ) : ↥K.1) ≠ 0 := by
    intro h
    apply hl0'
    have h' : (((l : ℕ) : ↥K.1) : Om l) = 0 := by rw [h]; rfl
    simpa using h'
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖((z : ↥K.1) : Om l)‖ ≤ 1 := z.2
    have hc : (((z * ((l : ℕ) : ↥(ball K)) : ↥(ball K)) : ↥K.1) : Om l) =
        ((z : ↥K.1) : Om l) * ((l : ℕ) : Om l) := by simp
    rw [hc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hz
  · intro h
    have hmem : ‖(((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
      have hc : (((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l) =
          ((y : ↥K.1) : Om l) / ((l : ℕ) : Om l) := by simp
      rw [hc, norm_div, div_le_one (norm_pos_iff.mpr hl0')]
      exact h
    refine ⟨⟨(y : ↥K.1) / ((l : ℕ) : ↥K.1), hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    push_cast
    exact div_mul_cancel₀ _ hl0

theorem locDegOf_of (hB : BallCard) (hD : DenseSurj) (hK : KerProp) (hN : NormCard) :
    LocDegOf := by
  intro l hl E _ _ φ K hφK hdense v hv hφv
  let ψ : 𝓞 E →+* ↥(ball K) :=
    { toFun := fun x => ⟨⟨φ (x : E), hφK _⟩, (hφv x).1⟩
      map_one' := Subtype.ext <| Subtype.ext <| by simp
      map_mul' := fun a b => Subtype.ext <| Subtype.ext <| by simp
      map_zero' := Subtype.ext <| Subtype.ext <| by simp
      map_add' := fun a b => Subtype.ext <| Subtype.ext <| by simp }
  let q := (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ↥(ball K))})).comp ψ
  have hsurj : Function.Surjective q := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hD l E φ K hφK hdense ((y : ↥K.1) : Om l) (y : ↥K.1).2 y.2
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ψ x) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq, mem_span_l_iff]
    have hc : (((ψ x - y : ↥(ball K)) : ↥K.1) : Om l) = φ (x : E) - ((y : ↥K.1) : Om l) := rfl
    rw [hc, norm_sub_rev]
    exact hx
  have hker : RingHom.ker q = v.asIdeal ^ v.asIdeal.ramificationIdx ℤ := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (ψ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_span_l_iff K (ψ x)).trans (hK l E φ v hv hφv x)
  have hcard : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Nat.card (↥(ball K) ⧸ Ideal.span {((l : ℕ) : ↥(ball K))}) := by
    rw [← hker]
    exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
  rw [hN l E v hv, hB l K] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm

end PI.CompDegEF
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

variable {l : ℕ} [hl : Fact l.Prime]

theorem algebraMap_padicInt_injective (K : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥K.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥K.1]
  exact (algebraMap ℚ_[l] ↥K.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

instance isTorsionFree_finExt (K : FinExt l) : Module.IsTorsionFree ℤ_[l] ↥K.1 where
  isSMulRegular r hr := fun x y h => by
    have hr0 : algebraMap ℤ_[l] ↥K.1 r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((map_eq_zero_iff _ (algebraMap_padicInt_injective K)).1 h0)
    change r • x = r • y at h
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ hr0 h

private theorem spectralValue_le_one_iff_norm_coeff_le_one (P : ℚ_[l][X]) (hP : P.Monic) :
    spectralValue P ≤ 1 ↔ ∀ n, ‖P.coeff n‖ ≤ 1 := by
  constructor
  · intro h n
    by_cases hn : n < P.natDegree
    · have ht : spectralValueTerms P n ≤ 1 :=
        (le_ciSup (spectralValueTerms_bddAbove P) n).trans h
      rw [spectralValueTerms, if_pos hn] at ht
      have hexp : (0 : ℝ) < 1 / ((P.natDegree : ℝ) - n) := by
        have : (n : ℝ) < P.natDegree := by exact_mod_cast hn
        apply div_pos one_pos; linarith
      by_contra hc
      push_neg at hc
      exact absurd ht (not_le.mpr (Real.one_lt_rpow hc hexp))
    · rcases eq_or_lt_of_le (not_lt.mp hn) with h' | h'
      · rw [← h', hP.coeff_natDegree, norm_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h', norm_zero]; exact zero_le_one
  · intro h
    unfold spectralValue
    apply ciSup_le
    intro n
    simp only [spectralValueTerms]
    split_ifs with hn
    · have : (n : ℝ) < P.natDegree := by exact_mod_cast hn
      exact Real.rpow_le_one (norm_nonneg _) (h n) (div_nonneg zero_le_one (by linarith))
    · exact zero_le_one

theorem norm_le_one_iff_isIntegral (z : Om l) : ‖z‖ ≤ 1 ↔ IsIntegral ℤ_[l] z := by
  have hzQ : IsIntegral ℚ_[l] z := by
    first
      | exact Algebra.IsIntegral.isIntegral z
      | exact (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hnorm : ‖z‖ = spectralValue (minpoly ℚ_[l] z) := rfl
  rw [hnorm, spectralValue_le_one_iff_norm_coeff_le_one _ (minpoly.monic hzQ)]
  constructor
  · intro h
    have hlift : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hqmap, -, hqm⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hzQ)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hqmap, minpoly.aeval]
  · intro hz n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hz, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

theorem mem_integralClosure_iff_mem_ball (K : FinExt l) (x : ↥K.1) :
    x ∈ integralClosure ℤ_[l] ↥K.1 ↔ x ∈ ball K := by
  rw [mem_integralClosure_iff]
  show IsIntegral ℤ_[l] x ↔ ‖((x : ↥K.1) : Om l)‖ ≤ 1
  rw [norm_le_one_iff_isIntegral]
  first
    | exact (isIntegral_algebraMap_iff (A := ↥K.1) (B := Om l) ).symm
    | exact (isIntegral_algHom_iff ((K.1.val).restrictScalars ℤ_[l]) K.1.val.injective).symm

theorem card_quot_l {C : Type} [CommRing C] [Algebra ℤ_[l] C] {n : ℕ} (b : Basis (Fin n) ℤ_[l] C) :
    Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = l ^ n := by
  let f : C →+ (Fin n → ZMod l) :=
    AddMonoidHom.pi fun i =>
      (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  have hf : ∀ x i, f x i = PadicInt.toZMod (b.repr x i) := fun x i => rfl
  have hsurj : Function.Surjective f := by
    intro w
    refine ⟨b.equivFun.symm (fun i => ((w i).val : ℤ_[l])), funext fun i => ?_⟩
    rw [hf]
    have h1 : b.repr (b.equivFun.symm (fun i => ((w i).val : ℤ_[l]))) i = ((w i).val : ℤ_[l]) := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [h1, map_natCast, ZMod.natCast_zmod_val]
  have hlC : ((l : ℕ) : C) = algebraMap ℤ_[l] C (l : ℤ_[l]) := (map_natCast _ _).symm
  have hk : (Ideal.span {((l : ℕ) : C)}).toAddSubgroup = f.ker := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      funext i
      show f (y * ((l : ℕ) : C)) i = 0
      rw [hf, hlC, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
        map_natCast, ZMod.natCast_self, zero_mul]
    · intro hx
      have hdiv : ∀ i, ∃ d : ℤ_[l], b.repr x i = (l : ℤ_[l]) * d := fun i => by
        have h0 : PadicInt.toZMod (b.repr x i) = 0 := congrFun hx i
        have hm : b.repr x i ∈ Ideal.span {((l : ℕ) : ℤ_[l])} := by
          rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
          exact RingHom.mem_ker.mpr h0
        exact (Ideal.mem_span_singleton'.mp hm).imp fun d hd => by rw [← hd, mul_comm]
      choose d hd using hdiv
      refine ⟨∑ i, d i • b i, ?_⟩
      rw [hlC, mul_comm, ← Algebra.smul_def, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd, smul_smul]
  have hcard : Nat.card (C ⧸ Ideal.span {((l : ℕ) : C)}) = Nat.card (C ⧸ f.ker) := by
    rw [← hk]; rfl
  rw [hcard, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ballCard : BallCard := by
  intro l _ K
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let S := integralClosure ℤ_[l] ↥K.1
  let e : ↥(ball K) ≃+* ↥S :=
    { toFun := fun x => ⟨x.1, (mem_integralClosure_iff_mem_ball K x.1).mpr x.2⟩
      invFun := fun y => ⟨y.1, (mem_integralClosure_iff_mem_ball K y.1).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hIJ : Ideal.span {((l : ℕ) : ↥S)} = (Ideal.span {((l : ℕ) : ↥(ball K))}).map e := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e hIJ).toEquiv]
  haveI : Module.Free ℤ_[l] S :=
    IsIntegralClosure.module_free (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)
  haveI : Module.Finite ℤ_[l] S :=
    IsIntegralClosure.finite (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)
  rw [card_quot_l (Module.finBasis ℤ_[l] S),
    IsIntegralClosure.rank (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)]

end PI.CompDegEF
end

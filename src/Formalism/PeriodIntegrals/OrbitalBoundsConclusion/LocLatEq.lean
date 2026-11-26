module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.LocLatEq
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ₁ Λ₂ : Submodule (𝓞 E) (Fin n → E)), Λ₁.FG → Λ₂.FG →
    (latL A Λ₁ = latL A Λ₂ ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
        ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₁) ↔ (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₂))

end PI.LocLatEq
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Imports
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

def IntP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    ∀ a : E, A.ιE a ∈ A.O → ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ b : 𝓞 E,
      ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) * a = b

end PI.LocLatEq.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Development
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

def UnitP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (d : 𝓞 F),
    d ∉ p.asIdeal → ∃ u ∈ A.O, u * A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = 1

def AvoidP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 E)),
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
      ¬ I ≤ P.asIdeal) →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d ∈ I

def CoreP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p)
    (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ y : Fin n → E, bc A y ∈ latL A Λ →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • y ∈ Λ

theorem bc_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (s : 𝓞 E) (x : Fin n → E) : bc A (s • x) = A.ιE (s : E) • bc A x := by
  funext i
  simp [bc, Algebra.smul_def]

theorem latL_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (hU : UnitP)
    (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ Λ, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • x ∈ Λ') :
    latL A Λ ≤ latL A Λ' := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd, hdx⟩ := h x hx
  obtain ⟨u, hu, hu1⟩ := hU F E sig p A d hd
  have hmem : ((⟨u, hu⟩ : A.O) • bc A (algebraMap (𝓞 F) (𝓞 E) d • x)) ∈ latL A Λ' :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdx, rfl⟩)
  have heq : (⟨u, hu⟩ : A.O) • bc A (algebraMap (𝓞 F) (𝓞 E) d • x) = bc A x := by
    rw [Subring.smul_def, bc_smul, smul_smul]
    simp only [hu1, one_smul]
  rw [SetLike.mem_coe, ← heq]
  exact hmem

theorem locLatEq_of (hU : UnitP) (hA : AvoidP) (hC : CoreP) : PI.LocLatEq.Stmt := by
  intro F E _ _ _ _ _ h2 sig p A n Λ₁ Λ₂ hf1 hf2
  constructor
  · intro heq P hP x
    have key : ∀ (Λ Λ' : Submodule (𝓞 E) (Fin n → E)), Λ'.FG → latL A Λ = latL A Λ' →
        (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) → (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ') := by
      rintro Λ Λ' hf' he ⟨s, hs, hsx⟩
      have hy : bc A (s • x) ∈ latL A Λ' := he ▸ Submodule.subset_span ⟨_, hsx, rfl⟩
      obtain ⟨d, hd, hdy⟩ := hC F E h2 sig p A n Λ' hf' (s • x) hy
      refine ⟨algebraMap (𝓞 F) (𝓞 E) d * s, ?_, by rwa [mul_smul]⟩
      intro hm
      rcases P.isPrime.mem_or_mem hm with h | h
      · apply hd
        rw [← hP]
        exact h
      · exact hs h
    exact ⟨key Λ₁ Λ₂ hf2 heq, key Λ₂ Λ₁ hf1 heq.symm⟩
  · intro h
    have side : ∀ (Λ Λ' : Submodule (𝓞 E) (Fin n → E)),
        (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
          ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) →
            (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ')) → latL A Λ ≤ latL A Λ' := by
      intro Λ Λ' hh
      apply latL_le A hU
      intro x hx
      apply hA F E p (Λ'.comap (LinearMap.toSpanSingleton (𝓞 E) _ x))
      intro P hP hle
      have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      obtain ⟨s, hs, hsx⟩ := hh P hP x ⟨1, h1, by simpa using hx⟩
      exact hs (hle (by simpa [LinearMap.toSpanSingleton_apply] using hsx))
    exact le_antisymm (side Λ₁ Λ₂ (fun P hP x => (h P hP x).1))
      (side Λ₂ Λ₁ (fun P hP x => (h P hP x).2))

end PI.LocLatEq.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.EpNontrivial
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem int_of_val (A : LocAt F E sig p) (x : F) (hx : A.ιF x ∈ 𝒪[A.Fp]) :
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * x = n := by
  rw [Valuation.mem_integer_iff] at hx
  have h1 : A.ιF x ≤ᵥ A.ιF 1 := by
    rw [map_one, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A.Fp), map_one]
    exact hx
  have hv : p.valuation F x ≤ 1 := by
    have := (A.val x 1).mp h1
    rwa [map_one] at this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p x hv
  refine ⟨d, d.2, n, ?_⟩
  rw [mul_comm]
  exact hnd

theorem ep_nontrivial (A : LocAt F E sig p) : Nontrivial A.Ep := by
  have := A.free
  exact Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)

theorem coeff_mem (h2 : Module.finrank F E = 2) (A : LocAt F E sig p) (a : E)
    (ha : IsIntegral 𝒪[A.Fp] (A.ιE a)) (hnot : a ∉ (algebraMap F E).range) (i : ℕ) :
    A.ιF ((minpoly F a).coeff i) ∈ 𝒪[A.Fp] := by
  classical
  haveI := ep_nontrivial A
  haveI := A.free
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    apply hnot
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hspanP : ⊤ ≤ Submodule.span A.Fp (Set.range ![(1 : A.Ep), A.ιE a]) := by
    rw [← A.span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx := B.sum_repr x
    rw [hB, Fin.sum_univ_two] at hx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
    have : A.ιE x = A.ιF (B.repr x 0) • (1 : A.Ep) + A.ιF (B.repr x 1) • A.ιE a := by
      conv_lhs => rw [← hx]
      simp only [map_add (f := _), map_mul, map_one, Algebra.smul_def, A.compat, mul_one]
    rw [SetLike.mem_coe, this]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  have hliP : LinearIndependent A.Fp ![(1 : A.Ep), A.ιE a] :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanP (by simp [A.rank])
  have hnotP : A.ιE a ∉ (algebraMap A.Fp A.Ep).range := by
    rintro ⟨c, hc⟩
    rw [LinearIndependent.pair_iff' one_ne_zero] at hliP
    apply hliP c
    rw [← hc, Algebra.algebraMap_eq_smul_one]
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  have hintP : IsIntegral A.Fp (A.ιE a) := Algebra.IsIntegral.isIntegral _
  have hdegP : 2 ≤ (minpoly A.Fp (A.ιE a)).natDegree := by
    have h0 := minpoly.natDegree_pos hintP
    have h1 : (minpoly A.Fp (A.ιE a)).natDegree ≠ 1 := fun h => hnotP (minpoly.natDegree_eq_one_iff.mp h)
    omega
  have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
  have hdegF : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  set g : A.Fp[X] := (minpoly F a).map A.ιF with hg
  have hgmon : g.Monic := (minpoly.monic hintF).map _
  have hgdeg : g.natDegree ≤ 2 := by
    rw [hg, natDegree_map]
    exact hdegF
  have hgα : aeval (A.ιE a) g = 0 := by
    rw [hg, aeval_def, eval₂_map]
    have hcomp : (algebraMap A.Fp A.Ep).comp A.ιF = A.ιE.comp (algebraMap F E) := by
      ext y
      simp [A.compat]
    rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hdvd : minpoly A.Fp (A.ιE a) ∣ g := minpoly.dvd A.Fp _ hgα
  have hgeq : g = minpoly A.Fp (A.ιE a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintP) hgmon hdvd (by omega)
  have hdvd2 : minpoly A.Fp (A.ιE a) ∣ (minpoly 𝒪[A.Fp] (A.ιE a)).map (algebraMap 𝒪[A.Fp] A.Fp) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, minpoly.aeval]
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd A.Fp (minpoly.monic ha) hdvd2
  rw [(minpoly.monic hintP).leadingCoeff, C_1, mul_one] at hg'
  have hc := congrArg (fun q => q.coeff i) (hg'.trans hgeq.symm)
  simp only [coeff_map, hg] at hc
  rw [← hc]
  exact (g'.coeff i).2

theorem intP : IntP := by
  intro F E _ _ _ _ _ h2 sig p A a ha
  rw [A.O_def] at ha
  have := ep_nontrivial A
  by_cases hr : a ∈ (algebraMap F E).range
  · obtain ⟨f, rfl⟩ := hr
    have hf : A.ιF f ∈ 𝒪[A.Fp] := by
      rw [A.compat] at ha
      have hi : IsIntegral 𝒪[A.Fp] (A.ιF f) :=
        (isIntegral_algebraMap_iff ).mp ha
      exact (Valuation.integer.integers _).mem_of_integral hi
    obtain ⟨d, hd, n, hn⟩ := int_of_val A f hf
    refine ⟨d, hd, algebraMap (𝓞 F) (𝓞 E) n, ?_⟩
    change algebraMap F E (d : F) * algebraMap F E f = algebraMap F E (n : F)
    rw [← map_mul, hn]
  · have hc : ∀ i, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * (minpoly F a).coeff i = n :=
      fun i => int_of_val A _ (coeff_mem h2 A a ha hr i)
    obtain ⟨d0, hd0, n0, hn0⟩ := hc 0
    obtain ⟨d1, hd1, n1, hn1⟩ := hc 1
    have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
    have hdeg : (minpoly F a).natDegree = 2 := by
      have h1 : (minpoly F a).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.mp h)
      have h0 := minpoly.natDegree_pos hintF
      have := minpoly.natDegree_le (A := F) a
      rw [h2] at this
      omega
    have hlead : (minpoly F a).coeff 2 = 1 := by
      have := (minpoly.monic hintF).leadingCoeff
      rwa [leadingCoeff, hdeg] at this
    have hrel : algebraMap F E ((minpoly F a).coeff 0) + algebraMap F E ((minpoly F a).coeff 1) * a
        + a ^ 2 = 0 := by
      have := minpoly.aeval F a
      rw [aeval_eq_sum_range' (n := 3) (by omega)] at this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlead, Algebra.smul_def,
        map_one, pow_zero, pow_one, one_mul, mul_one, zero_add] at this
      linear_combination this
    have hd : d0 * d1 ∉ p.asIdeal := fun h => (p.isPrime.mem_or_mem h).elim hd0 hd1
    have hint : IsIntegral (𝓞 F) (algebraMap F E ((d0 * d1 : 𝓞 F) : F) * a) := by
      refine ⟨X ^ 2 + C (d0 * n1) * X + C (d0 * d1 * d1 * n0), by monicity!, ?_⟩
      simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
      have e0 := congrArg (algebraMap F E) hn0
      have e1 := congrArg (algebraMap F E) hn1
      simp only [map_mul] at e0 e1
      simp only [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_mul] at *
      change _ = algebraMap F E (n0 : F) at e0
      linear_combination (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) ^ 2 * hrel
        - (algebraMap F E (d0 : F) * (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) * a) * e1
        - (algebraMap F E (d0 : F) * algebraMap F E (d1 : F) ^ 2) * e0
    obtain ⟨b, hb⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := 𝓞 F) (B := E) |>.mp hint
    refine ⟨d0 * d1, hd, b, ?_⟩
    rw [show ((b : 𝓞 E) : E) = algebraMap (𝓞 E) E b from rfl, hb]
    rfl

end PI.LocLatEq.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreFgOfLe
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreGenIdeal
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem core_gen_ideal (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (𝔞 : Ideal (𝓞 E)) :
    ∃ a ∈ 𝔞, ∀ b ∈ 𝔞, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d * b = r * a := by
  classical
  by_cases h𝔞 : 𝔞 = ⊥
  · refine ⟨0, 𝔞.zero_mem, fun b hb => ⟨1, ?_, 0, ?_⟩⟩
    · exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · rw [h𝔞, Ideal.mem_bot] at hb
      simp [hb]
  have h𝔞0 : 𝔞 ≠ 0 := h𝔞
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hpE0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]
    exact p.ne_bot
  have hle : 𝔞 * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ 𝔞 :=
    Ideal.mul_le_inf.trans inf_le_left
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle (mul_ne_zero h𝔞0 hpE0)
  have haa : a ∈ 𝔞 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨𝔠, h𝔠⟩ : 𝔞 ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haa)
  have hav : ∀ P : HeightOneSpectrum (𝓞 E),
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ¬ 𝔠 ≤ P.asIdeal := by
    intro P hP hcP
    have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ P.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr hP.ge
    have h2 : 𝔞 ≤ 𝔞 * P.asIdeal := by
      conv_lhs => rw [← ha]
      refine sup_le (Ideal.mul_mono_right h1) ?_
      rw [h𝔠]
      exact Ideal.mul_mono_right hcP
    have h3 : 𝔞 * P.asIdeal ∣ 𝔞 * 1 := by
      rw [mul_one]
      exact Ideal.dvd_iff_le.mpr h2
    have h4 := (mul_dvd_mul_iff_left h𝔞0).mp h3
    exact P.isPrime.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one h4))
  obtain ⟨d, hdp, hd⟩ := hA F E p 𝔠 hav
  refine ⟨a, haa, fun b hb => ⟨d, hdp, ?_⟩⟩
  have hmem : algebraMap (𝓞 F) (𝓞 E) d * b ∈ Ideal.span {a} := by
    rw [h𝔠, mul_comm (algebraMap (𝓞 F) (𝓞 E) d) b]
    exact Ideal.mul_mem_mul hb hd
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨r, hr.symm⟩

theorem core_gen (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (I : Submodule (𝓞 E) E)
    (hI : I.FG) : ∃ a ∈ I, ∀ b ∈ I, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d • b = r • a := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) S
  have hc0 : algebraMap (𝓞 E) E (c : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero c)
  have hint : ∀ x ∈ Submodule.span (𝓞 E) (S : Set E),
      ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (c : 𝓞 E) • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hc x hx
      exact ⟨y, hy⟩
    | zero => exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨y1, h1⟩ := hx
      obtain ⟨y2, h2⟩ := hz
      exact ⟨y1 + y2, by rw [map_add (f := _), h1, h2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨y, h⟩ := hx
      refine ⟨r * y, ?_⟩
      rw [map_mul, h]
      simp only [Algebra.smul_def]
      ring
  obtain ⟨a0, ha0, hgen⟩ := core_gen_ideal (F := F) hA p
    ((Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹))
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at ha0
  refine ⟨a0 • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹, ha0, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := hint b hb
  have hyb : y • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹ = b := by
    rw [Algebra.smul_def, hy, Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0,
      one_mul]
  have hy𝔞 : y ∈ (Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹) := by
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hyb]
    exact hb
  obtain ⟨d, hd, r, hr⟩ := hgen y hy𝔞
  refine ⟨d, hd, r, ?_⟩
  rw [← hyb, smul_smul, smul_smul, hr]

end PI.LocLatEq.W
end
end

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

theorem core_fg_of_le {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M]
    [Module R M] {N P : Submodule R M} (hN : N.FG) (h : P ≤ N) : P.FG := by
  have : IsNoetherian R N := isNoetherian_of_fg_of_noetherian N hN
  have h1 : (P.comap N.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map N.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at h2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem core_int_mem (A : LocAt F E sig p) (r : 𝓞 E) : A.ιE (r : E) ∈ A.O := by
  rw [A.O_def]
  exact ((RingOfIntegers.isIntegral_coe r).map A.ιE.toIntAlgHom).tower_top

theorem core_nontriv (A : LocAt F E sig p) : Nontrivial A.Ep := by
  by_contra h
  have : Subsingleton A.Ep := not_nontrivial_iff_subsingleton.1 h
  have h2 := A.rank
  rw [Module.finrank_zero_of_subsingleton] at h2
  omega

theorem core_bc_sub (A : LocAt F E sig p) {n : ℕ} (x y : Fin n → E) :
    bc A (x - y) = bc A x - bc A y := by
  funext i
  exact map_sub A.ιE (x i) (y i)

theorem core_smem (A : LocAt F E sig p) {n : ℕ} (S : Submodule A.O (Fin n → A.Ep)) {o : A.Ep}
    (ho : o ∈ A.O) {x : Fin n → A.Ep} (hx : x ∈ S) : o • x ∈ S :=
  S.smul_mem (⟨o, ho⟩ : A.O) hx

private theorem ringOfIntegers_smul_eq_coe_mul (r : 𝓞 E) (x : E) : r • x = (r : E) * x :=
  Algebra.smul_def r x

private theorem locLatEq_bc_apply (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ} (x : Fin n → E)
    (i : Fin n) : PI.LocLatEq.bc A x i = A.ιE (x i) := rfl

private theorem locLatEq_bc_mem_latL_of_mem (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ Λ) :
    PI.LocLatEq.bc A x ∈ PI.LocLatEq.latL A Λ := by
  unfold PI.LocLatEq.latL
  exact Submodule.subset_span ⟨x, hx, rfl⟩

private theorem mul_not_mem_asIdeal_of_not_mem {d d' : 𝓞 F} (hd : d ∉ p.asIdeal) (hd' : d' ∉ p.asIdeal) :
    d * d' ∉ p.asIdeal := fun h => (p.isPrime.mem_or_mem h).elim hd hd'

private theorem exists_linearMap_eq_cons_zero (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) : ∃ L : (Fin n → M) →ₗ[R] (Fin (n + 1) → M),
      ∀ v, L v = (Fin.cons (0 : M) v : Fin (n + 1) → M) :=
  ⟨{ toFun := fun v => (Fin.cons (0 : M) v : Fin (n + 1) → M)
     map_add' := fun v w => by
       funext i
       cases i using Fin.cases <;> simp
     map_smul' := fun c v => by
       funext i
       cases i using Fin.cases <;> simp }, fun _ => rfl⟩


set_option maxHeartbeats 800000 in
theorem core_ind (hU : UnitP) (hA : AvoidP) (hI : IntP) (h2 : Module.finrank F E = 2)
    (A : LocAt F E sig p) : ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG →
    ∀ y : Fin n → E, bc A y ∈ latL A Λ →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • y ∈ Λ := by
  have := core_nontriv A
  intro n
  induction n with
  | zero =>
    intro Λ _ y _
    refine ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    have hy0 : y = 0 := funext fun i => i.elim0
    rw [hy0, smul_zero]
    exact Λ.zero_mem
  | succ n ih =>
    intro Λ hΛ y hy
    obtain ⟨L, hL⟩ := exists_linearMap_eq_cons_zero (𝓞 E) E n
    have hinj : Function.Injective L := fun v w h => funext fun j => by
      simpa [hL] using congrFun h j.succ
    have hmapFG : (Submodule.map L (Λ.comap L)).FG :=
      core_fg_of_le hΛ (Submodule.map_comap_le L Λ)
    have hFG : (Λ.comap L).FG := Submodule.fg_of_fg_map_injective L hinj hmapFG
    obtain ⟨a, haI, hgen⟩ := core_gen hA p
      (Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin (n + 1) => E) 0)) (hΛ.map _)
    have hx0 : ∀ x ∈ Λ,
        x 0 ∈ Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin (n + 1) => E) 0) :=
      fun x hx => Submodule.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨l1, hl1, hl1a⟩ := Submodule.mem_map.1 haI
    obtain ⟨l0, hl0, hl0a, hl0z⟩ : ∃ l0 ∈ Λ, l0 0 = a ∧ (a = 0 → l0 = 0) := by
      by_cases ha0 : a = 0
      · exact ⟨0, Λ.zero_mem, by simp [ha0], fun _ => rfl⟩
      · exact ⟨l1, hl1, hl1a, fun h => absurd h ha0⟩
    have hdec : ∀ v ∈ PI.LocLatEq.latL A Λ, ∃ c ∈ A.O, ∃ w ∈ PI.LocLatEq.latL A (Λ.comap L),
        v = c • PI.LocLatEq.bc A l0 + (Fin.cons (0 : A.Ep) w : Fin (n + 1) → A.Ep) := by
      intro v hv
      unfold PI.LocLatEq.latL at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨d, hd, r, hr⟩ := hgen (l 0) (hx0 l hl)
        obtain ⟨u, hu, hud⟩ := hU F E sig p A d hd
        obtain ⟨m, hm⟩ : ∃ m : Fin (n + 1) → E, m = algebraMap (𝓞 F) (𝓞 E) d • l - r • l0 :=
          ⟨_, rfl⟩
        have hm0 : m 0 = 0 := by
          rw [hm, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hl0a, hr, sub_self]
        have hmc : (Fin.cons (0 : E) (Fin.tail m) : Fin (n + 1) → E) = m := by
          rw [← hm0, Fin.cons_self_tail]
        have hmt : Fin.tail m ∈ Λ.comap L := by
          rw [Submodule.mem_comap, hL, hmc, hm]
          exact Λ.sub_mem (Λ.smul_mem _ hl) (Λ.smul_mem _ hl0)
        have hr' : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) * l 0 = (r : E) * a := by
          simpa only [ringOfIntegers_smul_eq_coe_mul] using hr
        refine ⟨u * A.ιE (r : E), A.O.mul_mem hu (core_int_mem A r),
          u • PI.LocLatEq.bc A (Fin.tail m),
          core_smem A (PI.LocLatEq.latL A (Λ.comap L)) hu
            (locLatEq_bc_mem_latL_of_mem A _ hmt), ?_⟩
        funext i
        cases i using Fin.cases with
        | zero =>
          simp only [locLatEq_bc_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
            add_zero, hl0a]
          have h1 := congrArg A.ιE hr'
          rw [map_mul, map_mul] at h1
          linear_combination (-(A.ιE (l 0))) * hud + u * h1
        | succ j =>
          simp only [locLatEq_bc_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_succ,
            Fin.tail, hm, Pi.sub_apply, ringOfIntegers_smul_eq_coe_mul, map_sub, map_mul]
          linear_combination (-(A.ιE (l j.succ))) * hud
      | zero =>
        refine ⟨0, A.O.zero_mem, 0, Submodule.zero_mem _, ?_⟩
        funext i
        cases i using Fin.cases <;> simp
      | add x y _ _ hx hy =>
        obtain ⟨c1, hc1, w1, hw1, rfl⟩ := hx
        obtain ⟨c2, hc2, w2, hw2, rfl⟩ := hy
        refine ⟨c1 + c2, A.O.add_mem hc1 hc2, w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
        funext i
        cases i using Fin.cases <;>
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.cons_succ,
            add_zero] <;> ring
      | smul o x _ hx =>
        obtain ⟨c, hc, w, hw, rfl⟩ := hx
        refine ⟨(o : A.Ep) * c, A.O.mul_mem o.2 hc, o • w, Submodule.smul_mem _ o hw, ?_⟩
        funext i
        cases i using Fin.cases <;>
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Subring.smul_def, Fin.cons_zero,
            Fin.cons_succ, add_zero] <;> ring
    have htail : ∀ v ∈ PI.LocLatEq.latL A Λ, v 0 = 0 →
        Fin.tail v ∈ PI.LocLatEq.latL A (Λ.comap L) := by
      intro v hv hv0
      obtain ⟨c, hc, w, hw, rfl⟩ := hdec v hv
      have hca : c * A.ιE a = 0 := by
        have h0 := hv0
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, add_zero,
          locLatEq_bc_apply, hl0a] at h0
        exact h0
      have hzero : c • PI.LocLatEq.bc A l0 = 0 := by
        by_cases ha0 : a = 0
        · rw [hl0z ha0]
          funext i
          simp [locLatEq_bc_apply]
        · have hc0 : c = c * A.ιE a * A.ιE a⁻¹ := by
            rw [mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, mul_one]
          rw [hca, zero_mul] at hc0
          rw [hc0, zero_smul]
      rw [hzero, zero_add, Fin.tail_cons]
      exact hw
    obtain ⟨c, hc, w, hw, hyd⟩ := hdec _ hy
    have hy0 : A.ιE (y 0) = c * A.ιE a := by
      have h0 := congrFun hyd 0
      simp only [locLatEq_bc_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
        add_zero, hl0a] at h0
      exact h0
    obtain ⟨t, ht, hta⟩ : ∃ t : E, A.ιE t ∈ A.O ∧ y 0 = t * a := by
      by_cases ha0 : a = 0
      · refine ⟨0, by rw [map_zero]; exact A.O.zero_mem, ?_⟩
        rw [ha0, map_zero, mul_zero] at hy0
        rw [zero_mul]
        exact A.ιE.injective (by rw [hy0, map_zero])
      · refine ⟨y 0 * a⁻¹, ?_, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
        rw [map_mul, hy0, mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, mul_one]
        exact hc
    obtain ⟨d1, hd1, b, hb⟩ := hI F E h2 sig p A t ht
    obtain ⟨z, hz⟩ : ∃ z : Fin (n + 1) → E, z = algebraMap (𝓞 F) (𝓞 E) d1 • y - b • l0 :=
      ⟨_, rfl⟩
    have hz0 : z 0 = 0 := by
      rw [hz, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, ringOfIntegers_smul_eq_coe_mul, ringOfIntegers_smul_eq_coe_mul,
        hl0a, hta]
      linear_combination a * hb
    have hzL : PI.LocLatEq.bc A z ∈ PI.LocLatEq.latL A Λ := by
      rw [hz, core_bc_sub, bc_smul, bc_smul]
      exact Submodule.sub_mem _
        (core_smem A (PI.LocLatEq.latL A Λ) (core_int_mem A _) hy)
        (core_smem A (PI.LocLatEq.latL A Λ) (core_int_mem A b)
          (locLatEq_bc_mem_latL_of_mem A Λ hl0))
    have ht' : PI.LocLatEq.bc A (Fin.tail z) ∈ PI.LocLatEq.latL A (Λ.comap L) :=
      htail _ hzL (by rw [locLatEq_bc_apply, hz0, map_zero])
    obtain ⟨d2, hd2, hd2z⟩ := ih (Λ.comap L) hFG (Fin.tail z) ht'
    have hzc : (Fin.cons (0 : E) (Fin.tail z) : Fin (n + 1) → E) = z := by
      rw [← hz0, Fin.cons_self_tail]
    have hz2 : algebraMap (𝓞 F) (𝓞 E) d2 • z ∈ Λ := by
      have h := Submodule.mem_comap.1 hd2z
      rwa [map_smul, hL, hzc] at h
    have hy' : algebraMap (𝓞 F) (𝓞 E) d1 • y = z + b • l0 := by
      rw [hz, sub_add_cancel]
    refine ⟨d2 * d1, mul_not_mem_asIdeal_of_not_mem hd2 hd1, ?_⟩
    rw [map_mul, mul_smul, hy', smul_add, smul_smul]
    exact Λ.add_mem hz2 (Λ.smul_mem _ hl0)

theorem coreP_of_unitP_avoidP_intP (hU : UnitP) (hA : AvoidP) (hI : IntP) : CoreP := by
  intro F E _ _ _ _ _ h2 sig p A n Λ hΛ y hy
  exact core_ind hU hA hI h2 A n Λ hΛ y hy

end PI.LocLatEq.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.AvoidP
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

theorem unitP : UnitP := by
  intro F E _ _ _ _ _ sig p A d hd
  have hv1 : p.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) p).2 hd
  have h1 : A.ιF (algebraMap (𝓞 F) F d) ≤ᵥ A.ιF 1 := (A.val _ _).2 (by rw [hv1, map_one])
  have h2 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F d) := (A.val _ _).2 (by rw [hv1, map_one])
  rw [map_one] at h1 h2
  have hcv : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F d)) = 1 :=
    le_antisymm ((Valuation.vle_one_iff _).1 h1) ((Valuation.one_vle_iff _).1 h2)
  have hc0 : A.ιF (algebraMap (𝓞 F) F d) ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact zero_ne_one hcv
  have hinv : (A.ιF (algebraMap (𝓞 F) F d))⁻¹ ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hcv, inv_one]
  refine ⟨algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹, ?_, ?_⟩
  · rw [A.O_def]
    have hu : algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹ =
        algebraMap 𝒪[A.Fp] A.Ep ⟨_, hinv⟩ := rfl
    rw [hu]
    exact isIntegral_algebraMap
  · have hd' : A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) =
        algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d)) := by
      rw [← A.compat]
      rfl
    rw [hd', ← map_mul, inv_mul_cancel₀ hc0, map_one]

theorem avoidP : AvoidP := by
  intro F E _ _ _ _ _ p I hI
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ p.asIdeal := by
    intro d hd
    by_contra hdp
    exact hne d hdp hd
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := by
    intro a b hab
    have hE : algebraMap F E (a : F) = algebraMap F E (b : F) := congrArg (fun x : 𝓞 E => (x : E)) hab
    exact Subtype.ext ((algebraMap F E).injective hE)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [← hQp, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
  exact hI ⟨Q, hQ, hQ0⟩ hQp hIQ

end PI.LocLatEq.W
end
end

theorem eq_iff_locallyEq : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)

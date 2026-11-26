module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReduction
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatSep

theorem nilp_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilp_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilp_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem exists_lt_pow (x B : WithZero (Multiplicative ℤ)) (hx : 1 < x) : ∃ m : ℕ, B < x ^ m := by
  obtain ⟨k, hk⟩ := MulArchimedean.arch B hx
  refine ⟨k + 1, hk.trans_lt ?_⟩
  have h0 : x ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))
  rw [pow_succ]
  simpa using mul_lt_mul_of_pos_left hx (zero_lt_iff.2 h0)

theorem integral_of_commute_sep : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ w n P₀ hP A s hA hAc hsA hBd i j
  obtain ⟨B, hB⟩ := hBd
  have memO : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E ↔ Valued.v x ≤ 1 :=
    fun x => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  by_contra hij
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨⟨i₀, j₀⟩, hmax⟩ := Finite.exists_max (fun p : Fin n × Fin n => Valued.v (s p.1 p.2))
  have hc1 : 1 < Valued.v (s i₀ j₀) := by
    have : 1 < Valued.v (s i j) := not_le.1 (fun h => hij ((memO _).2 h))
    exact this.trans_le (hmax (i, j))
  have hvc : Valued.v (s i₀ j₀) ≠ 0 := ne_of_gt (zero_lt_one.trans hc1)
  have hc0 : s i₀ j₀ ≠ 0 := fun h => hvc (by rw [h, map_zero])
  set c := s i₀ j₀ with hcdef
  set u := c⁻¹ • s with hudef
  have hu : ∀ k l, u k l ∈ w.adicCompletionIntegers E := by
    intro k l
    rw [memO]
    simp only [u, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvc), mul_one]
    exact hmax (k, l)
  let A₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨A k l, hA k l⟩
  let u₀ : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := fun k l => ⟨u k l, hu k l⟩
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hA₀ : A₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = A := by
    ext; rfl
  have hu₀ : u₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = u := by
    ext; rfl
  have hcomm : Commute A₀ u₀ := by
    apply Matrix.map_injective hinj
    show (A₀ * u₀).map _ = (u₀ * A₀).map _
    rw [Matrix.map_mul, Matrix.map_mul, hA₀, hu₀]
    exact ((hsA.smul_left c⁻¹).symm).eq
  have hcp : A₀.charpoly = P₀ := by
    apply Polynomial.map_injective _ hinj
    rw [← Matrix.charpoly_map, hA₀, hAc]
  obtain ⟨m, hm⟩ := exists_lt_pow (Valued.v c) B hc1
  have hsmall : ∀ k l, Valued.v ((u ^ m) k l) < 1 := by
    intro k l
    rw [hudef, _root_.smul_pow, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_inv₀, inv_pow,
      inv_mul_lt_iff₀ (pow_pos (zero_lt_iff.2 hvc) _), mul_one]
    exact (hB m k l).trans_lt hm
  have hnil : IsNilpotent (u₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))) := by
    refine ⟨m, ?_⟩
    rw [← Matrix.map_pow]
    ext k l
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨y, hy⟩
    have e : (((u₀ ^ m) k l : w.adicCompletionIntegers E) : w.adicCompletion E) = (u ^ m) k l := by
      rw [← hu₀, ← Matrix.map_pow]; rfl
    have h1 := hsmall k l
    rw [← e, ← hy] at h1
    have h2 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
      have hy1 : ((y : w.adicCompletionIntegers E) : w.adicCompletion E) *
          (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) = 1 := by
        first
          | exact congrArg Subtype.val y.mul_inv
          | exact_mod_cast congrArg Subtype.val y.mul_inv
          | simp
      rw [← map_mul, hy1, map_one]
    have h3 := (memO _).1 (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E)).2
    have h4 : Valued.v (((y : w.adicCompletionIntegers E) : w.adicCompletion E)) *
        Valued.v (((y⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) : w.adicCompletion E) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) h1
    rw [h2] at h4
    exact lt_irrefl _ h4
  have hsep : (A₀.map (IsLocalRing.residue (w.adicCompletionIntegers E))).charpoly.Separable := by
    rw [Matrix.charpoly_map, hcp]
    exact Polynomial.Separable.map hP
  have h0 := nilp_eq_zero_of_commute_sep hsep hnil
    (hcomm.map (IsLocalRing.residue (w.adicCompletionIntegers E)).mapMatrix)
  have hone : u₀ i₀ j₀ = 1 := by
    apply Subtype.ext
    show c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc0
  have := congrFun (congrFun h0 i₀) j₀
  simp only [Matrix.map_apply, Matrix.zero_apply, hone, map_one] at this
  exact one_ne_zero this

end GlobalTheory.IntMatSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReductionStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integral_of_commute_separable_reduction : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.IntMatSep.integral_of_commute_sep | exact GlobalTheory.IntMatSep.integral_of_commute_sep | (intros; apply GlobalTheory.IntMatSep.integral_of_commute_sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjZpowersEntriesValuedBoundedOfCompactClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjZpowersEntriesValuedBoundedOfCompactClosure
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PowBdd

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound_of_isCompact (w : Pl E) {C : Set (w.adicCompletion E)} (hC : IsCompact C) :
    ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v x ≤ B := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun m : ℤ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m})
    (fun m => isOpen_le_exp w m) (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases h0 : Valued.v x = 0
      · exact ⟨0, by simp [h0]⟩
      · exact ⟨WithZero.log (Valued.v x), by simp [WithZero.exp_log h0]⟩)
  refine ⟨s.sup fun m => WithZero.exp m, fun x hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact hxm.trans (Finset.le_sup (f := fun m => WithZero.exp m) hm)

end GlobalTheory.PowBdd

open GlobalTheory.PowBdd in
theorem GlobalTheory.BCT.powers_entries_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  intro E _ _ _ n w t g hc
  have hent : ∀ i j : Fin n, ∃ B : WithZero (Multiplicative ℤ), ∀ k : ℤ,
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
    intro i j
    let f : UL n w → w.adicCompletion E := fun y =>
      (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
    have hf : Continuous f := by
      have h1 : Continuous fun y : UL n w => (g⁻¹ * y * g : UL n w) :=
        (continuous_const.mul continuous_id).mul continuous_const
      have h2 : Continuous fun y : UL n w => (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
        Units.continuous_val.comp (continuous_subtype_val.comp h1)
      exact (continuous_apply j).comp ((continuous_apply i).comp h2)
    obtain ⟨B, hB⟩ := exists_bound_of_isCompact w (hc.image hf)
    refine ⟨B, fun k => hB _ ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), rfl⟩⟩
  choose B hB using hent
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => B p.1 p.2, fun k i j => ?_⟩
  exact (hB i j k).trans (Finset.le_sup (f := fun p : Fin n × Fin n => B p.1 p.2) (Finset.mem_univ (i, j)))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjZpowersEntriesValuedBoundedOfCompactClosureStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  first | exact @GlobalTheory.BCT.powers_entries_bdd | exact GlobalTheory.BCT.powers_entries_bdd | (intros; apply GlobalTheory.BCT.powers_entries_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptCent

theorem mem_GLint_of_entries' {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entry_mem_of_mem_GLint' {K : Type} [Field K] {n : ℕ} (O : Subring K) {g : GL (Fin n) K}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (a b : Fin n) : g.val a b ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val a b).2

theorem conj_zpow' {G : Type} [Group G] (g t : G) (k : ℤ) : (g⁻¹ * t * g) ^ k = g⁻¹ * t ^ k * g := by
  have := map_zpow (MulAut.conj g⁻¹) t k
  simpa [MulAut.conj_apply] using this.symm

theorem cptPart_le_conj_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  intro E _ _ _ n w P₀ hP₀ γ hγ g hg
  have hgK : ((g⁻¹ * γ * g : UL n w) : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf).1 hg
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := ((g⁻¹ * γ * g : UL n w) : GLw n w).val with hAdef
  have hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E := fun i j => entry_mem_of_mem_GLint' _ hgK i j
  have hAc : A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [← hγ, hAdef]
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val = ((g : GLw n w)⁻¹).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp
    rw [this, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' (g : GLw n w) ((γ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro t ⟨ht, hcpt⟩
  have htγ : t * γ = γ * t := by simpa [twCent] using ht
  obtain ⟨B, hB⟩ := GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure E n w t g hcpt
  set x : UL n w := g⁻¹ * t * g with hx
  have hxA : x * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * x := by
    simp only [hx, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc t, htγ, mul_assoc]
  have val_pow : ∀ (y : UL n w) (k : ℕ), ((y ^ k : UL n w) : GLw n w).val = ((y : GLw n w).val) ^ k := by
    intro y k; simp
  have entries : ∀ (y : UL n w), y * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * y →
      (∀ k : ℕ, ∃ m : ℤ, y ^ k = g⁻¹ * t ^ m * g) → ∀ i j, (y : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
    intro y hy hpow
    refine GlobalTheory.T.mem_integral_of_commute_separable_reduction E w n P₀ hP₀ A _ hA hAc ?_ ⟨B, fun k i j => ?_⟩
    · have := congrArg (fun z : UL n w => (z : GLw n w).val) hy
      simpa [Commute, SemiconjBy, hAdef] using this
    · obtain ⟨m, hm⟩ := hpow k
      rw [← val_pow, hm]
      exact hB m i j
  have hxO := entries x hxA (fun k => ⟨k, by rw [hx, ← conj_zpow']; simp⟩)
  have hxiO := entries x⁻¹ (by
      have := congrArg (fun z => x⁻¹ * z * x⁻¹) hxA
      simpa [mul_assoc] using this.symm)
    (fun k => ⟨-(k : ℤ), by rw [hx, ← conj_zpow', _root_.zpow_neg, zpow_natCast, inv_pow]⟩)
  refine ⟨x, ?_, ?_⟩
  · show x ∈ KL n w
    refine (Subgroup.mem_subgroupOf).2 (mem_GLint_of_entries' _ _ hxO fun a b => ?_)
    have := hxiO a b
    simpa using this
  · simp [hx, MulAut.conj_apply, mul_assoc]

end GlobalTheory.CptCent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  first | exact @GlobalTheory.CptCent.cptPart_le_conj_KL | exact GlobalTheory.CptCent.cptPart_le_conj_KL | (intros; apply GlobalTheory.CptCent.cptPart_le_conj_KL <;> assumption)
end

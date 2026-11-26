module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TriBasis

noncomputable def revLex : MonomialOrder.{0, 0} ℕ :=
  (MonomialOrder.lex (σ := ℕᵒᵈ) : MonomialOrder ℕᵒᵈ)

theorem revLex_lt {β γ : ℕ →₀ ℕ} (i : ℕ) (h1 : ∀ j, i < j → β j = γ j) (h2 : β i < γ i) :
    revLex.toSyn β < revLex.toSyn γ := by
  exact ⟨OrderDual.toDual i, fun j hj => h1 (OrderDual.ofDual j) hj, h2⟩

variable {σ : Type} {R : Type} [CommRing R]

def Led (m : MonomialOrder.{0, 0} σ) (p : MvPolynomial σ R) (γ : σ →₀ ℕ) : Prop :=
  IsUnit (AddMonoidAlgebra.coeff p γ) ∧ m.toSyn (m.degree p) ≤ m.toSyn γ

theorem Led.mul {m : MonomialOrder.{0, 0} σ} {p q : MvPolynomial σ R} {γ δ : σ →₀ ℕ}
    (hp : Led m p γ) (hq : Led m q δ) : Led m (p * q) (γ + δ) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.coeff_mul_of_add_of_degree_le hp2 hq2]
    exact hp1.mul hq1
  · calc m.toSyn (m.degree (p * q)) ≤ m.toSyn (m.degree p + m.degree q) :=
          MonomialOrder.degree_mul_le
      _ = m.toSyn (m.degree p) + m.toSyn (m.degree q) := map_add _ _ _
      _ ≤ m.toSyn γ + m.toSyn δ := add_le_add hp2 hq2
      _ = m.toSyn (γ + δ) := (map_add _ _ _).symm

theorem Led.monomial (m : MonomialOrder.{0, 0} σ) (γ : σ →₀ ℕ) :
    Led m (MvPolynomial.monomial γ (1 : R)) γ := by
  classical
  refine ⟨?_, MonomialOrder.degree_monomial_le _⟩
  rw [MvPolynomial.coeff_monomial, if_pos rfl]
  exact isUnit_one

theorem Led.one (m : MonomialOrder.{0, 0} σ) : Led m (1 : MvPolynomial σ R) 0 := by
  have h := Led.monomial (R := R) m 0
  rwa [← MvPolynomial.C_apply, MvPolynomial.C_1] at h

theorem Led.pow {m : MonomialOrder.{0, 0} σ} {p : MvPolynomial σ R} {γ : σ →₀ ℕ}
    (hp : Led m p γ) (n : ℕ) : Led m (p ^ n) (n • γ) := by
  induction n with
  | zero =>
    have e : (0 : ℕ) • γ = 0 := by ext; simp
    rw [pow_zero, e]
    exact Led.one m
  | succ n ih =>
    have e : (n + 1) • γ = n • γ + γ := by ext; simp [add_mul]
    rw [pow_succ, e]
    exact ih.mul hp

theorem Led.prod {ι : Type} {m : MonomialOrder.{0, 0} σ} (s : Finset ι)
    {p : ι → MvPolynomial σ R} {γ : ι → σ →₀ ℕ}
    (hp : ∀ i, Led m (p i) (γ i)) : Led m (∏ i ∈ s, p i) (∑ i ∈ s, γ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact Led.one m
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (hp j).mul ih

theorem apply_eq_zero_of_supported {i : ℕ} {a : MvPolynomial ℕ R}
    (ha : a ∈ MvPolynomial.supported R (Set.Iio i)) {β : ℕ →₀ ℕ} (hβ : β ∈ a.support)
    {j : ℕ} (hj : i ≤ j) : β j = 0 := by
  by_contra h
  have hv : j ∈ a.vars :=
    (MvPolynomial.mem_vars_iff_mem_support j).2 ⟨β, hβ, Finsupp.mem_support_iff.2 h⟩
  have hlt : j < i := MvPolynomial.mem_supported.1 ha hv
  omega

theorem led_tri {l : ℕ} (hl : 2 ≤ l) (i : ℕ) (v : Rˣ) {a b : MvPolynomial ℕ R}
    (ha : a ∈ MvPolynomial.supported R (Set.Iio i))
    (hb : b ∈ MvPolynomial.supported R (Set.Iio i)) :
    Led revLex (MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      (Finsupp.single i l) := by
  classical
  have hmon : MvPolynomial.C (v : R) * MvPolynomial.X i ^ l =
      MvPolynomial.monomial (Finsupp.single i l) (v : R) := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hsmall : ∀ c : ℕ →₀ ℕ, (∀ j, i < j → c j = 0) → c i < l →
      revLex.toSyn c < revLex.toSyn (Finsupp.single i l) := by
    intro c h1 h2
    refine revLex_lt i (fun j hj => ?_) (by simpa using h2)
    rw [h1 j hj]
    simp [hj.ne]
  have hb0 : ∀ c, b.coeff c ≠ 0 → ∀ j, i ≤ j → c j = 0 := fun c hc j hj =>
    apply_eq_zero_of_supported hb (MvPolynomial.mem_support_iff.2 hc) hj
  have ha0 : ∀ c, (a * MvPolynomial.X i).coeff c ≠ 0 → (∀ j, i < j → c j = 0) ∧ c i ≤ 1 := by
    intro c hc
    rw [MvPolynomial.coeff_mul_X'] at hc
    split_ifs at hc with hci
    · have hd : ∀ j, i ≤ j → (c - Finsupp.single i 1 : ℕ →₀ ℕ) j = 0 := fun j hj =>
        apply_eq_zero_of_supported ha (MvPolynomial.mem_support_iff.2 hc) hj
      refine ⟨fun j hj => ?_, ?_⟩
      · have h := hd j hj.le
        rwa [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hj.ne, Nat.sub_zero] at h
      · have h := hd i le_rfl
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h
        omega
    · exact absurd rfl hc
  refine ⟨?_, ?_⟩
  · have h1 : (a * MvPolynomial.X i).coeff (Finsupp.single i l) = 0 := by
      by_contra h
      have h' := (ha0 _ h).2
      rw [Finsupp.single_eq_same] at h'
      omega
    have h2 : b.coeff (Finsupp.single i l) = 0 := by
      by_contra h
      have h' := hb0 _ h i le_rfl
      rw [Finsupp.single_eq_same] at h'
      omega
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, hmon, MvPolynomial.coeff_monomial, if_pos rfl,
      h1, h2, add_zero, add_zero]
    exact v.isUnit
  · rw [MonomialOrder.degree_le_iff]
    intro c hc
    by_cases hce : c = Finsupp.single i l
    · rw [hce]
    · have hc' := MvPolynomial.mem_support_iff.1 hc
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, hmon, MvPolynomial.coeff_monomial,
        if_neg (Ne.symm hce), zero_add] at hc'
      by_cases hA : (a * MvPolynomial.X i).coeff c = 0
      · rw [hA, zero_add] at hc'
        have h := hb0 c hc'
        refine (hsmall c (fun j hj => h j hj.le) ?_).le
        rw [h i le_rfl]
        omega
      · have h := ha0 c hA
        exact (hsmall c h.1 (by omega)).le

theorem bij (l : ℕ) [hl : Fact l.Prime] :
    Function.Bijective (fun x : Digits l × (ℕ →₀ ℕ) => x.1.1 + l • x.2) := by
  have hl0 : 0 < l := hl.out.pos
  constructor
  · rintro ⟨⟨α, hα⟩, γ⟩ ⟨⟨α', hα'⟩, γ'⟩ h
    have h' : α + l • γ = α' + l • γ' := h
    have hk : ∀ k, α k = α' k ∧ γ k = γ' k := by
      intro k
      have e := DFunLike.congr_fun h' k
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at e
      have e1 : α k = α' k := by
        have h2 := congrArg (· % l) e
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hα k), Nat.mod_eq_of_lt (hα' k)] at h2
        exact h2
      refine ⟨e1, ?_⟩
      rw [e1] at e
      exact Nat.eq_of_mul_eq_mul_left hl0 (Nat.add_left_cancel e)
    have e1 : α = α' := Finsupp.ext fun k => (hk k).1
    have e2 : γ = γ' := Finsupp.ext fun k => (hk k).2
    subst e1
    subst e2
    rfl
  · intro β
    refine ⟨(⟨Finsupp.mapRange (· % l) (Nat.zero_mod l) β, fun k => ?_⟩,
      Finsupp.mapRange (· / l) (Nat.zero_div l) β), ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact Nat.mod_lt _ hl0
    · ext k
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact Nat.mod_add_div (β k) l

theorem tri_basis : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (t : ℕ → MvPolynomial ℕ R), (∀ i, ∃ (v : Rˣ) (a b : MvPolynomial ℕ R), a ∈ MvPolynomial.supported R (Set.Iio i) ∧ b ∈ MvPolynomial.supported R (Set.Iio i) ∧ t i = MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) → LinearIndependent R (fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) ∧ Submodule.span R (Set.range fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) = ⊤ := by
  intro l hlp R _ t ht
  classical
  choose v a b ha hb hteq using ht
  have hl : 2 ≤ l := hlp.out.two_le
  set F : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ R :=
    fun x => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n with hF
  have hLed : ∀ x : Digits l × (ℕ →₀ ℕ), Led revLex (F x) (x.1.1 + l • x.2) := by
    intro x
    refine (Led.monomial revLex x.1.1).mul ?_
    have ht' : ∀ i, Led revLex (t i ^ x.2 i) (x.2 i • Finsupp.single i l) := fun i => by
      rw [hteq i]
      exact (led_tri hl i (v i) (ha i) (hb i)).pow _
    have hsum : (∑ i ∈ x.2.support, x.2 i • Finsupp.single i l) = l • x.2 := by
      ext j
      rw [Finsupp.finsetSum_apply]
      by_cases hj : j ∈ x.2.support
      · rw [Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro k _ hk
          simp [hk]
        · intro h
          exact absurd hj h
      · rw [Finset.sum_eq_zero]
        · have h0 : x.2 j = 0 := by simpa using hj
          simp [h0]
        · intro k hk
          have hkj : k ≠ j := fun e => hj (e ▸ hk)
          simp [hkj]
    rw [Finsupp.prod, ← hsum]
    exact Led.prod x.2.support ht'
  constructor
  · rw [linearIndependent_iff']
    intro s g hg i0 hi0s
    by_contra hi0
    have hs' : (s.filter fun x => g x ≠ 0).Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0s, hi0⟩⟩
    obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image _
      (fun x : Digits l × (ℕ →₀ ℕ) => revLex.toSyn (x.1.1 + l • x.2)) hs'
    rw [Finset.mem_filter] at hx
    have hc := congrArg (AddMonoidAlgebra.coeff · (x.1.1 + l • x.2)) hg
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single x] at hc
    · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hc
      obtain ⟨hu, _⟩ := hLed x
      exact hx.2 ((hu.mul_left_eq_zero).1 hc)
    · intro y hy hyx
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      by_cases hgy : g y = 0
      · rw [hgy, zero_mul]
      · have hle := hxmax y (Finset.mem_filter.2 ⟨hy, hgy⟩)
        have hne : y.1.1 + l • y.2 ≠ x.1.1 + l • x.2 := fun e => hyx ((bij l).1 e)
        have hlt : revLex.toSyn (y.1.1 + l • y.2) < revLex.toSyn (x.1.1 + l • x.2) :=
          lt_of_le_of_ne hle (fun e => hne (revLex.toSyn.injective e))
        obtain ⟨_, hdeg⟩ := hLed y
        rw [MonomialOrder.coeff_eq_zero_of_lt (lt_of_le_of_lt hdeg hlt), mul_zero]
    · intro h
      exact absurd hx.1 h
  · rw [Submodule.eq_top_iff']
    have key : ∀ s : revLex.syn, ∀ q : MvPolynomial ℕ R,
        revLex.toSyn (revLex.degree q) = s → q ∈ Submodule.span R (Set.range F) := by
      intro s
      induction s using WellFoundedLT.induction with
      | ind s ih =>
        intro q hq
        obtain ⟨x, hx⟩ := (bij l).2 (revLex.degree q)
        have hx' : x.1.1 + l • x.2 = revLex.degree q := hx
        obtain ⟨hu, hdeg⟩ := hLed x
        rw [hx'] at hu hdeg
        have hmem : (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x ∈ Submodule.span R (Set.range F) :=
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
        have hrest : q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x ∈
            Submodule.span R (Set.range F) := by
          by_cases h0 : q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x = 0
          · rw [h0]
            exact Submodule.zero_mem _
          · refine ih _ ?_ _ rfl
            rw [← hq]
            have hle : revLex.toSyn (revLex.degree (q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x))
                ≤ revLex.toSyn (revLex.degree q) :=
              le_trans MonomialOrder.degree_sub_le
                (sup_le le_rfl (le_trans MonomialOrder.degree_smul_le hdeg))
            refine lt_of_le_of_ne hle (fun e => ?_)
            have e' := revLex.toSyn.injective e
            have hz : (q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x).coeff (revLex.degree q) = 0 := by
              rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc,
                hu.val_inv_mul, mul_one, sub_self]
            exact (MonomialOrder.coeff_degree_ne_zero_iff.2 h0) (by rw [e']; exact hz)
        have h := Submodule.add_mem _ hrest hmem
        rwa [sub_add_cancel] at h
    intro q
    exact key _ q rfl

end GlobalTheory.TriBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_system_monomial_products_basis : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (t : ℕ → MvPolynomial ℕ R), (∀ i, ∃ (v : Rˣ) (a b : MvPolynomial ℕ R), a ∈ MvPolynomial.supported R (Set.Iio i) ∧ b ∈ MvPolynomial.supported R (Set.Iio i) ∧ t i = MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) → LinearIndependent R (fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) ∧ Submodule.span R (Set.range fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) = ⊤ := by
  first | exact @GlobalTheory.TriBasis.tri_basis | exact GlobalTheory.TriBasis.tri_basis | (intros; apply GlobalTheory.TriBasis.tri_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisOfCongrBasisModNilpotentIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisOfCongrBasisModNilpotentIdeal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem family_congr_basis_mod_nilpotent (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (ι : Type) (b b' : ι → M) (I : Ideal R) (n : ℕ) :
    I ^ n = ⊥ → LinearIndependent R b → Submodule.span R (Set.range b) = ⊤ →
    (∀ k, b' k - b k ∈ I • (⊤ : Submodule R M)) →
    LinearIndependent R b' ∧ Submodule.span R (Set.range b') = ⊤ := by
  intro hIn hli hsp hb
  let B : Module.Basis ι R M := Module.Basis.mk hli (by rw [hsp])
  let ν : Module.End R M := B.constr R (fun i => b' i - b i)
  have hν : ∀ i, ν (b i) = b' i - b i := by
    intro i
    have := B.constr_basis R (fun i => b' i - b i) i
    simpa [B, Module.Basis.mk_apply] using this
  have hrange : LinearMap.range ν ≤ I • (⊤ : Submodule R M) := by
    have e : LinearMap.range ν = Submodule.map ν (Submodule.span R (Set.range b)) := by
      rw [hsp, LinearMap.range_eq_map]
    rw [e, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show ν (b i) ∈ _
    rw [hν]; exact hb i
  have hpow : ∀ k : ℕ, LinearMap.range (ν ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc Submodule.map ν (LinearMap.range (ν ^ k))
          ≤ Submodule.map ν (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
        _ = I ^ k • Submodule.map ν ⊤ := Submodule.map_smul'' _ _ _
        _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := by
            exact Submodule.smul_mono le_rfl (by rw [← LinearMap.range_eq_map]; exact hrange)
        _ = I ^ (k + 1) • (⊤ : Submodule R M) := by
            rw [pow_succ, Submodule.mul_smul]
  have hnil : IsNilpotent ν := by
    refine ⟨n, ?_⟩
    have := hpow n
    rw [hIn, Submodule.bot_smul, le_bot_iff, LinearMap.range_eq_bot] at this
    exact this
  have hunit : IsUnit (1 + ν) := hnil.isUnit_one_add
  have hbij : Function.Bijective ⇑(1 + ν) := (Module.End.isUnit_iff _).1 hunit
  have hcomp : b' = ⇑(1 + ν) ∘ b := by
    funext i; simp [hν]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hli.map' (1 + ν) (LinearMap.ker_eq_bot.2 hbij.1)
  · rw [hcomp, Set.range_comp, ← Submodule.map_span, hsp, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top.2 hbij.2]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisOfCongrBasisModNilpotentIdealStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_of_congr_basis_mod_nilpotent_ideal : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (ι : Type) (b b' : ι → M) (I : Ideal R) (n : ℕ), I ^ n = ⊥ → LinearIndependent R b → Submodule.span R (Set.range b) = ⊤ → (∀ k, b' k - b k ∈ I • (⊤ : Submodule R M)) → LinearIndependent R b' ∧ Submodule.span R (Set.range b') = ⊤ := by
  first | exact @GlobalTheory.BSP.family_congr_basis_mod_nilpotent | exact GlobalTheory.BSP.family_congr_basis_mod_nilpotent | (intros; apply GlobalTheory.BSP.family_congr_basis_mod_nilpotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EnvLevel

theorem mem_smul_top_of_mem_map_C {R : Type} [CommRing R] (I : Ideal R) (p : MvPolynomial ℕ R)
    (hp : p ∈ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ℕ R) I) :
    p ∈ I • (⊤ : Submodule R (MvPolynomial ℕ R)) := by
  rw [MvPolynomial.mem_map_C_iff] at hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ fun s _ => ?_
  have : MvPolynomial.monomial s (p.coeff s) = p.coeff s • MvPolynomial.monomial s (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hp s) Submodule.mem_top

theorem tri_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (l i : ℕ) (v : Aˣ)
    (a b : MvPolynomial ℕ A)
    (ha : a ∈ MvPolynomial.supported A (Set.Iio i)) (hb : b ∈ MvPolynomial.supported A (Set.Iio i)) :
    ∃ (v' : Rˣ) (a' b' : MvPolynomial ℕ R), a' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      b' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      MvPolynomial.map f (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) =
        MvPolynomial.C (v' : R) * MvPolynomial.X i ^ l + a' * MvPolynomial.X i + b' := by
  refine ⟨Units.map f.toMonoidHom v, MvPolynomial.map f a, MvPolynomial.map f b, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported] at ha ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map a f)).trans ha
  · rw [MvPolynomial.mem_supported] at hb ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map b f)).trans hb
  · simp [map_add (f := _), map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]

end GlobalTheory.EnvLevel

theorem GlobalTheory.digitMonomials_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  intro l _ A _ J r hr n
  classical
  let π : MvPolynomial ℕ A →+* MvPolynomial ℕ (A ⧸ J ^ n) := MvPolynomial.map (Ideal.Quotient.mk (J ^ n))
  have hπs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    simp only [π]; rw [MvPolynomial.ker_map, Ideal.mk_ker]
  let I : Ideal (A ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n))
  have hIn : I ^ n = ⊥ := by
    simp only [I]; rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  choose v a b ha hb hrab using hr
  let t : ℕ → MvPolynomial ℕ (A ⧸ J ^ n) := fun i =>
    π (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)
  have ht := fun i => GlobalTheory.EnvLevel.tri_map (Ideal.Quotient.mk (J ^ n)) l i (v i) (a i) (b i) (ha i) (hb i)
  obtain ⟨htli, htsp⟩ := GlobalTheory.T.triangular_system_monomial_products_basis l (A ⧸ J ^ n) t ht
  let B : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ (A ⧸ J ^ n) := fun x =>
    MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => π (r i) ^ m
  have hK : ∀ i, π (r i) - t i ∈ Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I := by
    intro i
    have h1 : π (r i) - t i = π (r i - (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)) := by
      simp only [t, map_sub]
    have h2 : Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I =
        Ideal.map π (J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) := by
      simp only [I, π]
      rw [Ideal.map_map, Ideal.map_map, MvPolynomial.map_comp_C]
    rw [h1, h2]
    exact Ideal.mem_map_of_mem _ (hrab i)
  have hBK : ∀ x, B x - (MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => t i ^ m) ∈
      I • (⊤ : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n))) := by
    intro x
    apply GlobalTheory.EnvLevel.mem_smul_top_of_mem_map_C
    rw [← Ideal.Quotient.eq]
    simp only [B, map_mul, Finsupp.prod, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq.mpr (hK i)]
  obtain ⟨hBli, hBsp⟩ := GlobalTheory.T.basis_of_congr_basis_mod_nilpotent_ideal (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) (Digits l × (ℕ →₀ ℕ))
    _ B I n hIn htli htsp hBK
  have hBmem : ∀ k : Digits l × (ℕ →₀ ℕ), k.2 ≠ 0 → B k ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
    intro k hk
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hk
    apply Ideal.mul_mem_left
    have hd : π (r i) ^ k.2 i ∣ k.2.prod fun i m => π (r i) ^ m :=
      Finset.dvd_prod_of_mem (fun i => π (r i) ^ k.2 i) hi
    obtain ⟨d, hd⟩ := hd
    rw [hd]
    apply Ideal.mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self (f := ⇑π ∘ r) i)) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  let S : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) :=
    Submodule.span (A ⧸ J ^ n) (B '' {x | x.2 ≠ 0})
  have hmulS : ∀ i (p : MvPolynomial ℕ (A ⧸ J ^ n)), p * π (r i) ∈ S := by
    intro i p
    have hp : p ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : B k * π (r i) = B (k.1, k.2 + Finsupp.single i 1) := by
        simp only [B]
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp)]
        simp only [pow_one, mul_assoc]
      rw [this]
      refine Submodule.subset_span ⟨(k.1, k.2 + Finsupp.single i 1), ?_, rfl⟩
      intro h
      have := DFunLike.congr_fun h i
      simp at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hspanS : ∀ x ∈ Ideal.span (Set.range (⇑π ∘ r)), ∀ p, p * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact fun p => hmulS i p
    | zero => intro p; simp
    | add y z _ _ hy hz => intro p; rw [mul_add]; exact S.add_mem (hy p) (hz p)
    | smul c y _ hy => intro p; rw [smul_eq_mul, ← mul_assoc]; exact hy (p * c)
  refine ⟨?_, ?_⟩
  · intro x
    have hx : π x ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    let f0 := f.filter fun k => k.2 = 0
    let f1 := f.filter fun k => ¬ k.2 = 0
    let g : Digits l →₀ (A ⧸ J ^ n) := f0.mapDomain Prod.fst
    have hsplit : π x = (f0.sum fun k a => a • B k) + (f1.sum fun k a => a • B k) := by
      rw [← hf, ← Finsupp.sum_add_index' (h := fun k a => a • B k) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _)]
      simp only [f0, f1]
      rw [Finsupp.filter_add_filter_not]
    have h0sum : (f0.sum fun k a => a • B k) = g.sum fun α a => MvPolynomial.monomial α.1 a := by
      simp only [g]
      rw [Finsupp.sum_mapDomain_index (h := fun (α : Digits l) (a : A ⧸ J ^ n) => MvPolynomial.monomial α.1 a)
        (fun (α : Digits l) => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_zero)
        (fun (α : Digits l) _ _ => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_add _ _)]
      refine Finsupp.sum_congr fun k hk => ?_
      have hk2 : k.2 = 0 := by
        simp only [f0] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      simp only [B, hk2, Finsupp.prod_zero_index, mul_one, MvPolynomial.smul_monomial, smul_eq_mul]
    have h1mem : (f1.sum fun k a => a • B k) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      unfold Finsupp.sum
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk2 : k.2 ≠ 0 := by
        simp only [f1] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      show f1 k • B k ∈ _
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (hBmem k hk2)
    let sec : (A ⧸ J ^ n) → A := fun y =>
      if y = 0 then 0 else Function.surjInv (Ideal.Quotient.mk_surjective (I := J ^ n)) y
    have hsec0 : sec 0 = 0 := by simp [sec]
    have hsec : ∀ y, Ideal.Quotient.mk (J ^ n) (sec y) = y := by
      intro y
      by_cases h : y = 0
      · simp [sec, h]
      · simp only [sec, h, if_false]; exact Function.surjInv_eq _ y
    refine ⟨g.mapRange sec hsec0, ?_⟩
    have hmap : π ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) =
        g.sum fun α a => MvPolynomial.monomial α.1 a := by
      rw [map_finsuppSum, Finsupp.sum_mapRange_index (h := fun (α : Digits l) (a : A) => π (MvPolynomial.monomial α.1 a))
        (fun _ => by simp)]
      simp only [π, MvPolynomial.map_monomial, hsec]
    have hmem : x - ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) ∈
        Ideal.comap π (Ideal.map π (Ideal.span (Set.range r))) := by
      rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, map_sub, hmap, hsplit, ← h0sum,
        add_sub_cancel_left]
      exact h1mem
    rwa [Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot, hker] at hmem
  · intro c hc α
    have h1 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      have := Ideal.mem_map_of_mem π hc
      rwa [Ideal.map_sup, ← hker, (Ideal.map_eq_bot_iff_le_ker π).mpr le_rfl, sup_bot_eq, Ideal.map_span,
        ← Set.range_comp] at this
    have h2 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ S := by
      simpa using hspanS _ h1 1
    have hinj : Function.Injective (fun α : Digits l => (α, (0 : ℕ →₀ ℕ))) :=
      fun _ _ h => congrArg Prod.fst h
    let g' : Digits l × (ℕ →₀ ℕ) →₀ (A ⧸ J ^ n) :=
      Finsupp.mapDomain (fun α => (α, (0 : ℕ →₀ ℕ))) (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _))
    have hg' : Finsupp.linearCombination (A ⧸ J ^ n) B g' = π (c.sum fun α a => MvPolynomial.monomial α.1 a) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a => a • (B ∘ fun α => (α, (0 : ℕ →₀ ℕ))) i)
          (fun _ => zero_smul _ _), map_finsuppSum]
      refine Finsupp.sum_congr fun β _ => ?_
      simp [B, π, MvPolynomial.smul_monomial]
    obtain ⟨l', hl', hl'eq⟩ := (Finsupp.mem_span_image_iff_linearCombination (A ⧸ J ^ n)).mp h2
    have hl : l' = g' := hBli (hl'eq.trans hg'.symm)
    have h3 : g' (α, 0) = 0 := by
      rw [← hl]; exact (Finsupp.mem_supported' (A ⧸ J ^ n) l').mp hl' _ (by simp)
    have h4 : g' (α, 0) = Ideal.Quotient.mk (J ^ n) (c α) :=
      Finsupp.mapDomain_apply_of_injective hinj (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _)) α
    rw [h4] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digitMonomials_basis_envelope_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  first | exact @GlobalTheory.digitMonomials_basis_mod_pow | exact GlobalTheory.digitMonomials_basis_mod_pow | (intros; apply GlobalTheory.digitMonomials_basis_mod_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBases
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBases
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevelBasis

variable {A L Q : Type} [CommRing A] [CommRing L] [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A)
  {ι : Type} (m : ι → L)

def lsum (c : ι →₀ A) : L := c.sum fun k a => s a * m k

theorem lsum_add (c c' : ι →₀ A) : lsum s m (c + c') = lsum s m c + lsum s m c' :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add (f := _), add_mul])

theorem lsum_sub (c c' : ι →₀ A) : lsum s m (c - c') = lsum s m c - lsum s m c' :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul])

theorem lsum_smul (a : A) (c : ι →₀ A) : lsum s m (a • c) = s a * lsum s m c := by
  unfold lsum
  rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mul_assoc]

theorem lsum_single (k : ι) : lsum s m (Finsupp.single k 1) = m k := by
  unfold lsum; rw [Finsupp.sum_single_index (by simp), map_one, one_mul]

def IsApprox (n : ℕ) (x : Q) (c : ι →₀ A) : Prop := x - i (lsum s m c) ∈ (J ^ n).map (i.comp s)

theorem map_pow_eq (n : ℕ) : (J ^ n).map (i.comp s) = ((J.map s) ^ n).map i := by
  rw [← Ideal.map_map, Ideal.map_pow]

variable {s i J m}

theorem IsApprox.mono {n n' : ℕ} {x : Q} {c : ι →₀ A} (h : n' ≤ n) (hc : IsApprox s i J m n x c) :
    IsApprox s i J m n' x c :=
  Ideal.map_mono (Ideal.pow_le_pow_right h) hc

theorem exists_approx (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (n : ℕ) (x : Q) : ∃ c, IsApprox s i J m n x c := by
  obtain ⟨a, ha⟩ := hc.surj x n
  obtain ⟨c, hc'⟩ := H1 n a
  refine ⟨c, ?_⟩
  unfold IsApprox
  have e : x - i (lsum s m c) = (x - i a) + i (a - lsum s m c) := by rw [map_sub]; ring
  rw [e, map_pow_eq]
  refine add_mem ha (Ideal.mem_map_of_mem i ?_)
  rw [← Ideal.map_pow]; exact hc'

theorem approx_unique (hc : IsCompl i (J.map s))
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n)
    {n : ℕ} {x : Q} {c c' : ι →₀ A} (h : IsApprox s i J m n x c) (h' : IsApprox s i J m n x c') (k : ι) :
    c k - c' k ∈ J ^ n := by
  have h3 := sub_mem h' h
  have e : x - i (lsum s m c') - (x - i (lsum s m c)) = i (lsum s m (c - c')) := by
    rw [lsum_sub, map_sub]; ring
  rw [e, map_pow_eq] at h3
  have h4 := hc.ker _ n h3
  rw [← Ideal.map_pow] at h4
  simpa using H2 n (c - c') h4 k

end GlobalTheory.BSP.LevelBasis


open GlobalTheory.BSP.LevelBasis in
theorem GlobalTheory.BSP.exists_topBasis_of_levels (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι) (h1 : m k₀ = 1)
    (hA : IsAdicComplete J A) (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) :
    ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  have mt : ∀ n : ℕ, (J ^ n • ⊤ : Submodule A A) = J ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have exA := exists_approx (m := m) hc H1
  have lim : ∀ (x : Q) (k : ι), ∃ a : A, ∀ n c, IsApprox s i J m n x c → c k - a ∈ J ^ n := by
    intro x k
    choose f hf using exA
    obtain ⟨a, ha⟩ := hA.toIsPrecomplete.prec (f := fun n => f n x k) (fun {p q} hpq => by
      rw [SModEq.sub_mem, mt]
      exact approx_unique hc H2 (hf p x) ((hf q x).mono hpq) k)
    refine ⟨a, fun n c hcn => ?_⟩
    have h2 := ha n
    rw [SModEq.sub_mem, mt] at h2
    have := add_mem (approx_unique hc H2 hcn (hf n x) k) h2
    simpa using this
  choose C hC using lim
  have uniq : ∀ x k a, (∀ n, ∃ c, IsApprox s i J m n x c ∧ c k - a ∈ J ^ n) → C x k = a := by
    intro x k a h
    refine sub_eq_zero.1 (hA.toIsHausdorff.haus _ fun n => ?_)
    rw [SModEq.sub_mem, mt, sub_zero]
    obtain ⟨c, hc1, hc2⟩ := h n
    have := sub_mem hc2 (hC x k n c hc1)
    convert this using 1; ring
  have single_approx : ∀ n k, IsApprox s i J m n (i (m k)) (Finsupp.single k 1) := by
    intro n k; unfold IsApprox; rw [lsum_single, sub_self]; exact zero_mem _
  refine ⟨{
    b := fun k => i (m k)
    c := fun k => AddMonoidHom.mk' (fun x => C x k) (fun x y => uniq (x + y) k _ fun n => by
      obtain ⟨c, hc⟩ := exA n x
      obtain ⟨c', hc'⟩ := exA n y
      refine ⟨c + c', ?_, ?_⟩
      · unfold IsApprox at hc hc' ⊢
        have e : x + y - i (lsum s m (c + c')) = (x - i (lsum s m c)) + (y - i (lsum s m c')) := by
          rw [lsum_add, map_add (f := _)]; ring
        rw [e]; exact add_mem hc hc'
      · have := add_mem (hC x k n c hc) (hC y k n c' hc')
        convert this using 1; simp only [Finsupp.add_apply]; ring)
    c_mul := fun k a x => by
      simp only [AddMonoidHom.mk'_apply]
      refine uniq _ k _ fun n => ?_
      obtain ⟨c, hc⟩ := exA n x
      refine ⟨a • c, ?_, ?_⟩
      · unfold IsApprox at hc ⊢
        have e : (i.comp s) a * x - i (lsum s m (a • c)) = (i.comp s) a * (x - i (lsum s m c)) := by
          rw [lsum_smul, map_mul, RingHom.comp_apply]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ hc
      · have e : (a • c) k - a * C x k = a * (c k - C x k) := by
          rw [Finsupp.smul_apply, smul_eq_mul]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ (hC x k n c hc)
    c_self := fun k => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ k _ fun n => ⟨_, single_approx n k, by simp⟩
    c_ne := fun j k hjk => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ j _ fun n => ⟨_, single_approx n k, by simp [Finsupp.single_apply, Ne.symm hjk]⟩
    fin := fun x n => by
      obtain ⟨c, hc⟩ := exA n x
      refine c.support.finite_toSet.subset fun k hk => ?_
      simp only [Set.mem_setOf_eq, AddMonoidHom.mk'_apply] at hk
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      have := hC x k n c hc
      rw [h, zero_sub, neg_mem_iff] at this
      exact hk this
    approx := fun x n F hF => by
      classical
      simp only [AddMonoidHom.mk'_apply] at hF ⊢
      obtain ⟨c, hc⟩ := exA n x
      have e1 : i (lsum s m c) = ∑ k ∈ F ∪ c.support, (i.comp s) (c k) * i (m k) := by
        unfold lsum
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finsupp.sum_of_support_subset c (Finset.subset_union_right (s₁ := F)) _ (fun _ _ => by simp), map_sum]
        simp [RingHom.comp_apply, map_mul]
      have e2 : ∑ k ∈ F, (i.comp s) (C x k) * i (m k) =
          ∑ k ∈ F ∪ c.support, (i.comp s) (if k ∈ F then C x k else 0) * i (m k) := by
        rw [← Finset.sum_subset Finset.subset_union_left (fun k _ hk => by rw [if_neg hk, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]
      have e3 : x - ∑ k ∈ F, (i.comp s) (C x k) * i (m k) = (x - i (lsum s m c)) +
          ∑ k ∈ F ∪ c.support, (i.comp s) (c k - if k ∈ F then C x k else 0) * i (m k) := by
        rw [e2, e1]; simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
      rw [e3]
      refine add_mem hc (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      by_cases hk : k ∈ F
      · rw [if_pos hk]; exact hC x k n c hc
      · rw [if_neg hk, sub_zero]
        have := add_mem (hC x k n c hc) (hF k hk)
        simpa using this
    complete := by rw [← Ideal.map_map]; exact hc.complete
    i₀ := k₀
    b_i₀ := by simp only [h1, map_one] }, fun k => rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBasesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases : ∀ (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι), m k₀ = 1 → IsAdicComplete J A → IsCompl i (J.map s) → (∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s) → (∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) → ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_levels | exact GlobalTheory.BSP.exists_topBasis_of_levels | (intros; apply GlobalTheory.BSP.exists_topBasis_of_levels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpan
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.delta_quot_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  intro l _ A _ D s hs
  let N := Ideal.span s
  let g : A →+* W2 l (A ⧸ N) := (W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)
  have hg : ∀ a ∈ N, g a = 0 := by
    intro a ha
    have hle : N ≤ RingHom.ker g := by
      refine Ideal.span_le.2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      refine W2.ext ?_ ?_
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)
    exact hle ha
  let sec : A ⧸ N →+* W2 l (A ⧸ N) := Ideal.Quotient.lift N g hg
  have hsec : ∀ a, (sec a).fst = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  exact ⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpanStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_quotient_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  first | exact @GlobalTheory.BSP.delta_quot_span | exact GlobalTheory.BSP.delta_quot_span | (intros; apply GlobalTheory.BSP.delta_quot_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExists
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EnvExist

variable {l : ℕ}

theorem iter_map {A B : Type} [CommRing A] [CommRing B] {D : Delta l A} {D' : Delta l B} {g : A →+* B}
    (hg : IsδMap D D' g) (n : ℕ) (x : A) : g (D.δ^[n] x) = D'.δ^[n] (g x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]

theorem polyEval_isδ [Fact l.Prime] {A C : Type} [CommRing A] [CommRing C] (D : Delta l A) (DC : Delta l C)
    (f : A →+* C) (hf : IsδMap D DC f) (v : C) :
    IsδMap (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
  intro x
  have : x ∈ δLocus (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
    refine MvPolynomial.induction_on x ?_ ?_ ?_
    · intro a
      rw [mem_δLocus, polyDelta_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact hf a
    · intro p q hp hq
      exact add_mem hp hq
    · intro p k hp
      refine mul_mem hp ?_
      rw [mem_δLocus, polyDelta_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Function.iterate_succ_apply']
  exact mem_δLocus.1 this

end GlobalTheory.BSP.EnvExist


open GlobalTheory.BSP.EnvExist in
theorem GlobalTheory.BSP.envRing_exists : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A →
    Nonempty (EnvRing D J d p) := by
  intro l _ A _ D J d p hfg hl hd hδ hc
  have hstab : ∀ x ∈ Set.range (envRel D d p), (polyDelta D).δ x ∈ Ideal.span (Set.range (envRel D d p)) := by
    rintro _ ⟨k, rfl⟩
    refine Ideal.subset_span ⟨k + 1, ?_⟩
    unfold envRel
    exact Function.iterate_succ_apply' _ _ _
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_quotient_span l (MvPolynomial ℕ A) (polyDelta D) _ hstab
  set mk := Ideal.Quotient.mk (Ideal.span (Set.range (envRel D d p))) with hmk
  set s : A →+* MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p)) := mk.comp MvPolynomial.C with hs
  obtain ⟨Q, _, iQ, hQ⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ (J.map s) (hfg.map s)
  have hlL : ((l : ℕ) : MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) ∈ J.map s := by
    rw [← map_natCast s]; exact Ideal.mem_map_of_mem s hl
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q iQ (J.map s) hQ hlL DL
  have hX : ∀ k, iQ (mk (MvPolynomial.X k)) = DQ.δ^[k] (iQ (mk (MvPolynomial.X 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← polyDelta_X D k, hDL, hDQ, ih, Function.iterate_succ_apply']

  have hshape := GlobalTheory.T.prismaticEnvelopeRelation_triangular l A D J d p hl hd hδ
  have hlev := GlobalTheory.T.digitMonomials_basis_envelope_mod_pow l A J (envRel D d p) hshape
  have hmono : ∀ (α : ℕ →₀ ℕ) (a : A), mk (MvPolynomial.monomial α a) = s a * mk (MvPolynomial.monomial α 1) := by
    intro α a
    rw [hs, RingHom.comp_apply, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hsum : ∀ c : Digits l →₀ A, mk (c.sum fun α a => MvPolynomial.monomial α.1 a) =
      c.sum fun α a => s a * mk (MvPolynomial.monomial α.1 1) := fun c => by
    rw [map_finsuppSum]; exact Finsupp.sum_congr fun α _ => hmono α.1 (c α)
  have hmapmem : ∀ (n : ℕ) (y : MvPolynomial ℕ A), y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) →
      mk y ∈ (J ^ n).map s := by
    intro n y hy
    have h := Ideal.mem_map_of_mem mk hy
    rwa [Ideal.map_sup, hmk, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at h
  have hcomap : ∀ (n : ℕ) (y : MvPolynomial ℕ A), mk y ∈ (J ^ n).map s →
      y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    intro n y hy
    rw [hs, ← Ideal.map_map] at hy
    have h := Ideal.mem_comap.2 hy
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm] at h
  obtain ⟨tb, htb⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases A (MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) Q s iQ J (Digits l)
    (fun α => mk (MvPolynomial.monomial α.1 1)) ⟨0, fun _ => by simpa using (Fact.out : l.Prime).pos⟩
    (by simp) hc hQ
    (fun n x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc'⟩ := (hlev n).1 y
      refine ⟨c, ?_⟩
      have h := hmapmem n _ hc'
      rwa [map_sub, hsum] at h)
    (fun n c hcs => (hlev n).2 c (hcomap n _ (by rw [hsum]; exact hcs)))
  have hiδ : IsδMap D DQ (iQ.comp s) := by
    intro a
    show iQ (mk (MvPolynomial.C (D.δ a))) = DQ.δ (iQ (mk (MvPolynomial.C a)))
    rw [← polyDelta_C, hDL, hDQ]
  set_option synthInstance.maxHeartbeats 200000 in
  have hrel : DQ.δ ((iQ.comp s) p + (iQ.comp s) d * iQ (mk (MvPolynomial.X 0))) = 0 := by
    show DQ.δ (iQ (mk (MvPolynomial.C p)) + iQ (mk (MvPolynomial.C d)) * iQ (mk (MvPolynomial.X 0))) = 0
    have h0 : mk (envRel D d p 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)
    rw [← map_mul iQ, ← map_mul mk, ← map_add iQ, ← map_add mk, ← hDQ, ← hDL]
    change iQ (mk (envRel D d p 0)) = 0
    rw [h0, map_zero]
  have htbb : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))) ^ n := by
    intro α
    rw [htb α]
    show (iQ.comp mk) (MvPolynomial.monomial α.1 1) = _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    refine Finsupp.prod_congr fun k _ => ?_
    rw [map_pow, RingHom.comp_apply, hX]
  have hlift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
      IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
      ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp (iQ.comp s) = f ∧ h (iQ (mk (MvPolynomial.X 0))) = v := by
    intro C _ DC JC hC f hf hJ v hv
    have hg₀ := polyEval_isδ D DC f hf v
    set g₀ := MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v with hg₀def
    have hle : Ideal.span (Set.range (envRel D d p)) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hz : g₀ (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) = f p + f d * v := by
        simp [g₀]
      show g₀ (envRel D d p k) = 0
      rw [envRel, iter_map hg₀, Function.iterate_succ_apply, hz, hv]
      exact Function.iterate_fixed DC.δ_zero k
    set g₁ := Ideal.Quotient.lift (Ideal.span (Set.range (envRel D d p))) g₀ (fun a ha => hle ha) with hg₁def
    have hg₁C : g₁.comp s = f := RingHom.ext fun a => by
      show g₀ (MvPolynomial.C a) = f a
      exact MvPolynomial.eval₂Hom_C _ _ _
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C iQ (J.map s) JC hQ hC g₁ (by rw [Ideal.map_map, hg₁C]; exact hJ)
    have e : ∀ z, h (iQ z) = g₁ z := fun z => RingHom.congr_fun hh z
    have hlQ : ((l : ℕ) : Q) ∈ (J.map s).map iQ := by
      rw [← map_natCast iQ]; exact Ideal.mem_map_of_mem iQ hlL
    have hJQ : ((J.map s).map iQ).map h ≤ JC := by
      rw [Ideal.map_map, hh, Ideal.map_map, hg₁C]; exact hJ
    have hhδ : IsδMap DQ DC h := GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C DQ DC ((J.map s).map iQ) JC h hlQ hJQ inferInstance
      (fun x n => by
        obtain ⟨b, hb⟩ := hQ.surj x n
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        refine ⟨iQ (mk y), ?_, ?_⟩
        · rw [mem_δLocus, ← hDQ, ← hDL, e, e]
          exact hg₀ y
        · rw [← Ideal.map_pow]; exact hb)
    refine ⟨h, hhδ, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, hh, hg₁C]
    · show h (iQ (mk (MvPolynomial.X 0))) = v
      rw [e]
      show g₀ (MvPolynomial.X 0) = v
      rw [hg₀def, MvPolynomial.eval₂Hom_X']
      rfl
  exact ⟨{ Q := Q, DQ := DQ, i := iQ.comp s, i_δ := hiδ, w := iQ (mk (MvPolynomial.X 0)), rel := hrel, tb := tb, tb_b := htbb, lift := hlift }⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExistsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_envRing : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A → Nonempty (EnvRing D J d p) := by
  first | exact @GlobalTheory.BSP.envRing_exists | exact GlobalTheory.BSP.envRing_exists | (intros; apply GlobalTheory.BSP.envRing_exists <;> assumption)
end

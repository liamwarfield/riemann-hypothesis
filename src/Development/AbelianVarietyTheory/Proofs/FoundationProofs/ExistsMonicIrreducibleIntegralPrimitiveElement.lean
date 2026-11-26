module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.FunctionFieldPrimitive

open Polynomial

theorem _root_.GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive {F : Type} [Field F] [CharZero F]
    {L : Type} [Field L]
    [Algebra F L] (t : L) (ht : Transcendental F t)
    (hfin : FiniteDimensional (IntermediateField.adjoin F {t}) L) :
    ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧
      Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧
      ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F),
        Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  have htK : t ∈ IntermediateField.adjoin F {t} := IntermediateField.mem_adjoin_simple_self F t
  have hne : ∀ p : Polynomial F, p ≠ 0 → Polynomial.aeval t p ≠ 0 := fun p hp h =>
    ht ⟨p, hp, h⟩
  have hden : ∀ y ∈ IntermediateField.adjoin F {t}, ∃ s : Polynomial F, s ≠ 0 ∧
      ∃ r : Polynomial F, Polynomial.aeval t s * y = Polynomial.aeval t r := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff F y).1 hy
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, 0, by simp [hs]⟩
    · exact ⟨s, hs, r, by rw [mul_div_cancel₀ _ (hne s hs)]⟩
  have hcomm : ∀ p : Polynomial F,
      ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p :
        IntermediateField.adjoin F {t}) : L) = Polynomial.aeval t p := fun p =>
    (Polynomial.aeval_algHom_apply (IntermediateField.adjoin F {t}).val
      (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p).symm
  letI algK : Algebra (Polynomial F) (IntermediateField.adjoin F {t}) :=
    (Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t})).toRingHom.toAlgebra
  letI algL : Algebra (Polynomial F) L := (Polynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (Polynomial F) (IntermediateField.adjoin F {t}) L :=
    IsScalarTower.of_algebraMap_eq fun p => (hcomm p).symm
  haveI : Algebra.IsAlgebraic (Polynomial F) (IntermediateField.adjoin F {t}) := by
    constructor
    intro k
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C r, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P 1) h
      simp at h1
      exact hs h1
    · apply Subtype.val_injective
      rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
      show ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) s :
          IntermediateField.adjoin F {t}) : L) * k -
        ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) r :
          IntermediateField.adjoin F {t}) : L) = 0
      rw [hcomm, hcomm, hsr, sub_self]
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin F {t}) L :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (Polynomial F) L :=
    Algebra.IsAlgebraic.trans (Polynomial F) (IntermediateField.adjoin F {t}) L
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (IntermediateField.adjoin F {t}) L
  obtain ⟨y, hy0, hyint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Polynomial F) θ).exists_integral_multiple
  have hωdef : y • θ = Polynomial.aeval t y * θ := Algebra.smul_def y θ
  have hyK : Polynomial.aeval t y ∈ IntermediateField.adjoin F {t} := by
    rw [← hcomm]; exact Subtype.property _
  have htop : IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} = ⊤ := by
    rw [eq_top_iff, ← hθ, IntermediateField.adjoin_simple_le_iff]
    have hθeq : θ = (Polynomial.aeval t y)⁻¹ * (y • θ) := by
      rw [hωdef, inv_mul_cancel_left₀ (hne y hy0)]
    have hmem : (Polynomial.aeval t y)⁻¹ * (y • θ) ∈
        IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} :=
      mul_mem (inv_mem (IntermediateField.algebraMap_mem _
        (⟨Polynomial.aeval t y, hyK⟩ : IntermediateField.adjoin F {t})))
        (IntermediateField.mem_adjoin_simple_self _ (y • θ))
    rwa [← hθeq] at hmem
  refine ⟨minpoly (Polynomial F) (y • θ), y • θ, minpoly.monic hyint,
    minpoly.irreducible hyint, minpoly.aeval _ _, ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin (IntermediateField.adjoin F {t}) {y • θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (y • θ)), htop]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨1, one_ne_zero, Polynomial.X, by simp⟩
  | algebraMap k =>
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    exact ⟨s, hs, Polynomial.C r, by rw [Polynomial.eval₂_C]; exact hsr⟩
  | add a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, Polynomial.C Q₂ * R₁ + Polynomial.C Q₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, ← h₁, ← h₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, R₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_mul, ← h₁, ← h₂, map_mul]
    ring

end GlobalTheory.FunctionFieldPrimitive
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElementStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_irreducible_integral_primitive_element : ∀ {F : Type} [Field F] [CharZero F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧ Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧ ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  first | exact @GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | exact GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | (intros; apply GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePoint
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3

open Filter Topology

theorem isOpen_Hs_place : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isConnected_Hs_place : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

theorem exists_analyticAt_of_order_nonneg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ Hs) (f : X.K) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : X.an f * (b : Mero) = (a : Mero))
    (hord : 0 ≤ meromorphicOrderAt (a / b) τ) :
    ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs_place
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs_place
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs_place
  have hM : MeromorphicAt (a / b) τ := (hA τ hτ).meromorphicAt.div (hB τ hτ).meromorphicAt
  refine ⟨toMeromorphicNFAt (a / b) τ, ?_, hM.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord⟩
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have h2 : X.an f = ((a / b : ℂ → ℂ) : Mero) := by
    calc X.an f = X.an f * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (X.an f * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  rw [h2]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [compl_finite_mem_codiscreteWithin (s := Hs) (Set.finite_singleton τ)] with z hz
  exact hM.eqOn_compl_singleton_toMeromorphicNFAt hz

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

open Filter Topology

theorem exists_place_at_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs,
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  intro Ω _ _ ε X hj τ hτ
  have h0 : ∃ φ : ℂ → ℂ, X.an 0 = (φ : Mero) ∧ AnalyticAt ℂ φ τ :=
    ⟨0, by rw [map_zero, Filter.Germ.coe_zero], analyticAt_const⟩
  let W : ValuationSubring X.K :=
    { carrier := {f | ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ}
      zero_mem' := h0
      one_mem' := ⟨1, by rw [map_one, Filter.Germ.coe_one], analyticAt_const⟩
      add_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ + ψ, by rw [map_add (f := _), h1, h3, Filter.Germ.coe_add], h2.add h4⟩
      mul_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ * ψ, by rw [map_mul, h1, h3, Filter.Germ.coe_mul], h2.mul h4⟩
      neg_mem' := by
        rintro f ⟨φ, h1, h2⟩
        exact ⟨-φ, by rw [map_neg, h1, Filter.Germ.coe_neg], h2.neg⟩
      mem_or_inv_mem' := by
        intro f
        by_cases hf : f = 0
        · left; rw [hf]; exact h0
        obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero f
        have hu : X.an f⁻¹ * X.an f = 1 := by rw [← map_mul, inv_mul_cancel₀ hf, map_one]
        by_cases hord : 0 ≤ meromorphicOrderAt (a / b) τ
        · left
          exact exists_analyticAt_of_order_nonneg X hτ f a b ha hb hb0 hab hord
        · right
          have ha0 : (a : Mero) ≠ 0 := by
            intro h
            apply hb0
            calc (b : Mero) = X.an f⁻¹ * (X.an f * (b : Mero)) := by rw [← mul_assoc, hu, one_mul]
              _ = 0 := by rw [hab, h, mul_zero]
          have hba : X.an f⁻¹ * (a : Mero) = (b : Mero) := by rw [← hab, ← mul_assoc, hu, one_mul]
          have hinv : b / a = (a / b)⁻¹ := by
            funext z; simp [inv_div]
          have hord' : 0 ≤ meromorphicOrderAt (b / a) τ := by
            rw [hinv, meromorphicOrderAt_inv]
            push_neg at hord
            generalize meromorphicOrderAt (a / b) τ = o at hord ⊢
            induction o with
            | top => simp at hord
            | coe n =>
              have hn : n < 0 := by exact_mod_cast hord
              have : (0 : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ -n)
              simpa using this
          exact exists_analyticAt_of_order_nonneg X hτ f⁻¹ b a hb ha ha0 hba hord' }
  refine ⟨W, ⟨fun c => ⟨fun _ => ε c, X.an_c c, analyticAt_const⟩, ?_⟩, fun f => Iff.rfl⟩
  obtain ⟨φ, h1, h2⟩ := hj
  exact ⟨φ, h1, h2.analyticAt (isOpen_Hs_place.mem_nhds hτ)⟩

end GlobalTheory.KZ.H3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePointStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs, ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  first | exact @GlobalTheory.KZ.H3.exists_place_at_point | exact GlobalTheory.KZ.H3.exists_place_at_point | (intros; apply GlobalTheory.KZ.H3.exists_place_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductor
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductor
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.MinorMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_of_val_le {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) : Triv χ y :=
  fun u hu hle => hx u hu (hle.trans h)

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ hle
  rw [map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hle
  have : u = 1 := Units.ext hle
  simp [this]

def trivIdeal (χ : kˣ →* ℂˣ) : Ideal 𝒪[k] where
  carrier := {x | Triv χ (x : k)}
  zero_mem' := triv_zero χ
  add_mem' {x y} hx hy := by
    show Triv χ ((x : k) + y)
    rcases le_max_iff.1 (Valuation.map_add (valuation k) (x : k) y) with h | h
    · exact triv_of_val_le h hx
    · exact triv_of_val_le h hy
  smul_mem' c x hx := by
    show Triv χ ((c : k) * x)
    refine triv_of_val_le ?_ hx
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 c.2)

theorem mem_trivIdeal {χ : kˣ →* ℂˣ} {x : 𝒪[k]} : x ∈ trivIdeal χ ↔ Triv χ (x : k) := Iff.rfl

theorem isUnit_of_isUnit_mk {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  by_contra hn
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have hm : x * y ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal x).2 hn)
  have h2 := (IsLocalRing.le_maximalIdeal hI) h1
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ hm h2
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem toSquareBlockProp_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (M N : Matrix ι ι R) (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
    (M * N).toSquareBlockProp p = M.toSquareBlockProp p * N.toSquareBlockProp p := by
  have h0 : (M.toBlock p fun i => ¬ p i) = 0 := by
    ext i j; exact h i i.2 j j.2
  unfold toSquareBlockProp
  rw [toBlock_mul_eq_add p p p M N, h0, Matrix.zero_mul, add_zero]

theorem minor_map {n : ℕ} (u : GL (Fin n) 𝒪[k]) (m : Fin n) :
    minor (GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) m =
      algebraMap 𝒪[k] k ((u.val.toSquareBlockProp fun i => i ≤ m).det) := by
  rw [RingHom.map_det]; rfl

end GlobalTheory.PsType.MinorMul

open GlobalTheory.PsType.MinorMul in
theorem GlobalTheory.PsType.minor_mul_mod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  intro k _ _ _ _ n ψ hψ m hm
  set χ := ψ m / nxt ψ m with hχ
  set I := trivIdeal χ with hIdef
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : 𝒪[k]) ∈ I := h ▸ Submodule.mem_top
    exact hm (by have h2 := (mem_trivIdeal (χ := χ) (x := 1)).1 this; simpa using h2)

  have hent : ∀ a ∈ grp ψ, ∀ i j : Fin n, i ≤ m → ¬ j ≤ m → Triv χ (a.val i j) := by
    intro a ha i j hi hj
    have hj' : m < j := not_le.1 hj
    have hlt : (m : ℕ) + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt (Fin.lt_def.1 hj')) j.2
    have hnx : nxt ψ m = ψ ⟨(m : ℕ) + 1, hlt⟩ := dif_pos hlt
    have h1 := ha.2 i j (lt_of_le_of_lt hi hj')
    rw [hχ, hnx]
    exact hψ i m ⟨(m : ℕ) + 1, hlt⟩ j hi (Fin.le_def.2 (Nat.le_succ _))
      (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj'))) _ h1

  have hzero : ∀ u : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) u ∈ grp ψ →
      ∀ i, i ≤ m → ∀ j, ¬ j ≤ m → (Ideal.Quotient.mk I).mapMatrix u.val i j = 0 := by
    intro u hu i hi j hj
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hent _ hu i j hi hj)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨u, rfl⟩ := ha.1
    rw [minor_map]
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 ?_
    refine isUnit_of_isUnit_mk hI ?_
    have hdet : IsUnit ((Ideal.Quotient.mk I).mapMatrix u.val).det := by
      rw [← RingHom.map_det]
      exact (Matrix.isUnits_det_units u).map _
    rw [twoBlockTriangular_det' _ (fun i => i ≤ m) (hzero u ha)] at hdet
    have := isUnit_of_mul_isUnit_left hdet
    rwa [show (((Ideal.Quotient.mk I).mapMatrix u.val).toSquareBlockProp fun i => i ≤ m) =
      (Ideal.Quotient.mk I).mapMatrix (u.val.toSquareBlockProp fun i => i ≤ m) from rfl, ← RingHom.map_det] at this
  · intro a ha b hb
    obtain ⟨u, rfl⟩ := ha.1
    obtain ⟨w, rfl⟩ := hb.1
    rw [← map_mul, minor_map, minor_map, minor_map, ← map_mul, ← map_sub]
    suffices hs : (((u * w).val.toSquareBlockProp fun i => i ≤ m).det -
        (u.val.toSquareBlockProp fun i => i ≤ m).det * (w.val.toSquareBlockProp fun i => i ≤ m).det) ∈ I from hs
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, sub_eq_zero,
      ← det_mul]
    congr 1
    rw [Units.val_mul]
    show ((Ideal.Quotient.mk I).mapMatrix (u.val * w.val)).toSquareBlockProp (fun i => i ≤ m) = _
    rw [map_mul, toSquareBlockProp_mul _ _ _ (hzero u ha)]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  first | exact @GlobalTheory.PsType.minor_mul_mod | exact GlobalTheory.PsType.minor_mul_mod | (intros; apply GlobalTheory.PsType.minor_mul_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShape
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShape
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.CoDiag

theorem rk_eq_of_conj {G : Type} [Group G] [Fintype G] {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G M) (e e' : G → ℂ) (t : G) (h : ∀ u, e' (t * u * t⁻¹) = e u) :
    rk ρ e = rk ρ e' := by
  have h1 : op ρ e' = ρ t * op ρ e * ρ t⁻¹ := by
    unfold op
    rw [Finset.mul_sum, Finset.sum_mul, ← Equiv.sum_comp (MulAut.conj t).toEquiv]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [h]
  let T : M ≃ₗ[ℂ] M := LinearEquiv.ofLinear (ρ t) (ρ t⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
  have h2 : LinearMap.range (op ρ e') = (LinearMap.range (op ρ e)).map (T : M →ₗ[ℂ] M) := by
    have : op ρ e' = (T : M →ₗ[ℂ] M) ∘ₗ (op ρ e ∘ₗ (T.symm : M →ₗ[ℂ] M)) := by
      rw [h1]; rfl
    rw [this, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  unfold rk
  rw [h2, LinearEquiv.finrank_map_eq]

theorem exists_potential {N : ℕ} {A : Type} [Group A] (E : Fin N → Fin N → Prop)
    (hlt : ∀ a b, E a b → a < b) (huniq : ∀ a a' b, E a b → E a' b → a = a') (r : Fin N → A) :
    ∃ t : Fin N → A, ∀ a b, E a b → t b = t a * r a := by
  let F : ∀ b : Fin N, (∀ a, a < b → A) → A := fun b rec =>
    if h : ∃ a, E a b then rec h.choose (hlt _ _ h.choose_spec) * r h.choose else 1
  refine ⟨wellFounded_lt.fix F, fun a b hab => ?_⟩
  have h : ∃ a, E a b := ⟨a, hab⟩
  have ha : h.choose = a := huniq _ _ _ h.choose_spec hab
  rw [WellFounded.fix_eq]
  have : F b (fun y _ => wellFounded_lt.fix F y) = wellFounded_lt.fix F h.choose * r h.choose := dif_pos h
  rw [this, ha]

theorem exists_unit_shift (g : ℕ) [Fact g.Prime] (ψ ψ' : AddChar (ZMod g) ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ c : (ZMod g)ˣ, ∀ x, ψ' x = ψ (c * x) := by
  have hp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one h
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive hp
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, (AddChar.card_eq (α := ZMod g)).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h' (by rw [← hc, AddChar.mulShift_zero])
  exact ⟨Units.mk0 c hc0, fun x => by rw [← hc]; simp⟩

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def diagUnit (t : Fin N → (ZMod g)ˣ) : GG g N where
  val := Matrix.diagonal fun a => (t a : ZMod g)
  inv := Matrix.diagonal fun a => (((t a)⁻¹ : (ZMod g)ˣ) : ZMod g)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.mul_inv, Matrix.diagonal_one]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.inv_mul, Matrix.diagonal_one]

theorem conj_diagUnit_apply (t : Fin N → (ZMod g)ˣ) (u : GG g N) (a b : Fin N) :
    (diagUnit t * u * (diagUnit t)⁻¹).val a b = (t a : ZMod g) * u.val a b * ((t b)⁻¹ : (ZMod g)ˣ) := by
  have : (diagUnit t * u * (diagUnit t)⁻¹).val
      = Matrix.diagonal (fun a => (t a : ZMod g)) * u.val * Matrix.diagonal (fun a => (((t a)⁻¹ : (ZMod g)ˣ) : ZMod g)) := rfl
  rw [this, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_conj_diagUnit (L : Lev g N) (t : Fin N → (ZMod g)ˣ) (u : GG g N) :
    L.Mem (diagUnit t * u * (diagUnit t)⁻¹) ↔ L.Mem u := by
  have h0 : ∀ a b, (diagUnit t * u * (diagUnit t)⁻¹).val a b = 0 ↔ u.val a b = 0 := by
    intro a b
    rw [conj_diagUnit_apply, Units.mul_left_eq_zero, Units.mul_right_eq_zero]
  have h1 : ∀ a, (diagUnit t * u * (diagUnit t)⁻¹).val a a = u.val a a := by
    intro a
    rw [conj_diagUnit_apply, mul_right_comm, Units.mul_inv, one_mul]
  unfold Lev.Mem IsUp
  simp only [h0, h1]

theorem edge_lt (L : Lev g N) (a b : Fin N) (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

theorem edge_unique (L : Lev g N) (a a' b : Fin N) (h : L.Edge a b) (h' : L.Edge a' b) : a = a' := by
  unfold Lev.Edge at h h'
  apply Fin.ext
  split_ifs at h h' <;> omega

theorem rk_e_eq : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k →
    rk ρ L.e = rk ρ L'.e := by
  intro g _ N M _ _ _ ρ L L' h1 h2 h3
  have hM : L'.Mem = L.Mem := by
    funext u
    unfold Lev.Mem
    rw [h1, h2, h3]
  have hE : L'.Edge = L.Edge := by
    funext a b
    unfold Lev.Edge
    rw [h1, h2, h3]
  obtain ⟨c, hc⟩ := exists_unit_shift g L.ψ L'.ψ L.hψ L'.hψ
  obtain ⟨t, ht⟩ := exists_potential L.Edge (edge_lt L) (edge_unique L) (fun a => c * L'.co a * (L.co a)⁻¹)
  refine rk_eq_of_conj ρ _ _ (diagUnit t) fun u => ?_
  have hchi : L'.chi (diagUnit t * u * (diagUnit t)⁻¹) = L.chi u := by
    unfold Lev.chi
    rw [hc, hE, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [conj_diagUnit_apply, ht a b hab]
      simp only [Units.val_inv_eq_inv_val, Units.val_mul]
      have := (t a).ne_zero
      have := c.ne_zero
      have := (L.co a).ne_zero
      have := (L'.co a).ne_zero
      field_simp
    · simp
  unfold Lev.e eps
  rw [hchi, hM]
  simp only [mem_conj_diagUnit]

end GlobalTheory.BadShare.CoDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShapeStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k → rk ρ L.e = rk ρ L'.e := by
  first | exact @GlobalTheory.BadShare.CoDiag.rk_e_eq | exact GlobalTheory.BadShare.CoDiag.rk_e_eq | (intros; apply GlobalTheory.BadShare.CoDiag.rk_e_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvd
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section
namespace GlobalTheory.KZ.RootDisc

open Metric Filter Topology

theorem exists_root_of_ne_zero (g : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ) (hm : 0 < m)
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0) (hR : 0 < R) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball c R) ∧ ∀ z ∈ ball c R, s z ^ m = g z := by
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨L, hL0, hL⟩ := hd.isExactOn_ball.with_val_at c (Complex.log (g c))
  have hc : c ∈ ball c R := mem_ball_self hR
  have hgd : ∀ z ∈ ball c R, HasDerivAt g (deriv g z) z := fun z hz =>
    ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hh : ∀ z ∈ ball c R, HasDerivAt (fun w => g w * Complex.exp (-L w)) 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w => g w * Complex.exp (-L w))
        (deriv g z * Complex.exp (-L z) + g z * (Complex.exp (-L z) * -(deriv g z / g z))) z :=
      (hgd z hz).mul ((hL z hz).neg.cexp)
    refine h1.congr_deriv ?_
    have e : g z * (deriv g z / g z) = deriv g z := mul_div_cancel₀ _ (hne z hz)
    linear_combination (-Complex.exp (-L z)) * e
  have hexp : ∀ z ∈ ball c R, g z = Complex.exp (L z) := by
    intro z hz
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hh z hz).deriv) hz hc
    simp only [hL0, Complex.exp_neg, Complex.exp_log (hne c hc)] at hconst
    rw [mul_inv_cancel₀ (hne c hc)] at hconst
    have := Complex.exp_ne_zero (L z)
    field_simp at hconst
    exact hconst
  refine ⟨fun z => Complex.exp (L z / m), ?_, ?_⟩
  · intro z hz
    exact (((hL z hz).differentiableAt.div_const (m : ℂ)).cexp).differentiableWithinAt
  · intro z hz
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hm', hexp z hz]

end GlobalTheory.KZ.RootDisc

namespace GlobalTheory.KZ.RootDisc
open Metric Filter Topology

theorem exists_root_disc : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R →
    AnalyticOnNhd ℂ h (Metric.closedBall c R) →
    (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  intro h m c R hm hR hh hord
  set U := closedBall c R with hU
  have hmer : MeromorphicOn h U := hh.meromorphicOn
  have htop : ∀ u : U, meromorphicOrderAt h u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := hord u hu
    rw [(hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe]
    exact WithTop.coe_ne_top
  have hfin : (MeromorphicOn.divisor h U).support.Finite := (MeromorphicOn.divisor h U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg, hgne, hgeq⟩ := hmer.extract_zeros_poles htop hfin
  set d := MeromorphicOn.divisor h U with hd
  set S := hfin.toFinset with hS
  have hdU : ∀ u ∈ U, ∃ k : ℕ, d u = ((m * k : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hord u hu
    refine ⟨k, ?_⟩
    rw [hd, MeromorphicOn.divisor_apply hmer hu, (hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe, WithTop.untop₀_coe]
  let kk : ℂ → ℕ := fun u => (d u).toNat / m
  have hkk : ∀ u ∈ U, d u = ((m * kk u : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hdU u hu
    have : kk u = k := by
      simp only [kk, hk, Int.toNat_natCast]
      exact Nat.mul_div_cancel_left k hm
    rw [this, hk]
  have hSU : ∀ u ∈ S, u ∈ U := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    exact d.supportWithinDomain hu
  let q : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ kk u
  have hP : ∀ z, (∏ᶠ u, (· - u) ^ d u : ℂ → ℂ) z = q z ^ m := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S), Finset.prod_apply, ← Finset.prod_pow]
    · refine Finset.prod_congr rfl fun u hu => ?_
      rw [hkk u (hSU u hu), zpow_natCast, mul_comm, pow_mul]
      rfl
    · intro u hu
      rw [Set.Finite.coe_toFinset]
      rw [Function.mem_mulSupport] at hu
      rw [Function.mem_support]
      intro h0
      apply hu
      rw [h0, zpow_zero]
  have hqd : Differentiable ℂ q := by
    intro z
    simp only [q]
    fun_prop
  have hgball : DifferentiableOn ℂ g (ball c R) :=
    (hg.mono ball_subset_closedBall).differentiableOn
  obtain ⟨s, hs, hsm⟩ := exists_root_of_ne_zero g m c R hm hgball
    (fun z hz => hgne ⟨z, ball_subset_closedBall hz⟩) hR
  refine ⟨fun z => q z * s z, hqd.differentiableOn.mul hs, ?_⟩
  intro z hz
  rw [mul_pow, hsm z hz]
  have hzU : z ∈ U := ball_subset_closedBall hz
  have hA := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hgeq) z hzU
  have hUn : U ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds
    (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hev : h =ᶠ[𝓝[≠] z] fun w => q w ^ m * g w := by
    filter_upwards [hA, hUn] with w hw hwU
    rcases hw with hw | hw
    · simp only [Set.mem_setOf_eq, Pi.smul_apply', smul_eq_mul] at hw
      rw [hw, hP]
    · exact absurd hwU hw
  have t1 : Tendsto h (𝓝[≠] z) (𝓝 (h z)) :=
    (hh z hzU).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => q w ^ m * g w) (𝓝[≠] z) (𝓝 (q z ^ m * g z)) :=
    (((hqd z).continuousAt.pow m).mul (hg z hzU).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique_of_eventuallyEq t2 t1 hev.symm)

end GlobalTheory.KZ.RootDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvdStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R → AnalyticOnNhd ℂ h (Metric.closedBall c R) → (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.RootDisc.exists_root_disc | exact GlobalTheory.KZ.RootDisc.exists_root_disc | (intros; apply GlobalTheory.KZ.RootDisc.exists_root_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section AvgAux

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem avg_shift {K : Subgroup G} (M : Subgroup K) [M.Normal] [Fintype (K ⧸ M)]
    (π : Representation ℂ G V) (θ : G → ℂ) (s : K ⧸ M → K)
    (hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q) (hone : θ 1 = 1)
    (hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b)
    (w : V) (hw : ∀ m ∈ M, π (m : G) w = w) (hθM : ∀ m ∈ M, θ (m : G) = 1) (h : K) :
    ∑ q, (θ (s q))⁻¹ • π (s q) (π h w) = θ h • ∑ q, (θ (s q))⁻¹ • π (s q) w := by
  have hne : ∀ a : K, θ a ≠ 0 := by
    intro a ha
    have := hmul a a⁻¹
    rw [mul_inv_cancel, ha, zero_mul] at this
    simp [hone] at this
  have key : ∀ q : K ⧸ M, (θ (s q))⁻¹ • π (s q) (π h w) =
      θ h • ((θ (s (q * QuotientGroup.mk h)))⁻¹ • π (s (q * QuotientGroup.mk h)) w) := by
    intro q
    set q' := q * (QuotientGroup.mk h : K ⧸ M)
    set m : K := (s q')⁻¹ * (s q * h) with hm_def
    have hmM : m ∈ M := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [hm_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, q']
      group
    have hsplit : s q * h = s q' * m := by simp [hm_def]
    have h1 : π (s q) (π h w) = π (s q') w := by
      have : π ((s q * h : K) : G) w = π ((s q' * m : K) : G) w := by rw [hsplit]
      simpa [map_mul, hw m hmM] using this
    have h2 : θ (s q) * θ h = θ (s q') := by
      rw [← hmul, hsplit, hmul, hθM m hmM, mul_one]
    rw [h1, smul_smul]
    congr 1
    rw [← h2]
    field_simp [hne (s q), hne h]
  rw [Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : K ⧸ M))
    (fun q => (θ (s q))⁻¹ • π (s q) w)

end AvgAux

theorem aug_avg_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧
      ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  intro G V _ _ _ _ _ π hsm H θ hD u hu
  let K : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hu
  choose h hh w hw using fun i => (g i).2
  have hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b := fun a b => hD.val_mul a a.2 b b.2
  let N : Subgroup K :=
    { carrier := {j | θ j = 1 ∧ ∀ i, π j (w i) = w i}
      mul_mem' := by
        intro a b ha hb
        refine ⟨by rw [hmul, ha.1, hb.1, one_mul], fun i => ?_⟩
        simp [map_mul, ha.2 i, hb.2 i]
      one_mem' := ⟨hD.val_one, fun i => by simp⟩
      inv_mem' := by
        intro a ha
        refine ⟨?_, fun i => ?_⟩
        · have := hmul a a⁻¹
          rw [mul_inv_cancel, ha.1, one_mul] at this
          simpa [hD.val_one] using this.symm
        · have := congrArg (π ((a⁻¹ : K) : G)) (ha.2 i)
          simpa [← map_mul] using this.symm }
  have hNopen : IsOpen (N : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds
    obtain ⟨U, hU, hUθ⟩ := hD.near
    have hS : (U ∩ ⋂ i, {g : G | π g (w i) = w i}) ∈ nhds (1 : G) :=
      Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (hsm (w i)).mem_nhds (by simp))
    have hS' := continuous_subtype_val.continuousAt.preimage_mem_nhds (x := (1 : K)) hS
    refine Filter.mem_of_superset hS' ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact ⟨hUθ x hx.1 x.2, hx.2⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set G) from hD.compact)
  haveI : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let M : Subgroup K := N.normalCore
  haveI : Finite (K ⧸ M) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M) := Fintype.ofFinite _
  classical
  let s : K ⧸ M → K := fun q => if q = 1 then 1 else q.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q := by
    intro q
    by_cases hq : q = 1
    · simp [s, hq]
    · simp [s, hq]
  have hMN : ∀ m ∈ M, m ∈ N := fun m hm => Subgroup.normalCore_le N hm
  have hinj : Function.Injective (fun q => ((s q : K) : G)) := by
    intro a b hab
    rw [← hs a, ← hs b, Subtype.ext hab]
  refine ⟨Finset.univ.image (fun q => ((s q : K) : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [s]⟩
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (s q).2
  · rw [Finset.sum_image fun a _ b _ hab => hinj hab]
    have hgen : ∀ i, ∑ q, (θ (s q))⁻¹ • π (s q) ((g i : V)) = 0 := by
      intro i
      rw [hw i]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib]
      have := avg_shift M π θ s hs hD.val_one hmul (w i) (fun m hm => (hMN m hm).2 i)
        (fun m hm => (hMN m hm).1) ⟨h i, hh i⟩
      rw [this, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hc : ∀ q, (θ (s q : G))⁻¹ • c i • π (s q : G) (g i : V) =
        c i • ((θ (s q : G))⁻¹ • π (s q : G) (g i : V)) := fun q => smul_comm _ _ _
    simp only [hc, ← Finset.smul_sum, hgen i, smul_zero]

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_average_twistedSpan_eq_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  first | exact @GlobalTheory.PsType.aug_avg_zero | exact GlobalTheory.PsType.aug_avg_zero | (intros; apply GlobalTheory.PsType.aug_avg_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCoset
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem perm_apply_eq_of_le {N : ℕ} (τ : Equiv.Perm (Fin N)) (h : ∀ b, τ b ≤ b) (b : Fin N) : τ b = b := by
  have hs : ∑ i : Fin N, (τ i : ℕ) = ∑ i : Fin N, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin N => (τ i : ℕ))
    (g := fun i : Fin N => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

theorem monomial_eq_of_unipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  intro g _ N w w' u u' ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hu hu' h
  have hz : ∀ a b, a ≠ σ b → w.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ a b hne)
  have hz' : ∀ a b, a ≠ σ' b → w'.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ' a b hne)
  have hne : ∀ b, w.val (σ b) b ≠ 0 := by
    intro b h0
    have h1 : ((w⁻¹).val * w.val) b b = 1 := by
      rw [Units.inv_mul, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k = σ b
      · rw [hk, h0, mul_zero]
      · rw [hz k b hk, mul_zero]
  have key : ∀ b, w.val (σ b) b = w'.val (σ b) (σ'.symm (σ b)) * u'.val (σ'.symm (σ b)) b := by
    intro b
    have h1 : (u.val * w.val) (σ b) b = (w'.val * u'.val) (σ b) b := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ b),
      Finset.sum_eq_single (σ'.symm (σ b)), hu.1, one_mul] at h1
    · exact h1
    · intro k _ hk
      rw [hz' (σ b) k, zero_mul]
      intro hh
      apply hk
      rw [hh, Equiv.symm_apply_apply]
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro k _ hk
      rw [hz k b hk, mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have hle : ∀ b, (σ.trans σ'.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < σ'.symm (σ b) := not_le.1 hlt
    apply hne b
    rw [key b, hu'.2 _ _ hlt', mul_zero]
  have hfix : ∀ b, σ'.symm (σ b) = b := fun b => perm_apply_eq_of_le _ hle b
  have hσσ : ∀ b, σ b = σ' b := fun b => by
    have := congrArg σ' (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  apply Units.ext
  ext a b
  by_cases hab : a = σ b
  · rw [hab, key b, hfix b, hu'.1, mul_one]
  · rw [hz a b hab, hz' a b (by rwa [← hσσ])]

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCosetStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_eq_of_upperUnipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  first | exact @GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | exact GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | (intros; apply GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset <;> assumption)
end
end

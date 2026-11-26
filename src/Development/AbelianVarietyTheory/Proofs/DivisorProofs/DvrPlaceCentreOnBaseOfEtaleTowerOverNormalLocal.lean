module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModel
open GlobalTheory GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_place_isPrimeOf_of_height_eq_one {K : Type} [Field K] (cK : ℂ →+* K)
    (R : Subring K) (hR : IsLocModel cK R) (hic : IsIntegrallyClosed R) (p : Ideal R)
    (hpp : p.IsPrime) (hp : p.height = 1) :
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  classical
  letI : Algebra ℂ R := (cK.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  set S := primeLocalSubalgebra K p with hS
  have hmem : ∀ x : K, x ∈ S ↔ ∃ s : R, s ∉ p ∧ ∃ a : R, (a : K) = s * x := by
    intro x
    rw [hS, mem_primeLocalSubalgebra_iff]
    rfl
  have hne : ∀ s : R, s ∉ p → (s : K) ≠ 0 := fun s hs h =>
    hs ((Subtype.ext h : s = 0) ▸ p.zero_mem)
  have h1p : (1 : R) ∉ p := (Ideal.ne_top_iff_one p).mp hpp.ne_top
  have hRS : ∀ r : R, (r : K) ∈ S := fun r =>
    (hmem _).2 ⟨1, h1p, r, by simp⟩
  have hinv : ∀ s : R, s ∉ p → (s : K)⁻¹ ∈ S := fun s hs =>
    (hmem _).2 ⟨s, hs, 1, by simp [mul_inv_cancel₀ (hne s hs)]⟩
  have hor : ∀ x : K, x ∈ S ∨ x⁻¹ ∈ S := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ S.zero_mem)
    rw [mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx,
      mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero hx),
      heightOneOrd_vw_inv]
    omega
  let V : ValuationSubring K := { S.toSubring with mem_or_inv_mem' := hor }
  have hV : ∀ x : K, x ∈ V ↔ x ∈ S := fun _ => Iff.rfl
  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRS r⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra R V := ι.toAlgebra
  have hunit : ∀ s : R, s ∉ p → IsUnit (algebraMap R V s) := fun s hs =>
    isUnit_iff_exists_inv.mpr ⟨⟨(s : K)⁻¹, hinv s hs⟩, Subtype.ext (mul_inv_cancel₀ (hne s hs))⟩
  haveI hloc : IsLocalization.AtPrime V p := by
    refine ⟨fun y => hunit y y.2, fun z => ?_, fun {x y} h => ?_⟩
    · obtain ⟨s, hs, a, e⟩ := (hmem z).1 z.2
      refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
      show (z : K) * s = a
      rw [e, mul_comm]
    · refine ⟨1, ?_⟩
      have hxy : (x : K) = y := congrArg (fun z : V => (z : K)) h
      have : x = y := Subtype.ext hxy
      rw [this]
  haveI : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V
  have hc : ∀ a, cK a ∈ V := fun a => hRS ⟨cK a, hR.const_mem a⟩
  have hess : (cK.codRestrict V hc).EssFiniteType := by
    have h0 : (cK.codRestrict R hR.const_mem).EssFiniteType := hR.essFiniteType
    have h1 : (algebraMap R V).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization V p.primeCompl)
    convert h0.comp h1 using 1
    exact RingHom.ext fun _ => rfl
  let P0 : Place cK := ⟨V, hc, inferInstance, hess⟩
  refine ⟨P0, ⟨fun f hf => hRS ⟨f, hf⟩, fun f hf => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨s, hs, a, e⟩ := (hmem f).1 hf
    refine ⟨a, a.2, s, s.2, hne s hs, P0.ord_eq_zero (u := algebraMap R V s) (hunit s hs), ?_⟩
    rw [e, mul_comm]
  · have hg0 : (g : K) ≠ 0 := fun h => hg (Subtype.ext h)
    constructor
    · intro h hgp
      have h' : 0 ≤ P0.ord (g : K)⁻¹ := by rw [P0.ord_inv, h]; rfl
      obtain ⟨s, hs, a, e⟩ := (hmem _).1 ((P0.ord_nonneg_iff (inv_ne_zero hg0)).1 h')
      have : s = a * g := Subtype.ext (by
        show (s : K) = a * g
        rw [e, mul_assoc, inv_mul_cancel₀ hg0, mul_one])
      exact hs (this ▸ p.mul_mem_left a hgp)
    · intro hgp
      exact P0.ord_eq_zero (u := algebraMap R V g) (hunit g hgp)

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModelStatement
open GlobalTheory GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K), IsLocModel cK R → IsIntegrallyClosed R →
    ∀ p : Ideal R, p.IsPrime → p.height = 1 →
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  first | exact @GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one | exact GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one | (intros; apply GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceCentreOnBaseOfEtaleTowerOverNormalLocal
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem Place.ord_eq_zero_iff_isUnit {L : Type} [Field L] {cL : ℂ →+* L} (P : Place cL) {u : P.ring}
    (hu : u ≠ 0) : P.ord (u : L) = 0 ↔ IsUnit u := by
  refine ⟨fun h => ?_, P.ord_eq_zero⟩
  have hu' : (u : L) ≠ 0 := fun e => hu (Subtype.ext e)
  have hi : (u : L)⁻¹ ∈ P.ring := by
    rw [← P.ord_nonneg_iff (inv_ne_zero hu'), P.ord_inv, h, neg_zero]
  exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hu'))

theorem Place.exists_centre_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (T : Subring L) (P : Place cL), P.IsPrimeOf T →
    ∃ q : Ideal T, q.IsPrime ∧ q.height = 1 ∧ ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := by
  intro L _ cL T P hP
  have hC : ∀ t : T, (t : L) ∈ P.ring := fun t => hP.1 _ t.2
  let f : T →+* P.ring := T.subtype.codRestrict P.ring hC
  let q : Ideal T := (IsLocalRing.maximalIdeal P.ring).comap f
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ t : T, t ∉ q ↔ IsUnit (f t) := fun t => by
    simp only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hf : ∀ t : T, ((f t : P.ring) : L) = t := fun t => rfl
  have hord : ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := fun t ht => by
    rw [hmem t]
    have h0 : f t ≠ 0 := by
      intro e
      apply ht
      apply Subtype.ext
      rw [← hf t, e]
      simp
    have h1 := P.ord_eq_zero_iff_isUnit h0
    rw [hf t] at h1
    exact h1
  letI : Algebra T P.ring := f.toAlgebra
  haveI : IsLocalization.AtPrime P.ring q :=
    { map_units := fun y => (hmem y).1 y.2
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        have hb' : (⟨b, hb⟩ : T) ∉ q :=
          (hord ⟨b, hb⟩ (fun e' => hb0 (congrArg Subtype.val e'))).1 hbo
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb'⟩), Subtype.ext e⟩
      exists_of_eq := fun {x y} e => ⟨1, by
        have h' : ((algebraMap T P.ring x : P.ring) : L) = ((algebraMap T P.ring y : P.ring) : L) :=
          congrArg Subtype.val e
        have : x = y := Subtype.ext h'
        rw [this]⟩ }
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q P.ring
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at hd
  refine ⟨q, hq, ?_, hord⟩
  exact_mod_cast hd.symm

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem IsEtTower.flat {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) : IsNoetherianRing R ∧ ι.Flat := by
  letI := (cK.codRestrict R h.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI hR : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  refine ⟨hR, ?_⟩
  let B := MvPolynomial (Fin r) R
  let e : B →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra B T := e.toAlgebra
  letI : Algebra R T := ι.toAlgebra
  haveI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun a => by
    show ι a = e (MvPolynomial.C a)
    exact (MvPolynomial.eval₂_C _ _ _).symm
  haveI : Algebra.FormallyEtale B T := h.etale
  have hc : (cL.codRestrict T h.top.const_mem) = e.comp ((algebraMap R B).comp (cK.codRestrict R h.base.const_mem)) := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have h2 : e (MvPolynomial.C (cK.codRestrict R h.base.const_mem a)) = ι ⟨cK a, h.base.const_mem a⟩ :=
      MvPolynomial.eval₂_C _ _ _
    show cL a = ((e ((algebraMap R B) (cK.codRestrict R h.base.const_mem a)) : T) : L)
    rw [MvPolynomial.algebraMap_eq, h2, h.const]
  haveI : Algebra.EssFiniteType B T := by
    have h1 := h.top.essFiniteType
    rw [hc] at h1
    exact RingHom.EssFiniteType.of_comp _ h1
  haveI : Module.Flat B T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType B T
  haveI : Module.Flat R T := Module.Flat.trans R B T
  exact RingHom.flat_algebraMap_iff.2 inferInstance

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem centre_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  intro K L _ _ cK cL r R T ι ψ τ P h hP
  obtain ⟨-, hF⟩ := h.flat
  obtain ⟨q, hq, hq1, hqo⟩ := Place.exists_centre_of_isPrimeOf cL T P hP
  letI : Algebra R T := ι.toAlgebra
  haveI : Module.Flat R T := hF
  haveI : Algebra.HasGoingDown R T := Algebra.HasGoingDown.of_flat
  let p : Ideal R := q.comap ι
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI : q.LiesOver p := ⟨rfl⟩
  have hinj : Function.Injective ι := fun a b e => by simpa [h.retr] using congrArg ψ e
  have hι : ∀ g : R, g ≠ 0 → (P.ord (ι g : L) = 0 ↔ g ∉ p) := fun g hg =>
    hqo (ι g) ((map_ne_zero_iff ι hinj).2 hg)
  by_cases hp0 : p = ⊥
  · left
    intro g hg
    exact (hι g hg).2 (by rw [hp0]; simpa using hg)
  · right
    have hp1 : p.height = 1 := by
      apply le_antisymm
      · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
        intro p' hp' hlt
        haveI := hp'
        rw [Nat.cast_one, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot]
        by_contra hne
        obtain ⟨Q, hQq, hQ, hQo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := T) q hlt
        haveI := hQ
        have hQ0 : Q ≠ ⊥ := by
          rintro rfl
          apply hne
          rw [hQo.over]
          ext x
          simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
          exact ⟨fun e => hinj (e.trans (map_zero ι).symm), fun e => by simp [e]⟩
        have h1 : 1 ≤ Q.height := ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hQ0)
        have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQq
        rw [hq1] at h2
        have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
        exact absurd h3 (by decide)
      · exact ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hp0)
    obtain ⟨P0, h0, h0o⟩ := GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel cK R h.base h.normal p inferInstance hp1
    exact ⟨P0, h0, fun g hg => (h0o g hg).trans (hι g hg).symm⟩

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceCentreOnBaseOfEtaleTowerOverNormalLocalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_centre_on_base_of_etaleTowerOverNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  first | exact @GlobalTheory.FieldPair.centre_of_isEtTower | exact GlobalTheory.FieldPair.centre_of_isEtTower | (intros; apply GlobalTheory.FieldPair.centre_of_isEtTower <;> assumption)
end

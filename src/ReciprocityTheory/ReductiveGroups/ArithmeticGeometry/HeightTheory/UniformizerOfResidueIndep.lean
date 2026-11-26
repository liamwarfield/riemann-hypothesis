module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValAlgebraMapEqZero
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraicIndependentResidueOfIsUnit
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem mem_valuationRing {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) (x : E) :
    x ∈ vRing v ↔ 0 ≤ v x :=
  (Valuation.mem_valuationSubring_iff (v : Valuation E (Multiplicative (WithTop ℤ)ᵒᵈ)) x).trans Iff.rfl

theorem algebraicIndependent_residue_of_isUnit {A R E : Type} [CommRing A] [Field R] [Field E] (V : ValuationSubring E)
    [Algebra R (IsLocalRing.ResidueField V)] (φ : A →+* V) (ψ : A →+* R)
    (hψ : Function.Surjective ψ)
    (hc : ∀ a, algebraMap R (IsLocalRing.ResidueField V) (ψ a) = IsLocalRing.residue V (φ a))
    {τ : Type} (t : τ → V) (h : ∀ q : MvPolynomial τ A, q.map ψ ≠ 0 → IsUnit (eval₂ φ t q)) :
    AlgebraicIndependent R (fun j => IsLocalRing.residue V (t j)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective ψ hψ P
  have hu := (h q hne).map (IsLocalRing.residue V)
  have key : IsLocalRing.residue V (eval₂ φ t q) =
      MvPolynomial.aeval (fun j => IsLocalRing.residue V (t j)) (q.map ψ) := by
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext fun a => (hc a).symm
  rw [key, hP] at hu
  exact not_isUnit_zero hu

theorem trdeg_residue_le {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D : ℕ)
    (hD : Algebra.trdeg K Ω = D) (v : AddValuation Ω (WithTop ℤ))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0) (a0 : Ω) (ha0 : a0 ≠ 0) (hva0 : v a0 ≠ 0) :
    @Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (vRing v)) _ _ (resAlg (F := K) v) ≤ ((D - 1 : ℕ) : Cardinal) := by
  set V := vRing v with hV
  set k := IsLocalRing.ResidueField (V.comap (algebraMap K Ω)) with hk
  set κ := IsLocalRing.ResidueField V with hκ
  letI inst : Algebra k κ := resAlg (F := K) v
  have hKV : ∀ a : K, algebraMap K Ω a ∈ V := by
    intro a
    rw [hV, mem_valuationRing]
    by_cases ha : a = 0
    · rw [ha, map_zero, AddValuation.map_zero]
      exact le_top
    · exact le_of_eq (hK a ha).symm
  let jK : K →+* V := (algebraMap K Ω).codRestrict V hKV
  let jW : K →+* V.comap (algebraMap K Ω) :=
    (RingHom.id K).codRestrict (V.comap (algebraMap K Ω)) fun a => ValuationSubring.mem_comap.mpr (hKV a)
  let ιK : K →+* k := (IsLocalRing.residue _).comp jW
  have hcompat : ∀ a : K, algebraMap k κ (ιK a) = IsLocalRing.residue V (jK a) := by
    intro a
    show IsLocalRing.ResidueField.map (comapIncl V (algebraMap K Ω)) (IsLocalRing.residue _ (jW a)) = _
    rw [IsLocalRing.ResidueField.map_residue]
    rfl
  have hle : Algebra.trdeg k κ ≤ D := by
    have h := ReciprocityTheory.MultiplicativeHeights.residueTrdegLe K Ω V
    rw [hD] at h
    exact h
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Algebra.trdeg k κ = r :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hle Cardinal.natCast_lt_aleph0)
  haveI : FaithfulSMul k κ :=
    (faithfulSMul_iff_algebraMap_injective k κ).mpr (algebraMap k κ).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hsr : Cardinal.mk s = r := by rw [hs.cardinalMk_eq_trdeg, hr]
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hsr
  let ρ : Fin r → κ := fun i => (e.symm i : κ)
  have hρ : AlgebraicIndependent k ρ := hs.1.comp e.symm e.symm.injective
  choose tV htV using fun i => IsLocalRing.residue_surjective (R := V) (ρ i)
  let t : Fin r → Ω := fun i => (tV i : Ω)
  let ψ : MvPolynomial (Fin r) K →+* V := MvPolynomial.eval₂Hom jK tV
  have hψ : ∀ p, (ψ p : Ω) = MvPolynomial.aeval t p := by
    intro p
    show V.subtype (MvPolynomial.eval₂ jK tV p) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
  have hres : ∀ p, IsLocalRing.residue V (ψ p) = MvPolynomial.aeval ρ (p.map ιK) := by
    intro p
    show IsLocalRing.residue V (MvPolynomial.eval₂ jK tV p) = _
    have hf : (IsLocalRing.residue V).comp jK = (algebraMap k κ).comp ιK :=
      RingHom.ext fun a => (hcompat a).symm
    have hg : (fun i => IsLocalRing.residue V (tV i)) = ρ := funext htV
    rw [MvPolynomial.hom_eval₂, hf, hg, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hG : ∀ p : MvPolynomial (Fin r) K, p ≠ 0 → v (MvPolynomial.aeval t p) = 0 := by
    intro p hp
    have hne : MvPolynomial.aeval ρ (p.map ιK) ≠ 0 := by
      intro h0
      apply hp
      apply MvPolynomial.map_injective ιK ιK.injective
      rw [map_zero]
      exact (algebraicIndependent_iff.mp hρ) _ h0
    rw [← hres] at hne
    have hu := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
    rw [← hψ]
    obtain ⟨u, hu'⟩ := hu
    have hmul : (ψ p : Ω) * ((↑u⁻¹ : V) : Ω) = 1 := by
      have h1 := u.mul_inv
      rw [hu'] at h1
      exact congrArg Subtype.val h1
    have hsum : v (ψ p : Ω) + v ((↑u⁻¹ : V) : Ω) = 0 := by
      rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v _).mp (ψ p).2)
      ((mem_valuationRing v _).mp (↑u⁻¹ : V).2)).mp hsum).1
  have ht : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    have h1 := hG p hne
    rw [hp, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : WithTop ℤ) = v a0 :=
    WithTop.ne_top_iff_exists.mp (by rw [Ne, AddValuation.top_iff]; exact ha0)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hva0 hm.symm
  have htr : Transcendental (Algebra.adjoin K (Set.range t)) a0 := by
    rintro ⟨q, hq0, hq⟩
    have hcv : ∀ j, q.coeff j ≠ 0 → v ((q.coeff j : Ω)) = 0 := by
      intro j hj
      have hmem : (q.coeff j : Ω) ∈ (MvPolynomial.aeval (R := K) t).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval K t]
        exact (q.coeff j).2
      obtain ⟨p, hp⟩ := hmem
      have hp0 : p ≠ 0 := by
        rintro rfl
        apply hj
        apply Subtype.ext
        rw [← hp, map_zero]
        rfl
      rw [← hp]
      exact hG p hp0
    rw [Polynomial.aeval_eq_sum_range] at hq
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image q.support (fun j => (j : ℤ) * m)
      (Polynomial.nonempty_support_iff.mpr hq0)
    have hj0S : j0 ∈ Finset.range (q.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp j0 hj0))
    have hterm : ∀ j, q.coeff j ≠ 0 → v (q.coeff j • a0 ^ j) = (((j : ℤ) * m : ℤ) : WithTop ℤ) := by
      intro j hj
      rw [Algebra.smul_def, AddValuation.map_mul, AddValuation.map_pow, ← hm]
      have e1 : algebraMap (Algebra.adjoin K (Set.range t)) Ω (q.coeff j) = (q.coeff j : Ω) := rfl
      rw [e1, hcv j hj, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul]
    have hg : v (q.coeff j0 • a0 ^ j0) = (((j0 : ℤ) * m : ℤ) : WithTop ℤ) :=
      hterm j0 (Polynomial.mem_support_iff.mp hj0)
    have hrest : v (q.coeff j0 • a0 ^ j0) <
        v (∑ j ∈ (Finset.range (q.natDegree + 1)).erase j0, q.coeff j • a0 ^ j) := by
      rw [hg]
      apply AddValuation.map_lt_sum _ WithTop.coe_ne_top
      intro j hj
      by_cases hc : q.coeff j = 0
      · rw [hc, zero_smul, AddValuation.map_zero]
        exact WithTop.coe_lt_top _
      · rw [hterm j hc, WithTop.coe_lt_coe]
        have hne : j ≠ j0 := Finset.ne_of_mem_erase hj
        have hle := hmin j (Polynomial.mem_support_iff.mpr hc)
        have hneq : (j0 : ℤ) * m ≠ (j : ℤ) * m := by
          intro h
          apply hne
          exact_mod_cast (mul_right_cancel₀ hm0 h).symm
        exact lt_of_le_of_ne hle hneq
    rw [← Finset.add_sum_erase _ _ hj0S] at hq
    have h2 := AddValuation.map_add_eq_of_lt_left v hrest
    rw [hq, AddValuation.map_zero, hg] at h2
    exact WithTop.top_ne_coe h2
  have hind : AlgebraicIndependent K (fun o : Option (Fin r) => o.elim a0 t) :=
    AlgebraicIndependent.option_iff.mpr ⟨ht, htr⟩
  have hcardle := hind.cardinalMk_le_trdeg
  rw [hD, Cardinal.mk_option, Cardinal.mk_fintype, Fintype.card_fin] at hcardle
  have hrD : r + 1 ≤ D := by exact_mod_cast hcardle
  have hfin : Algebra.trdeg k κ ≤ ((D - 1 : ℕ) : Cardinal) := by
    rw [hr]
    exact_mod_cast (by omega : r ≤ D - 1)
  exact hfin

theorem trdeg_eq_of_card {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] {σ τ : Type} [Fintype σ] [Fintype τ] (tb : σ → C)
    (ub : τ → C) (hu : AlgebraicIndependent F ub)
    (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) (n : ℕ)
    (hE : Algebra.trdeg F E ≤ n) (hcard : Fintype.card τ = Fintype.card σ + n)
    (hT : ∀ x : F, algebraMap F C x = algebraMap E C (algebraMap F E x)) :
    Algebra.trdeg F E = n ∧ AlgebraicIndependent E tb := by
  haveI : IsScalarTower F E C := IsScalarTower.of_algebraMap_eq hT
  have h1 := ReciprocityTheory.MultiplicativeHeights.gauss_card_le_trdeg_add tb ub hu hmem
  have h2 := ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le (E := E) tb
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Algebra.trdeg F E = a :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hE Cardinal.natCast_lt_aleph0)
  rw [Cardinal.mk_fintype] at h2
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) = b :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt h2 Cardinal.natCast_lt_aleph0)
  rw [Cardinal.mk_fintype, hcard, ha, hb] at h1
  rw [ha] at hE
  rw [hb] at h2
  have h1' : Fintype.card σ + n ≤ a + b := by exact_mod_cast h1
  have hE' : a ≤ n := by exact_mod_cast hE
  have h2' : b ≤ Fintype.card σ := by exact_mod_cast h2
  have han : a = n := by omega
  have hbs : b = Fintype.card σ := by omega
  refine ⟨by rw [ha, han], ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg tb ?_⟩
  rw [hb, hbs, Cardinal.mk_fintype]

theorem isUnit_of_val_eq_zero' {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hz : v z = 0) : IsUnit (⟨z, h⟩ : vRing v) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hz
    exact WithTop.top_ne_coe hz
  have hinv : z⁻¹ ∈ vRing v := by
    rw [mem_valuationRing, AddValuation.map_inv, hz, neg_zero]
  exact IsUnit.of_mul_eq_one (⟨z⁻¹, hinv⟩ : vRing v) (Subtype.ext (mul_inv_cancel₀ hz0))

theorem val_eq_zero_of_isUnit' {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hu : IsUnit (⟨z, h⟩ : vRing v)) : v z = 0 := by
  obtain ⟨u, hu⟩ := hu
  have hmul : z * ((↑u⁻¹ : vRing v) : E) = 1 := by
    have h1 := u.mul_inv
    rw [hu] at h1
    exact congrArg Subtype.val h1
  have hsum : v z + v ((↑u⁻¹ : vRing v) : E) = 0 := by
    rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v z).mp h)
    ((mem_valuationRing v _).mp (↑u⁻¹ : vRing v).2)).mp hsum).1

theorem scalarRatio_eq {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have he : ∃ b : Ω, f = b • g := ⟨a, h⟩
  rw [ratio, dite_eq_left he]
  exact smul_left_injective Ω hg (he.choose_spec.symm.trans h)

theorem genericImage_base {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (i : Fin (D + 1)) :
    sImg j₀ x (i, j₀) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
      (if i = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) := by
  rw [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem genericImage_succAbove {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (i : Fin (D + 1)) (k : Fin N) :
    sImg j₀ x (i, j₀.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.X (Sum.inr (i, k))) := by
  rw [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem exists_rename_notMem {K : Type} [Field K] {σ : Type} (p : Ideal (MvPolynomial σ K))
    (hp : p.IsPrime ∧ p.height = 1) :
    ∃ e0 : σ, ∀ q : MvPolynomial {e // e ≠ e0} K, q ≠ 0 → rename Subtype.val q ∉ p := by
  classical
  haveI : UniqueFactorizationMonoid (MvPolynomial σ K) := MvPolynomial.uniqueFactorizationMonoid σ
  obtain ⟨hprime, hh⟩ := hp
  have hne : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hh
    exact zero_ne_one hh
  obtain ⟨g, hgp, hgprime⟩ := hprime.exists_mem_prime_of_ne_bot hne
  have hg0 : g ≠ 0 := hgprime.ne_zero
  haveI hPprime : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hg0).mpr hgprime
  have hPle : Ideal.span {g} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hgp
  have hPeq : Ideal.span {g} = p := by
    by_contra hneq
    have hlt : Ideal.span {g} < p := lt_of_le_of_ne hPle hneq
    haveI : p.FiniteHeight := ⟨Or.inr (by rw [hh]; exact ENat.one_ne_top)⟩
    have h1 : (Ideal.span {g}).height < p.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [hh] at h1
    have hPh : (Ideal.span {g}).height = 0 := ENat.lt_one_iff_eq_zero.mp h1
    haveI : (Ideal.span {g}).FiniteHeight := ⟨Or.inr (by rw [hPh]; exact ENat.zero_ne_top)⟩
    have hbot : (⊥ : Ideal (MvPolynomial σ K)) < Ideal.span {g} := by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hg0
    have h2 : (⊥ : Ideal (MvPolynomial σ K)).height < (Ideal.span {g}).height :=
      Ideal.height_strict_mono_of_isPrime_of_isPrime hbot
    rw [hPh] at h2
    exact absurd h2 not_lt_zero'
  have hvars : g.vars.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have htd : g.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold MvPolynomial.totalDegree
      apply Finset.sup_le
      intro d hd
      have hd0 : d = 0 := by
        ext i
        by_contra hi
        have hiv : i ∈ g.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr hi⟩
        rw [hemp] at hiv
        simp at hiv
      simp [hd0]
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
    have ha : AddMonoidAlgebra.coeff g 0 ≠ 0 := by
      intro ha0
      apply hg0
      rw [htd, ha0, map_zero]
    apply hgprime.not_unit
    rw [htd]
    exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
  obtain ⟨e0, he0⟩ := hvars
  refine ⟨e0, fun q hq hmem => ?_⟩
  rw [← hPeq, Ideal.mem_span_singleton] at hmem
  obtain ⟨h, hh2⟩ := hmem
  have hr0 : rename Subtype.val q ≠ 0 := by
    intro h0
    apply hq
    exact MvPolynomial.rename_injective _ Subtype.val_injective (by rw [h0, map_zero])
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh2
    exact hr0 hh2
  have hdeg : MvPolynomial.degreeOf e0 (rename Subtype.val q) ≠ 0 := by
    rw [hh2, MvPolynomial.degreeOf_mul_eq hg0 hh0]
    have h3 := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mp he0
    omega
  have hin : e0 ∈ (rename Subtype.val q).vars := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hdeg
  obtain ⟨i, -, hi⟩ := MvPolynomial.mem_vars_rename _ _ hin
  exact i.2 hi

theorem card_subtype_ne' {σ : Type} [Fintype σ] [DecidableEq σ] (e0 : σ) :
    Fintype.card {e // e ≠ e0} = Fintype.card σ - 1 := by
  first
  | rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  | simp [Fintype.card_subtype_compl]

theorem card_baseOrOffColumn {D N : ℕ} (j0 : Fin (N + 1)) :
    Fintype.card {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} = (D + 1) * (N + 1) - D := by
  have hc := Fintype.card_subtype_compl (fun e : TVar D N => ¬ (e.1 = 0 ∨ e.2 ≠ j0))
  have e1 : {e : TVar D N // ¬ ¬ (e.1 = 0 ∨ e.2 ≠ j0)} ≃ {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} :=
    Equiv.subtypeEquivRight (fun _ => not_not)
  have e2 : {e : TVar D N // ¬ (e.1 = 0 ∨ e.2 ≠ j0)} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun x => ⟨x.1.1, fun h => x.2 (Or.inl h)⟩
      invFun := fun i => ⟨(i.1, j0), fun h => h.elim i.2 (fun h' => h' rfl)⟩
      left_inv := fun x => by
        obtain ⟨⟨a, b⟩, hx⟩ := x
        have hb : b = j0 := by
          by_contra hne
          exact hx (Or.inr hne)
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e1, Fintype.card_congr e2] at hc
  have h3 : Fintype.card {i : Fin (D + 1) // i ≠ 0} = D := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  rw [hc, h3, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem val_algebraMap_eq_zero (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p) (a : K)
    (ha : a ≠ 0) : w (algebraMap K (OmS (Ω c) d.D d.N) a) = 0 := by
  have h1 := (hw.2 (MvPolynomial.C a)).1
  have h2 := (hw.2 (MvPolynomial.C a⁻¹)).1
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes] at h1 h2
  have h3 : w (algebraMap K (OmS (Ω c) d.D d.N) a) + w (algebraMap K (OmS (Ω c) d.D d.N) a⁻¹) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg h1 h2).mp h3).1

theorem w_eq_scalarRatio_smul (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hmem := hd.w_mem
  have hne : (⟨d.w (d.jc c) c, hmem _ c⟩ : 𝒜 c d.wL) ≠ 0 := fun h => hd.w_base c (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨d.w j c, hmem j c⟩
  have hex : ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    refine ⟨a, ?_⟩
    have h2 := congrArg Subtype.val ha
    simpa using h2.symm
  unfold ratio
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem exists_integral_base (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) :
    ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing v) ∧
      ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 ∧
      ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
  have uniq : ∀ (f g : A c) (a : Ω c), g ≠ 0 → f = a • g → ratio (Ω := Ω c) f g = a := by
    intro f g a hg hfa
    have hex : ∃ b : Ω c, f = b • g := ⟨a, hfa⟩
    unfold ratio
    rw [dite_eq_left hex]
    by_contra hne
    apply hg
    have h0 : (hex.choose - a) • g = 0 := by rw [sub_smul, ← hex.choose_spec, ← hfa, sub_self]
    have h1 := congrArg (fun y => (hex.choose - a)⁻¹ • y) h0
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h1
  obtain ⟨q, hqdef⟩ : ∃ q : Fin (d.N + 1) → Ω c, ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = q j :=
    ⟨_, fun _ => rfl⟩
  have hx : ∀ j, d.w j c = q j • d.w (d.jc c) c := fun j => by
    rw [← hqdef]
    exact d.w_eq_scalarRatio_smul hd c j
  have hq1 : q (d.jc c) = 1 := by
    rw [← hqdef]
    exact uniq _ _ 1 (hd.w_base c) (one_smul _ _).symm
  have key : ∀ a b : WithTop ℤ, b ≠ ⊤ → b ≤ a + b → 0 ≤ a := by
    intro a b hb h
    induction a using WithTop.recTopCoe with
    | top => exact le_top
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top => exact absurd rfl hb
      | coe b =>
        have h1 : (b : WithTop ℤ) ≤ ((a + b : ℤ) : WithTop ℤ) := by exact_mod_cast h
        have h2 : b ≤ a + b := WithTop.coe_le_coe.mp h1
        exact_mod_cast (show (0 : ℤ) ≤ a by omega)
  have smul_ne : ∀ (a : Ω c) (g : A c), a ≠ 0 → g ≠ 0 → a • g ≠ 0 := by
    intro a g ha hg h
    apply hg
    have h1 := congrArg (fun y => a⁻¹ • y) h
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ ha] at h1
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ (fun j => v (q j)) ⟨d.jc c, Finset.mem_univ _⟩
  have hvle : v (q j0) ≤ 0 := by
    have h1 := hj0 (d.jc c) (Finset.mem_univ _)
    rwa [hq1, AddValuation.map_one] at h1
  have hq0 : q j0 ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hvle
    first
    | exact absurd hvle (by simp)
    | exact WithTop.zero_ne_top (top_le_iff.mp hvle)
  have hw0 : d.w j0 c ≠ 0 := by
    rw [hx j0]
    exact smul_ne _ _ hq0 (hd.w_base c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) = q j / q j0 := by
    intro j
    apply uniq _ _ _ hw0
    rw [hx j, hx j0, smul_smul, div_mul_cancel₀ _ hq0]
  refine ⟨j0, hw0, fun j => ?_, by rw [hqdef]; exact hq0, fun j => by rw [hrat j, hqdef, hqdef]⟩
  rw [mem_valuationRing, hrat j]
  have hmul : v (q j) = v (q j / q j0) + v (q j0) := by
    rw [← AddValuation.map_mul, div_mul_cancel₀ _ hq0]
  have hle := hj0 j (Finset.mem_univ _)
  rw [hmul] at hle
  have hnt : v (q j0) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact hq0 h
  exact key _ _ hnt hle

theorem genericHomAt_relation (hd : d.AxH 𝒜) (c : ι) (j0 : Fin (d.N + 1)) (hw0 : d.w j0 c ≠ 0)
    (hq : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))
    (i : Fin (d.D + 1)) (hi : i ≠ 0) :
    d.sH c (X (i, j0)) = -∑ j ∈ Finset.univ.erase j0, d.sH c (X (i, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) := by
  have uniq : ∀ (f g : A c) (a : Ω c), g ≠ 0 → f = a • g → ratio (Ω := Ω c) f g = a := by
    intro f g a hg hfa
    have hex : ∃ b : Ω c, f = b • g := ⟨a, hfa⟩
    unfold ratio
    rw [dite_eq_left hex]
    by_contra hne
    apply hg
    have h0 : (hex.choose - a) • g = 0 := by rw [sub_smul, ← hex.choose_spec, ← hfa, sub_self]
    have h1 := congrArg (fun y => (hex.choose - a)⁻¹ • y) h0
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h1
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : Fin (d.N + 1) → Ω c, ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = q j :=
    ⟨_, fun _ => rfl⟩
  have hx : ∀ j, d.w j c = q j • d.w (d.jc c) c := fun j => by
    rw [← hqdef]
    exact d.w_eq_scalarRatio_smul hd c j
  have hq1 : q (d.jc c) = 1 := by
    rw [← hqdef]
    exact uniq _ _ 1 (hd.w_base c) (one_smul _ _).symm
  have hq0 : q j0 ≠ 0 := by
    intro h0
    apply hw0
    rw [hx j0, h0, zero_smul]
  have hxq : ∀ k, d.x c k = q ((d.jc c).succAbove k) := fun k => hqdef _
  obtain ⟨T, hTdef⟩ : ∃ T : Fin (d.N + 1) → OmS (Ω c) d.D d.N, ∀ j, d.sH c (X (i, j)) = T j :=
    ⟨_, fun _ => rfl⟩
  have hTX : ∀ j, T j = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
        (-∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (Sum.inr (i, k))) j) := by
    intro j
    rw [← hTdef]
    simp only [Data.sH, sHom, MvPolynomial.aeval_X, sImg, if_neg hi]
  have hCr : ∀ a : Ω c, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (MvPolynomial.C a) =
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N),
      MvPolynomial.algebraMap_eq]
  have hTjc : T (d.jc c) = -∑ k, T ((d.jc c).succAbove k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (d.x c k) := by
    rw [hTX, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_neg, map_sum, map_mul, hCr]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hTX, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  have hsum : ∑ j, T j * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j) = 0 := by
    rw [Fin.sum_univ_succAbove _ (d.jc c), hq1, map_one, mul_one, hTjc]
    simp only [hxq]
    exact neg_add_cancel _
  simp only [hq, hqdef, hTdef, map_div₀]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)] at hsum
  have hr0 : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0) ≠ 0 := (map_ne_zero _).mpr hq0
  have hS : ∑ j ∈ Finset.univ.erase j0, T j * (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j) /
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0)) =
      (∑ j ∈ Finset.univ.erase j0, T j * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j)) /
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hS, ← neg_div, eq_div_iff hr0]
  linear_combination hsum

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem uniformizer_of_residue_indep {Ω : Type} [Field Ω] {σ τ : Type}
    (w : AddValuation (FractionRing (MvPolynomial σ Ω)) (WithTop ℤ)) (hw : IsNormDiscrete w)
    (t : τ → FractionRing (MvPolynomial σ Ω)) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))
      AlgebraicIndependent (IsLocalRing.ResidueField
          ((vRing w).comap (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))))
        (fun s => IsLocalRing.residue (vRing w) ⟨t s, ht s⟩))
    (g : σ → MvPolynomial τ Ω)
    (hg : ∀ x, algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) (X x) =
      aeval t (g x)) :
    ∃ π : Ω, w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) π) = 1 := by
  classical
  obtain ⟨hw1, f, hf⟩ := hw
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ Ω) f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have key : ∀ P : MvPolynomial σ Ω,
      algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) P =
        aeval t (bind₁ g P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [bind₁_C_right, aeval_C, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
    | mul_X P x hP => simp only [map_mul, hP, bind₁_X_right, hg]
  have hinj := IsFractionRing.injective (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, AddValuation.map_zero] at hf
    simp at hf
  have hne : ∀ P : MvPolynomial σ Ω, P ≠ 0 → bind₁ g P ≠ 0 := by
    intro P hP h0
    apply hP
    apply hinj
    rw [key, h0, map_zero, map_zero]
  obtain ⟨c, hc0, hc⟩ := ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne p hp0)
  obtain ⟨d, hd0, hd⟩ := ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne q hq0)
  rw [← key] at hc hd
  have hqa : algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) q ≠ 0 := by
    intro h0; exact hq0 (hinj (by rw [h0, map_zero]))
  have hda : algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d ≠ 0 :=
    (map_ne_zero _).2 hd0
  refine ⟨c / d, ?_⟩
  have h1 : w (algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) p) =
      1 + w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d) := by
    rw [← hf, ← hd, ← AddValuation.map_mul, div_mul_cancel₀ _ hqa]
  have h2 : w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) c) =
      w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) (c / d)) +
        w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d) := by
    rw [← AddValuation.map_mul, ← map_mul, div_mul_cancel₀ _ hd0]
  exact ValuationResidueLemmas.wt_cancel (hw1 _ hda) (by rw [← h2, ← hc, h1])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)


set_option maxHeartbeats 800000 in
theorem PlaceTrivialOrPositive (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N))
    (hp : p ∈ d.HtOne) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p) :
    (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∨
    (d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) := by
  classical
  by_cases htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0
  · exact Or.inl htriv
  right
  simp only [not_forall] at htriv
  obtain ⟨a0, ha0, hva0⟩ := htriv
  have hvK : IsTrivOn K (d.Wres c w) := by
    intro a ha
    show w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a)) = 0
    rw [← IsScalarTower.algebraMap_apply]
    exact d.val_algebraMap_eq_zero c p w hw a ha
  obtain ⟨j0, hw0, hint, hx0, hq⟩ := d.exists_integral_base hd c (d.Wres c w)
  have htr := trdeg_residue_le d.D (hd.trdeg c) (d.Wres c w) hvK a0 ha0 hva0
  letI iWV : Algebra (IsLocalRing.ResidueField (vRing (d.Wres c w)))
      (IsLocalRing.ResidueField (vRing w)) := resAlg (F := Ω c) w
  letI iRW := resAlg (F := K) (d.Wres c w)
  letI iRV : Algebra (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing w)) :=
    ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp
      (algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
        (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let t' : TVar d.D d.N → vRing w := fun e => ⟨d.sH c (X e), (hw.2 (X e)).1⟩
  let ρ : Fin (d.N + 1) → IsLocalRing.ResidueField (vRing (d.Wres c w)) := fun j =>
    IsLocalRing.residue _ ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩
  have hres : ∀ i, i ≠ 0 → IsLocalRing.residue (vRing w) (t' (i, j0)) =
      -∑ j ∈ Finset.univ.erase j0, IsLocalRing.residue (vRing w) (t' (i, j)) *
        algebraMap _ (IsLocalRing.ResidueField (vRing w)) (ρ j) := by
    intro i hi
    have hV : t' (i, j0) = -∑ j ∈ Finset.univ.erase j0, t' (i, j) *
        comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩ := by
      apply Subtype.ext
      push_cast
      exact d.genericHomAt_relation hd c j0 hw0 hq i hi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hV, map_neg, map_sum]
    congr 1
  obtain ⟨e0, he0⟩ := exists_rename_notMem p hp
  have hcK : ∀ a : K, algebraMap K (OmS (Ω c) d.D d.N) a ∈ vRing w := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    · rw [mem_valuationRing, d.val_algebraMap_eq_zero c p w hw a ha]
  have hoK : ∀ a : K, a ∈ (vRing (d.Wres c w)).comap (algebraMap K (Ω c)) := by
    intro a
    show algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a) ∈ vRing w
    rw [← IsScalarTower.algebraMap_apply]
    exact hcK a
  let φ : K →+* vRing w := (algebraMap K (OmS (Ω c) d.D d.N)).codRestrict (vRing w) hcK
  let ψ : K →+* IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))) :=
    (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict _ hoK)
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨x.1, rfl⟩
  have hc : ∀ a, algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing w)) (ψ a) = IsLocalRing.residue (vRing w) (φ a) := by
    intro a
    show IsLocalRing.residue (vRing w) (comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
      (comapIncl (vRing (d.Wres c w)) (algebraMap K (Ω c)) ⟨a, hoK a⟩)) = _
    exact congrArg _ (Subtype.ext (IsScalarTower.algebraMap_apply K (Ω c) _ a).symm)
  have hu : AlgebraicIndependent (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (fun e : {e // e ≠ e0} => IsLocalRing.residue (vRing w) (t' e.1)) := by
    apply algebraicIndependent_residue_of_isUnit (vRing w) φ ψ hψ hc (fun e : {e // e ≠ e0} => t' e.1)
    intro q hq
    have hq0 : q ≠ 0 := by rintro rfl; exact hq (map_zero _)
    have hnot := he0 q hq0
    have hcoe : ((eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q : vRing w) : OmS (Ω c) d.D d.N) =
        d.sH c (rename Subtype.val q) := by
      have e1 := eval₂_comp_left (vRing w).subtype φ (fun e : {e // e ≠ e0} => t' e.1) q
      have e2 : (vRing w).subtype.comp φ = algebraMap K (OmS (Ω c) d.D d.N) := RingHom.ext fun _ => rfl
      rw [e2] at e1
      refine e1.trans ?_
      conv_rhs => rw [MvPolynomial.aeval_unique (d.sH c), aeval_rename, aeval_def]
      rfl
    have h0 := (hw.2 (rename Subtype.val q)).1
    have h1 : ¬ (0 < w (d.sH c (rename Subtype.val q))) := fun h => hnot ((hw.2 _).2.mp h)
    have hv0 : w (d.sH c (rename Subtype.val q)) = 0 := le_antisymm (not_lt.mp h1) h0
    have he : eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q = ⟨d.sH c (rename Subtype.val q), h0⟩ :=
      Subtype.ext hcoe
    rw [he]
    exact isUnit_of_val_eq_zero' w h0 hv0
  let tb : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} → IsLocalRing.ResidueField (vRing w) :=
    fun e => IsLocalRing.residue (vRing w) (t' e.1)
  have hmemG : ∀ (M : Type) [Field M] [Algebra M (IsLocalRing.ResidueField (vRing w))],
      (∀ j, ∃ m : M, algebraMap M (IsLocalRing.ResidueField (vRing w)) m =
        algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j)) →
      ∀ e : {e // e ≠ e0}, IsLocalRing.residue (vRing w) (t' e.1) ∈ Algebra.adjoin M (Set.range tb) := by
    intro M _ _ hM e
    obtain ⟨⟨i, j⟩, he⟩ := e
    by_cases hij : i = 0 ∨ j ≠ j0
    · exact Algebra.subset_adjoin ⟨⟨(i, j), hij⟩, rfl⟩
    · rw [not_or, not_not] at hij
      obtain ⟨hi, rfl⟩ := hij
      show IsLocalRing.residue (vRing w) (t' (i, _)) ∈ _
      rw [hres i hi]
      refine neg_mem (Subalgebra.sum_mem _ fun j hj => Subalgebra.mul_mem _ ?_ ?_)
      · exact Algebra.subset_adjoin ⟨⟨(i, j), Or.inr (Finset.ne_of_mem_erase hj)⟩, rfl⟩
      · obtain ⟨m, hm⟩ := hM j
        rw [← hm]
        exact Subalgebra.algebraMap_mem _ m
  have hcard : Fintype.card {e : TVar d.D d.N // e ≠ e0} =
      Fintype.card {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} + (d.D - 1) := by
    rw [card_subtype_ne', card_baseOrOffColumn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have h3 := hd.D_ge
    have h4 : d.D + 1 ≤ (d.D + 1) * (d.N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  obtain ⟨htrW, hindW⟩ := trdeg_eq_of_card tb _ hu (hmemG _ fun j => ⟨ρ j, rfl⟩) (d.D - 1) htr hcard (fun _ => rfl)
  let k1 := IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
    {r | ∃ j, ∃ h : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing (d.Wres c w),
      r = IsLocalRing.residue (vRing (d.Wres c w)) ⟨_, h⟩}
  letI ik1 : Algebra k1 (IsLocalRing.ResidueField (vRing w)) :=
    ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp
      (algebraMap k1 (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra
  have hk1le := (trdeg_le_of_injective k1.val Subtype.val_injective).trans htr
  obtain ⟨htrk1, -⟩ := trdeg_eq_of_card (E := k1) tb _ hu
    (hmemG k1 fun j => ⟨⟨ρ j, IntermediateField.subset_adjoin _ _ ⟨j, hint j, rfl⟩⟩, rfl⟩) (d.D - 1) hk1le hcard (fun _ => rfl)
  have hRC : d.ResCond c (d.Wres c w) (d.D - 1) := ⟨htrW, j0, hw0, fun j => hint j, htrk1⟩

  have hz0mem : (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∈ vRing w :=
    sum_mem fun j _ => mul_mem (hw.2 (X (0, j))).1 (hint j)
  have hz0V : (⟨_, hz0mem⟩ : vRing w) = ∑ j, t' (0, j) *
      comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) ⟨_, hint j⟩ := by
    apply Subtype.ext
    push_cast
    rfl
  have hres0 : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ =
      ∑ j, algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j) *
        tb ⟨(0, j), Or.inl rfl⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz0V, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_comm]
    rfl
  have hli := hindW.linearIndependent.comp
    (fun j : Fin (d.N + 1) => (⟨(0, j), Or.inl rfl⟩ : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0}))
    (fun a b hab => by simpa using hab)
  have hρ0 : ρ j0 = 1 := by
    have e : (⟨ratio (Ω := Ω c) (d.w j0 c) (d.w j0 c), hint j0⟩ : vRing (d.Wres c w)) = 1 :=
      Subtype.ext (scalarRatio_eq hw0 (one_smul _ _).symm)
    show IsLocalRing.residue _ _ = 1
    rw [e, map_one]
  have hne : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ ≠ 0 := by
    intro h0
    have := Fintype.linearIndependent_iff.mp hli ρ (by
      rw [← h0, hres0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def]
      rfl) j0
    rw [hρ0] at this
    exact one_ne_zero this
  have hunit : w (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0 :=
    val_eq_zero_of_isUnit' w hz0mem ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne)

  have hNorm : IsNormDiscrete (d.Wres c w) := by
    refine ⟨fun x hx => hw.1.1 _ ((map_ne_zero _).mpr hx), ?_⟩
    let G : TVar d.D d.N → MvPolynomial {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} (Ω c) := fun e =>
      if h : e.1 = 0 ∨ e.2 ≠ j0 then X ⟨e, h⟩ else
        -∑ j ∈ (Finset.univ.erase j0).attach,
          X ⟨(e.1, j.1), Or.inr (Finset.ne_of_mem_erase j.2)⟩ *
            C (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))
    have hG : ∀ e, d.sH c (X e) =
        aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1)) (G e) := by
      rintro ⟨i, j⟩
      by_cases h : i = 0 ∨ j ≠ j0
      · simp only [G, dite_eq_left h, aeval_X]
      · set_option synthInstance.maxHeartbeats 100000 in
          simp only [G, dite_eq_right h, map_neg, map_sum, map_mul, aeval_X, aeval_C]
        rw [not_or, not_not] at h
        obtain ⟨hi, hj⟩ := h
        subst j
        rw [d.genericHomAt_relation hd c _ hw0 hq i hi]
        congr 1
        exact (Finset.sum_attach _ (fun j => d.sH c (X (i, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))).symm
    have hg : ∀ x : SVar d.D d.N,
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (X x) =
          aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1))
            (Sum.elim (fun _ => G (0, d.jc c)) (fun ik => G (ik.1, (d.jc c).succAbove ik.2)) x) := by
      rintro (_ | ⟨i, k⟩)
      · rw [Sum.elim_inl, ← hG]
        simp [Data.sH, sHom, genericImage_base]
      · rw [Sum.elim_inr, ← hG]
        simp [Data.sH, sHom, genericImage_succAbove]
    obtain ⟨π, hπ⟩ := uniformizer_of_residue_indep w hw.1
      (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1))
      (fun e => (hw.2 (X e.1)).1) hindW _ hg
    exact ⟨π, hπ⟩
  exact ⟨⟨hNorm, Or.inr ⟨hvK, hRC⟩⟩, hvK, j0, hw0, fun j => hint j, hunit⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0

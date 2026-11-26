module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNonzeroLocusEqOfIsAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_nonzeroLocus_eq_of_isAffineOpen : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ W : X.Opens, IsAffineOpen W → (W : Set X).Nonempty → ∃ (L : LB X) (s : LB.Sec L), L.IsLB ∧ Out.nonzeroLocus s = W :=
  fun X _ _ _ _ h W hW hne => GlobalTheory.AffineComplement.exists_nonzeroLocus_eq X W hW hne h

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf

theorem exists_basicOpen_factor : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  intro k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h
  let U : (Spec (CommRingCat.of B)).Opens := φ.left ⁻¹ᵁ j.left.opensRange
  let p₀ : PrimeSpectrum F := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum B := PrimeSpectrum.comap (δ : B →+* F) p₀
  have hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left := by
    have := congrArg (fun x => x.left) h
    simpa only [Over.comp_left] using this
  have hp : p ∈ (U : Set (Spec (CommRingCat.of B))) := by
    refine ⟨(algOverHom χ₀).left p₀, ?_⟩
    have := congrArg (fun x => x p₀) hl
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  obtain ⟨_, ⟨e, rfl⟩, he, heU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩
  intro B' _ _ ρ hρ
  have hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e := by
      intro hm
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)
    rw [Scheme.Hom.comp_apply]
    exact heU hq
  have hf := IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr
  let ψ : algOver k B' ⟶ algOver k A :=
    Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by
      rw [← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective ψ
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

end GlobalTheory.SS.ArcInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_factor_fieldPoint_affineOpen : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  first | exact @GlobalTheory.SS.ArcInf.exists_basicOpen_factor | exact GlobalTheory.SS.ArcInf.exists_basicOpen_factor | (intros; apply GlobalTheory.SS.ArcInf.exists_basicOpen_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesGenericRelationChainStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesGenericRelationChain
namespace GlobalTheory

theorem powerSeries_generic_relation_chain :
    ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by
  intro k _ _ ρ Gen hs ht hg
  have h1 : ∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) →
      w.order = (m : ℕ∞) → ρ z w := by
    intro m n hmn z w hz hw
    obtain ⟨S, hS, hzS⟩ := hg m n hmn z hz
    obtain ⟨T, hT, hwT⟩ := hg m n hmn w hw
    obtain ⟨t, htt⟩ := (hS.union hT).exists_notMem
    simp only [Set.mem_union, not_or] at htt
    exact ht _ _ _ (hzS t htt.1) (hs _ _ (hwT t htt.2))
  refine ⟨h1, fun m₀ hG => ?_⟩
  have h2 : ∀ m, m₀ ≤ m → ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
      ρ z (PowerSeries.X ^ m₀) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun z hz => h1 _ _ (hG _ le_rfl) _ _ hz (PowerSeries.order_X_pow _)
    | succ m hm ih =>
      intro z hz
      obtain ⟨S, hS, hXS⟩ := hg m _ (hG m hm) (PowerSeries.X ^ m) (PowerSeries.order_X_pow _)
      obtain ⟨t, htt⟩ := (hS.insert 0).exists_notMem
      simp only [Set.mem_insert_iff, not_or] at htt
      have ho : (PowerSeries.C t * PowerSeries.X ^ (m + 1) : PowerSeries k).order
          = ((m + 1 : ℕ) : ℕ∞) := by
        rw [PowerSeries.X_pow_eq, ← PowerSeries.monomial_zero_eq_C_apply,
          PowerSeries.monomial_mul_monomial, zero_add, mul_one]
        exact PowerSeries.order_monomial_of_ne_zero _ _ htt.1
      exact ht _ _ _ (h1 _ _ (hG _ (Nat.le_succ_of_le hm)) _ _ hz ho)
        (ht _ _ _ (hs _ _ (hXS t htt.2)) (ih _ (PowerSeries.order_X_pow _)))
  intro m n z w hm hn hz hw
  exact ht _ _ _ (h2 m hm z hz) (hs _ _ (h2 n hn w hw))

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relation_of_gen_of_order_eq : ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by
  first | exact @GlobalTheory.powerSeries_generic_relation_chain | exact GlobalTheory.powerSeries_generic_relation_chain | (intros; apply GlobalTheory.powerSeries_generic_relation_chain <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineUnitChartSmoothGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineUnitChartSmoothGroupScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_isChart : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  intro k _ G _ hG
  have hs : Smooth G.hom := hG.2.1
  let e : algOver k k ⟶ G := 1
  let x0 : (Sp k) := IsLocalRing.closedPoint k
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left) (x := e.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  have hft : Algebra.FiniteType k R := by
    have h1 : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h1
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    have : y = x0 := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]; exact hx
  let l : algOver k k ⟶ algOver k R := Over.homMk (IsOpenImmersion.lift i e.left hr) (by
    have := Over.w e
    rw [← this]
    show _ ≫ Spec.map φ = _
    rw [hφ, IsOpenImmersion.lift_fac_assoc])
  obtain ⟨ε, hε⟩ := algOverHom_surjective l
  obtain ⟨s, hsg⟩ := hft.out
  refine ⟨R, inferInstance, inferInstance, j, ε, s.card,
    fun n => (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n)), hi, ?_, ?_, ?_⟩
  · rw [hε]
    ext1
    exact IsOpenImmersion.lift_fac i e.left hr
  · rw [eq_top_iff, ← hsg, Algebra.adjoin_le_iff]
    intro a ha
    have h1 : a - algebraMap k R (ε a) ∈ Algebra.adjoin k (Set.range fun n =>
        (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n))) :=
      Algebra.subset_adjoin ⟨s.equivFin ⟨a, ha⟩, by simp⟩
    have h2 := add_mem h1 (Subalgebra.algebraMap_mem _ (ε a))
    simpa using h2
  · intro n
    simp

end GlobalTheory.SS.ArcInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineUnitChartSmoothGroupSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  first | exact @GlobalTheory.SS.ArcInf.exists_isChart | exact GlobalTheory.SS.ArcInf.exists_isChart | (intros; apply GlobalTheory.SS.ArcInf.exists_isChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcs
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcs
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS

private lemma weight_fin_two (m n : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) e = m * e 0 + n * e 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm]

private lemma leading_polynomial_eq_zero_iff_lt_weightedOrder {k : Type} [Field k] {m n : ℕ} (hm : 1 ≤ m)
    (f : MvPowerSeries (Fin 2) k) {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)) = 0 ↔
      (D : ℕ∞) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f := by
  have hcoeff : ∀ e ∈ S,
      (∑ e' ∈ S, Polynomial.C (MvPowerSeries.coeff e' f) * Polynomial.X ^ (e' 1)).coeff (e 1) =
        MvPowerSeries.coeff e f := by
    intro e he
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single e]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · intro e' he' hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h1
      apply hne
      have w1 := (hS e').1 he'
      have w2 := (hS e).1 he
      rw [weight_fin_two] at w1 w2
      rw [h1] at w2
      have h0 : e' 0 = e 0 :=
        Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel (w1.trans w2.symm))
      ext i
      fin_cases i
      · exact h0
      · exact h1.symm
    · intro h; exact absurd he h
  constructor
  · intro h0
    by_contra hlt
    push_neg at hlt
    have heq : MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f = D := le_antisymm hlt hD
    obtain ⟨e, hne, hwe⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder
      (![m, n] : Fin 2 → ℕ) (f := f) (by rw [heq]; rfl)
    rw [heq, Nat.cast_inj] at hwe
    have := hcoeff e ((hS e).2 hwe)
    rw [h0, Polynomial.coeff_zero] at this
    exact hne this.symm
  · intro hlt
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (by rw [(hS e).1 he]; exact hlt),
      map_zero, zero_mul]

private lemma prod_pow_fin_two {k : Type} [Field k] (z w : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    (e.prod fun s j => (![z, w] : Fin 2 → PowerSeries k) s ^ j) = z ^ e 0 * w ^ e 1 := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl

open PowerSeries in
private lemma coeff_pow_mul_pow_of_le_order {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order) (a b : ℕ) :
    (∀ j < m * a + n * b, coeff j (z ^ a * w ^ b) = 0) ∧
      coeff (m * a + n * b) (z ^ a * w ^ b) = coeff m z ^ a * coeff n w ^ b := by
  obtain ⟨z', rfl⟩ : X ^ m ∣ z := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hz)
  obtain ⟨w', rfl⟩ : X ^ n ∣ w := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hw)
  have hprod : (X ^ m * z') ^ a * (X ^ n * w') ^ b = X ^ (m * a + n * b) * (z' ^ a * w' ^ b) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
  rw [hprod]
  refine ⟨fun j hj => by rw [coeff_X_pow_mul', if_neg (by omega)], ?_⟩
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff, map_mul, map_pow,
    map_pow]

private lemma coeff_subst_eq_zero_of_lt {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {f : MvPowerSeries (Fin 2) k}
    {D : ℕ} (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f) {j : ℕ}
    (hj : j < D) : PowerSeries.coeff j (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) = 0 := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases hlt : Finsupp.weight (![m, n] : Fin 2 → ℕ) e < D
  · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
      (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
  · rw [weight_fin_two] at hlt
    rw [prod_pow_fin_two, ← PowerSeries.coeff,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 j (by omega), smul_zero]

private lemma coeff_subst_eq_pow_mul_eval_leading {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {s t : k}
    (hzs : PowerSeries.coeff m z = s ^ m) (hwt : PowerSeries.coeff n w = s ^ n * t)
    {f : MvPowerSeries (Fin 2) k} {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    PowerSeries.coeff D (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) =
      s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := S)]
  · rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hwe := (hS e).1 he
    rw [weight_fin_two] at hwe
    rw [prod_pow_fin_two, ← PowerSeries.coeff, ← hwe,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).2, hzs, hwt]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    rw [pow_add, pow_mul, pow_mul]
    ring
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.mem_coe, hS]
    by_contra hne
    apply he
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
        (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
    · rw [weight_fin_two] at hgt
      rw [prod_pow_fin_two, ← PowerSeries.coeff,
        (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 D (by omega), smul_zero]

theorem _root_.GlobalTheory.SS.exists_polynomial_leading_quotient_subst :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  intro k _ _ m n hm hn r h d hd hdh
  have hfin : ((MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat : ℕ∞) =
      MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d :=
    ENat.coe_toNat ((MvPowerSeries.weightedOrder_eq_top_iff _).not.2 hd)
  set D := (MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat with hD_def
  have hWpos : ∀ x, (![m, n] : Fin 2 → ℕ) x ≠ 0 := by
    intro x; fin_cases x <;> simp <;> omega
  set S := (Finsupp.finite_of_nat_weight_le _ hWpos D).toFinset.filter
    fun e => Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D with hS_def
  have hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D := by
    intro e
    simp only [hS_def, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have hDd : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d := hfin.le
  have hDh : ∀ i, (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) :=
    fun i => hfin.le.trans (hdh i)
  refine ⟨∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e d) * Polynomial.X ^ (e 1),
    fun i => ∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e (h i)) * Polynomial.X ^ (e 1), ?_, ?_, ?_⟩
  · intro h0
    have := (leading_polynomial_eq_zero_iff_lt_weightedOrder hm d hDd S hS).1 h0
    rw [hfin] at this
    exact lt_irrefl _ this
  · intro i
    rw [leading_polynomial_eq_zero_iff_lt_weightedOrder hm (h i) (hDh i) S hS, hfin]
  · intro s t z w hs0 hz hw hzs hwt hPd
    have hz0 : PowerSeries.coeff 0 z = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)
    have hw0 : PowerSeries.coeff 0 w = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hn) hw)
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hz0 hw0
    have hsub : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        fin_cases i
        · exact hz0
        · exact hw0
    have factor : ∀ f : MvPowerSeries (Fin 2) k,
        (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f →
        ∃ g : PowerSeries k, MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f =
          PowerSeries.X ^ D * g ∧ PowerSeries.constantCoeff g =
            s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
      intro f hf
      obtain ⟨g, hg⟩ := PowerSeries.X_pow_dvd_iff.2 fun j hj =>
        coeff_subst_eq_zero_of_lt hz hw hsub hf hj
      refine ⟨g, hg, ?_⟩
      have := coeff_subst_eq_pow_mul_eval_leading hz hw hsub hzs hwt hf S hS
      rw [hg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff] at this
      exact this
    obtain ⟨gd, hgd, hgd0⟩ := factor d hDd
    have hgd0' : PowerSeries.constantCoeff gd ≠ 0 := by
      rw [hgd0]; exact mul_ne_zero (pow_ne_zero _ hs0) hPd
    refine ⟨?_, fun i => (factor (h i) (hDh i)).choose * gd⁻¹, fun i => ?_⟩
    · rw [hgd]
      exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
        fun h0 => hgd0' (by rw [h0, map_zero])
    · obtain ⟨hgi, hgi0⟩ := (factor (h i) (hDh i)).choose_spec
      constructor
      · rw [hgd, hgi, show (factor (h i) (hDh i)).choose * gd⁻¹ * (PowerSeries.X ^ D * gd) =
          PowerSeries.X ^ D * (factor (h i) (hDh i)).choose * (gd * gd⁻¹) by ring,
          PowerSeries.mul_inv_cancel _ hgd0', _root_.mul_one]
      · rw [map_mul, PowerSeries.constantCoeff_inv, hgi0, hgd0]
        field_simp

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leading_quotient_weighted_arcs : ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  first | exact @GlobalTheory.SS.exists_polynomial_leading_quotient_subst | exact GlobalTheory.SS.exists_polynomial_leading_quotient_subst | (intros; apply GlobalTheory.SS.exists_polynomial_leading_quotient_subst <;> assumption)
end
end

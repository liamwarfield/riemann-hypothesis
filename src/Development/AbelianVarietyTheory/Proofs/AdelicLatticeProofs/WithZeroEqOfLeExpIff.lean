module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem _root_.GlobalTheory.QNorm.intValuation_of_eq_comap {R : Type} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w w' : HeightOneSpectrum R) (h : w'.asIdeal = w.asIdeal.comap e) (x : R) :
    w'.intValuation x = w.intValuation (e x) := by
  have hmem : ∀ n : ℕ, x ∈ w'.asIdeal ^ n ↔ e x ∈ w.asIdeal ^ n := by
    intro n
    rw [h, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hle : ∀ n : ℕ, w'.intValuation x ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (e x) ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, hmem]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hex : e x ≠ 0 := fun h0 => hx (e.injective (h0.trans (map_zero e).symm))
    rw [HeightOneSpectrum.intValuation_if_neg _ hx, HeightOneSpectrum.intValuation_if_neg _ hex]
      at hle ⊢
    set a := (Associates.mk w'.asIdeal).count (Associates.mk (Ideal.span {x})).factors
    set b := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {e x})).factors
    have h1 := (hle a).1 le_rfl
    have h2 := (hle b).2 le_rfl
    simp only [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
    rw [le_antisymm h1 h2]

theorem _root_.GlobalTheory.QNorm.valuation_of_eq_comap {E : Type} [Field E] [NumberField E] (σ : E ≃+* E)
    (w w' : HeightOneSpectrum (𝓞 E))
    (h : w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ)) (y : E) :
    w'.valuation E y = w.valuation E (σ y) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hσ : ∀ r : 𝓞 E, σ (algebraMap (𝓞 E) E r) =
      algebraMap (𝓞 E) E (RingOfIntegers.mapRingEquiv σ r) := fun r => rfl
  rw [map_div₀ σ, hσ, hσ, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [_root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h a,
    _root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h b]

private lemma ringOfIntegers_mapRingEquiv_algebraMap {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : 𝓞 F) :
    RingOfIntegers.mapRingEquiv (σ : E ≃+* E) (algebraMap (𝓞 F) (𝓞 E) n) =
      algebraMap (𝓞 F) (𝓞 E) n := by
  ext
  rw [show ((algebraMap (𝓞 F) (𝓞 E) n : 𝓞 E) : E) = algebraMap F E (n : F) from rfl]
  exact σ.commutes _

private lemma exists_algebraMap_eq_mul_conj_of_isQuad {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (x : 𝓞 E) :
    ∃ n : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) n = x * RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x := by
  obtain ⟨a, b, hab⟩ := hq.span (x : E)
  have hprod : (x : E) * σ (x : E) = algebraMap F E (a ^ 2 - b ^ 2 * δ) := by
    rw [hab]
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hq.conj]
    rw [map_sub, map_mul, map_pow, map_pow, ← hq.sq]
    ring
  have hint : IsIntegral ℤ (algebraMap F E (a ^ 2 - b ^ 2 * δ)) := by
    rw [← hprod]
    exact (RingOfIntegers.isIntegral_coe x).mul
      (RingOfIntegers.isIntegral_coe (RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x))
  refine ⟨⟨a ^ 2 - b ^ 2 * δ,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).mp hint⟩, ?_⟩
  ext
  exact hprod.symm

theorem _root_.GlobalTheory.QNorm.conj_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (σ y)) ∧
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      w' = w ∨ ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  intro F E _ _ _ _ _ δ θ σ hq
  set e := RingOfIntegers.mapRingEquiv (σ : E ≃+* E) with he
  refine ⟨fun w => ?_, fun w w' hunder => ?_⟩
  · refine ⟨HeightOneSpectrum.comap (e : 𝓞 E →+* 𝓞 E) e.surjective w, ?_, fun y =>
      _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w _ rfl y⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    ext n
    change e (algebraMap (𝓞 F) (𝓞 E) n) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal
    rw [he, ringOfIntegers_mapRingEquiv_algebraMap]
  · by_cases hw : w' = w
    · exact Or.inl hw
    right
    refine _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w w' ?_
    by_contra hne
    have h1 : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
      hw (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
    have h2 : ¬ w'.asIdeal ≤ w.asIdeal.comap e := fun hle =>
      hne (w'.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle)
    have hns : ¬ ((w'.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ (w.asIdeal.comap e)) :=
      fun hs => (Ideal.subset_union.mp hs).elim h1 h2
    rw [Set.not_subset] at hns
    obtain ⟨x, hx, hxn⟩ := hns
    simp only [Set.mem_union, SetLike.mem_coe, Ideal.mem_comap, not_or] at hxn
    obtain ⟨n, hn⟩ := exists_algebraMap_eq_mul_conj_of_isQuad hq x
    have hnw' : n ∈ (w'.under (𝓞 F)).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal]
      change algebraMap (𝓞 F) (𝓞 E) n ∈ w'.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [hunder, HeightOneSpectrum.under_asIdeal] at hnw'
    change algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal at hnw'
    rw [hn] at hnw'
    rcases w.isPrime.mem_or_mem hnw' with h | h
    · exact hxn.1 h
    · exact hxn.2 h

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem finite_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := hv
  have h0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact x.ne_zero
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact one_lt_inv₀ (zero_lt_iff.mpr h0) |>.mpr h
  · left
    exact h

theorem exists_superset_mem_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (X : Finset Fˣ)
      (S₀ : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ S, S₀ ⊆ S ∧ ∀ S', S ⊆ S' → ∀ x ∈ X, x ∈ sUnits F S' := by
  intro F _ _ X S₀
  classical
  have hT : (⋃ x ∈ X, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}).Finite :=
    X.finite_toSet.biUnion fun x _ => finite_valuation_ne_one F x
  refine ⟨S₀ ∪ hT.toFinset, Finset.subset_union_left, ?_⟩
  intro S' hS' x hx
  rw [mem_sUnits]
  intro v hv
  by_contra h
  apply hv
  apply hS'
  apply Finset.mem_union_right
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_biUnion hx h

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem _root_.GlobalTheory.QNorm.finite_places_over (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

theorem _root_.GlobalTheory.QNorm.places_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
  intro F E _ _ _ _ _
  refine ⟨fun S => ?_, fun v => ?_, fun w => ?_⟩
  · have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
      have hU : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S} =
          ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
        ext w; simp
      rw [hU]
      exact S.finite_toSet.biUnion fun v _ => _root_.GlobalTheory.QNorm.finite_places_over F E v
    exact ⟨hfin.toFinset, fun w => by simp⟩
  · obtain ⟨P, hmax, hover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 E)
    have hne : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
    exact ⟨⟨P, hmax.isPrime, hne⟩, HeightOneSpectrum.ext hover.over.symm⟩
  · haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    refine ⟨(w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal, Nat.pos_of_ne_zero ?_,
      fun x => ?_⟩
    · refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ w.isPrime Ideal.map_comap_le
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact (w.under (𝓞 F)).ne_bot
    · rw [Ideal.ramificationIdx'_eq_ramificationIdx
        (w.under (𝓞 F)).asIdeal w.asIdeal (w.under (𝓞 F)).ne_bot]
      exact (HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x).symm

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSetStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightOneSpectrum_places_over_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
  first | exact @GlobalTheory.QNorm.places_over | exact GlobalTheory.QNorm.places_over | (intros; apply GlobalTheory.QNorm.places_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open scoped MonoidAlgebra

private theorem subalgebra_end_eq_whole_of_isSimpleModule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSimpleModule A V] :
    A = ⊤ := by
  classical
  have schur : ∀ f : V →ₗ[A] V, ∃ c : ℂ, ∀ y, f y = c • y := by
    intro f
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f
    exact ⟨c, fun y => by rw [← hc]; rfl⟩
  let b := Module.finBasis ℂ V
  let ι := Fin (Module.finrank ℂ V)
  let N : Submodule A (ι → V) := Submodule.span A {fun i => b i}
  obtain ⟨W, hW⟩ := exists_isCompl N
  let P : (ι → V) →ₗ[A] (ι → V) := N.subtype.comp (Submodule.linearProjOfIsCompl N W hW)
  have hPN : ∀ x, P x ∈ N := fun x => (Submodule.linearProjOfIsCompl N W hW x).2
  have hPfix : ∀ x ∈ N, P x = x := fun x hx => by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩)
  have hcomm : ∀ (T : Module.End ℂ V) (x : ι → V), P (fun i => T (x i)) = fun i => T (P x i) := by
    intro T x
    have hsingle : ∀ (i j : ι) (y : V), P (Pi.single j (T y)) i = T (P (Pi.single j y) i) := by
      intro i j y
      obtain ⟨c, hc⟩ := schur ((LinearMap.proj i).comp (P.comp (LinearMap.single A (fun _ : ι => V) j)))
      have h1 := hc (T y)
      have h2 := hc y
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply] at h1 h2
      rw [h1, h2, map_smul]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← Finset.univ_sum_single (fun i => T (x i)), map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, map_sum, hsingle]
  ext T
  simp only [Algebra.mem_top, iff_true]
  have hmem : (fun i => T (b i)) ∈ N := by
    have hfix : P (fun i => T (b i)) = fun i => T (b i) := by
      rw [hcomm T (fun i => b i), hPfix _ (Submodule.mem_span_singleton_self _)]
    rw [← hfix]
    exact hPN _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have hT : T = (a : Module.End ℂ V) := by
    refine b.ext fun i => ?_
    have := congrFun ha i
    exact this.symm
  rw [hT]
  exact a.2

theorem _root_.GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by
  intro G _ V _ _ ρ _ h
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)
  have hρA : ∀ g, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  have hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V)) :=
      (MonoidHom.coe_mrange ρ).symm
    rw [this, Submonoid.closure_eq]
  let φ : Submodule A V → Subrepresentation ρ := fun M =>
    ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩
  haveI : IsSimpleModule A V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun M => ?_ }
    · obtain ⟨S, S', hS'⟩ := h.exists_pair_ne
      have hzero : ∀ x : V, x = 0 := fun x => by
        have : x ∈ (⊤ : Submodule A V) := Submodule.mem_top
        rw [← hbt] at this
        exact (Submodule.mem_bot A).1 this
      have hall : ∀ T U : Subrepresentation ρ, T = U := fun T U => by
        apply Subrepresentation.ext
        ext x
        rw [hzero x]
        exact ⟨fun _ => U.toSubmodule.zero_mem, fun _ => T.toSubmodule.zero_mem⟩
      exact hS' (hall S S')
    · rcases h.eq_bot_or_eq_top (φ M) with hM | hM
      · left
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this
      · right
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 this
  rw [← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]
  ext x
  simp

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Calc

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem hf_add_left (x x' y : Fin n → R) : hf σ G (x + x') y = hf σ G x y + hf σ G x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y y' : Fin n → R) : hf σ G x (y + y') = hf σ G x y + hf σ G x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : R) (x y : Fin n → R) : hf σ G (c • x) y = c * hf σ G x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : R) (x y : Fin n → R) : hf σ G x (c • y) = σ c * hf σ G x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_conj (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) :
    σ (hf σ G x y) = hf σ G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem tv_mulVec (x : Fin n → R) (t : R) (v : Fin n → R) :
    tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [hf]
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem tv_mul (x : Fin n → R) (t t' : R) :
    tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x) := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, tv_mulVec, hf_add_left, hf_smul_left,
    add_assoc, ← add_smul]
  congr 2
  ring

theorem tv_det (x : Fin n → R) (t : R) : (tv σ G x t).det = 1 + t * hf σ G x x := by
  have h : tv σ G x t = 1 + Matrix.replicateCol Unit (t • x) *
      Matrix.replicateRow Unit (fun b => ∑ e, G b e * σ (x e)) := by
    rw [tv]
    congr 1
    ext a b
    simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem isU_tv (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hf_conj σ G hσ hG]
  linear_combination (hf σ G v x * hf σ G x w) * h

theorem conj_tv (γ : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) (h : IsU σ G γ) :
    γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, h, Matrix.mulVec_add,
    Matrix.mulVec_smul]

theorem tv_smul (a : R) (x : Fin n → R) (t : R) :
    tv σ G (a • x) t = tv σ G x (t * a * σ a) := by
  refine ext_mulVec fun v => ?_
  rw [tv_mulVec, tv_mulVec, hf_smul_right, smul_smul]
  congr 2
  ring

theorem isU_mul (γ γ' : Matrix (Fin n) (Fin n) R) (h : IsU σ G γ) (h' : IsU σ G γ') :
    IsU σ G (γ * γ') := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, h']

theorem calculus : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) :=
  fun _ _ _ σ G hσ hG => ⟨hf_conj σ G hσ hG, tv_mulVec σ G, tv_mul σ G, tv_det σ G, isU_tv σ G hσ hG,
    conj_tv σ G, tv_smul σ G, isU_mul σ G⟩

end GlobalTheory.UTrans.Calc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitaryStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_identities_unitary : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) := by
  first | exact @GlobalTheory.UTrans.Calc.calculus | exact GlobalTheory.UTrans.Calc.calculus | (intros; apply GlobalTheory.UTrans.Calc.calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]

omit [Fintype ι] in
theorem tpow_diagonal_alg (n : ℕ) (a : ι → R) :
    tpow n (diagonal a) = diagonal (fun b : Fin n → ι => ∏ j, a (b j)) := by
  ext b c
  simp only [tpow, Matrix.of_apply]
  by_cases h : b = c
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Matrix.diagonal_apply_ne _ hj)

omit [Fintype ι] in
theorem tpow_one_alg (n : ℕ) : tpow n (1 : Matrix ι ι R) = 1 := by
  have h := tpow_diagonal_alg (ι := ι) n (fun _ => (1 : R))
  simpa using h

omit [DecidableEq ι] in
theorem tpow_mul_alg (n : ℕ) (y z : Matrix ι ι R) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext b c
  simp only [tpow, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]

theorem act_apply_alg {m : ℕ} (d : Fin m → ℕ) (t : TIdx ι d → R) (y : Matrix ι ι R) (k : TIdx ι d) :
    act d t y k = ∑ a : Fin (d k.1) → ι, t ⟨k.1, a⟩ * ∏ j, y (a j) (k.2 j) := by
  simp [act, tpow, Matrix.vecMul, dotProduct]

end

theorem tpow_act_algebra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R], (∀ n : ℕ, tpow n (1 : Matrix ι ι R) = 1 ∧ (∀ y z : Matrix ι ι R, tpow n (y * z) = tpow n y * tpow n z) ∧ ∀ y : Matrix ι ι R, (tpow n y)ᵀ = tpow n yᵀ) ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → R), act d t 1 = t ∧ (∀ y z : Matrix ι ι R, act d t (y * z) = act d (act d t y) z) ∧ (∀ (a : ι → R) (k : TIdx ι d), act d t (diagonal a) k = t k * ∏ j, a (k.2 j)) ∧ (∀ (S : Subring R) (y : Matrix ι ι R), (∀ k, t k ∈ S) → (∀ i j, y i j ∈ S) → ∀ k, act d t y k ∈ S) ∧ (∀ (c : R) (y : Matrix ι ι R), act d (c • t) y = c • act d t y) ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (y : Matrix ι ι R), act d (fun k => φ (t k)) (y.map φ) = fun k => φ (act d t y k) := by
  intro ι _ _ R _
  refine ⟨fun n => ⟨tpow_one_alg n, tpow_mul_alg n, fun y => ?_⟩, fun m d t => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ext a b
    simp [tpow]
  · funext k
    simp [act, tpow_one_alg]
  · intro y z
    funext k
    simp only [act, tpow_mul_alg, ← Matrix.vecMul_vecMul]
  · intro a k
    simp only [act, tpow_diagonal_alg, Matrix.vecMul_diagonal]
  · intro S y ht hy k
    rw [act_apply_alg]
    exact S.sum_mem fun a _ => S.mul_mem (ht _) (S.prod_mem fun j _ => hy _ _)
  · intro c y
    funext k
    simp only [act_apply_alg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · intro R' _ φ y
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [act_apply_alg, map_sum, map_mul, map_prod, Matrix.map_apply]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebraStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R], (∀ n : ℕ, tpow n (1 : Matrix ι ι R) = 1 ∧ (∀ y z : Matrix ι ι R, tpow n (y * z) = tpow n y * tpow n z) ∧ ∀ y : Matrix ι ι R, (tpow n y)ᵀ = tpow n yᵀ) ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → R), act d t 1 = t ∧ (∀ y z : Matrix ι ι R, act d t (y * z) = act d (act d t y) z) ∧ (∀ (a : ι → R) (k : TIdx ι d), act d t (diagonal a) k = t k * ∏ j, a (k.2 j)) ∧ (∀ (S : Subring R) (y : Matrix ι ι R), (∀ k, t k ∈ S) → (∀ i j, y i j ∈ S) → ∀ k, act d t y k ∈ S) ∧ (∀ (c : R) (y : Matrix ι ι R), act d (c • t) y = c • act d t y) ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (y : Matrix ι ι R), act d (fun k => φ (t k)) (y.map φ) = fun k => φ (act d t y k) := by
  first | exact @GlobalTheory.ClassFin.tpow_act_algebra | exact GlobalTheory.ClassFin.tpow_act_algebra | (intros; apply GlobalTheory.ClassFin.tpow_act_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem intValuation_of_span_eq_mul {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ 0) (hv : ¬ v.asIdeal ∣ I) (x : R)
    (hx0 : x ≠ 0) (hx : v.asIdeal * I = Ideal.span {x}) :
    v.intValuation x = WithZero.exp (-1) := by
  have hvd : v.asIdeal ∣ Ideal.span {x} := ⟨I, hx.symm⟩
  have hsq : ¬ v.asIdeal ^ 2 ∣ Ideal.span {x} := by
    rintro ⟨J, hJ⟩
    apply hv
    rw [← hx, pow_two, mul_assoc] at hJ
    exact ⟨J, mul_left_cancel₀ v.ne_bot hJ⟩
  have h1 : v.intValuation x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd x 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation x ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hsq ((v.intValuation_le_pow_iff_dvd x 2).1 h)
  have hne : v.intValuation x ≠ 0 := v.intValuation_ne_zero x hx0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

theorem exists_admissible_superset_finite_places : ∀ (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))), ∃ S, S₀ ⊆ S ∧ admitted F S := by
  intro F _ _ S₀
  classical
  choose J hJ using fun c : ClassGroup (𝓞 F) => ClassGroup.mk0_surjective c
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have hprod : (∏ c : ClassGroup (𝓞 F), (J c : Ideal (𝓞 F))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro c _
    exact nonZeroDivisors.coe_ne_zero (J c)
  have hs : Ideal.span {(2 : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h2
  obtain ⟨M, hM, hM2, hMJ⟩ : ∃ M : Ideal (𝓞 F), M ≠ 0 ∧ Ideal.span {(2 : 𝓞 F)} ∣ M ∧
      ∀ c, (J c : Ideal (𝓞 F)) ∣ M :=
    ⟨_, mul_ne_zero hs hprod, dvd_mul_right _ _,
      fun c => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _⟩
  obtain ⟨S, hS0, hSM⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u.asIdeal ∣ M → u ∈ S :=
    ⟨S₀ ∪ (Ideal.finite_factors hM).toFinset, Finset.subset_union_left,
      fun u h => Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)⟩
  have hout : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → ¬ u.asIdeal ∣ M :=
    fun u hu h => hu (hSM u h)
  have houtJ : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → ∀ c, ¬ u.asIdeal ∣ (J c : Ideal (𝓞 F)) :=
    fun u hu c h => hout u hu (h.trans (hMJ c))
  refine ⟨S, hS0, ?_⟩
  intro v hv
  refine ⟨?_, ?_⟩
  · have h2 : ¬ v.asIdeal ∣ Ideal.span {(2 : 𝓞 F)} := fun h => hout v hv (h.trans hM2)
    have key : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun hm => h2 (Ideal.dvd_span_singleton.2 hm)
    rwa [map_ofNat] at key
  · let P : nonZeroDivisors (Ideal (𝓞 F)) := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
    let c : ClassGroup (𝓞 F) := (ClassGroup.mk0 P)⁻¹
    have hprod : ClassGroup.mk0 (P * J c) = 1 := by
      rw [map_mul, hJ c, mul_inv_cancel]
    have hprin : (v.asIdeal * (J c : Ideal (𝓞 F))).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (P * J c).2).1 hprod
    obtain ⟨y, hy⟩ := hprin.principal
    have hy' : v.asIdeal * (J c : Ideal (𝓞 F)) = Ideal.span {y} := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hy'
      exact (mul_ne_zero v.ne_bot (nonZeroDivisors.coe_ne_zero (J c))) hy'
    refine ⟨algebraMap (𝓞 F) F y, ?_, ?_⟩
    · rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact intValuation_of_span_eq_mul v _ (nonZeroDivisors.coe_ne_zero _) (houtJ v hv c) y hy0 hy'
    · intro w hw hwv
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hyw
      have hdvd : w.asIdeal ∣ v.asIdeal * (J c : Ideal (𝓞 F)) := by
        rw [hy']
        exact Ideal.dvd_span_singleton.2 hyw
      rcases (Ideal.prime_of_isPrime w.ne_bot w.isPrime).dvd_or_dvd hdvd with h | h
      · apply hwv
        have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd h
        exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
      · exact houtJ w hw c h

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem GlobalTheory.QNorm.exists_ringHom_adicCompletion_under :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (w : HeightOneSpectrum (𝓞 E)),
      ∃ φ : (w.under (𝓞 F)).adicCompletion F →+* w.adicCompletion E,
        ∀ x : F, φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
          algebraMap E (w.adicCompletion E) (algebraMap F E x) := by
  intro K L _ _ _ _ _ w
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K))
    w).continuous
  refine ⟨((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K (w.under (𝓞 K))).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_unit_valuation_eq_of_adm :
    ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
      (n : HeightOneSpectrum (𝓞 F) → ℤ), admitted F S → (∀ v, v ∉ T → n v = 0) →
      ∃ a : Fˣ, ∀ v, v ∉ S → v.valuation F (a : F) = WithZero.exp (n v) := by
  intro F _ _ S T n hS hT
  classical
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ π : Fˣ,
      v.valuation F (π : F) = WithZero.exp (-1) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (π : F) = 1 := by
    intro v hv
    obtain ⟨-, π, h1, h2⟩ := hS v hv
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    exact ⟨Units.mk0 π hπ0, h1, h2⟩
  choose! π hπ1 hπ2 using key
  refine ⟨∏ w ∈ T.filter (· ∉ S), (π w) ^ (-n w), ?_⟩
  intro v hv
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, map_prod, map_zpow₀]
  by_cases hvT : v ∈ T
  · rw [Finset.prod_eq_single v]
    · rw [hπ1 v hv, ← WithZero.exp_zsmul]
      congr 1
      simp
    · intro w hw hwv
      rw [hπ2 w (Finset.mem_filter.1 hw).2 v hv (Ne.symm hwv), one_zpow]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨hvT, hv⟩) h
  · rw [hT v hvT, WithZero.exp_zero]
    refine Finset.prod_eq_one fun w hw => ?_
    have hne : v ≠ w := fun h => hvT (h ▸ (Finset.mem_filter.1 hw).1)
    rw [hπ2 w (Finset.mem_filter.1 hw).2 v hv hne, one_zpow]

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range :
    ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  intro G _ W _ _ ρ J V _ _ r p hr hp htop
  let f : ∀ j, (r j).IntertwiningMap ρ := fun j => ⟨p j, fun g => LinearMap.ext fun v => hp j g v⟩
  let F : ∀ j, (r j).asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    fun j => Representation.IntertwiningMap.equivLinearMapAsModule (r j) ρ (f j)
  have hF : ∀ j (v : V j), F j v = p j v := fun j v => rfl
  have hs : ∀ j, IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (F j)) := by
    intro j
    haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (r j)).mp
      (hr j)
    exact IsSemisimpleModule.range (F j)
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hs ?_
  rw [eq_top_iff]
  intro x _
  have hx : (show W from x) ∈ ⨆ j, LinearMap.range (p j) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (fun j => LinearMap.range (p j))
    (motive := fun y : W => (show ρ.asModule from y) ∈ ⨆ j, LinearMap.range (F j)) hx ?_ ?_ ?_
  · rintro j y ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨v, hF j v⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariantStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant : ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_uniformizer_and_residue_representatives :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  intro F _ _ v
  classical
  have h2 : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have h3 : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.Idele.exists_valued_sub_le v hx 1
    refine ⟨a, lt_of_le_of_lt ha ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨?_, h2, h3, ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    exact ⟨π, hπ, (h2 π).trans hπ⟩
  · haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    choose s hs using Ideal.Quotient.mk_surjective (I := v.asIdeal)
    refine ⟨Finset.univ.image fun q : 𝓞 F ⧸ v.asIdeal =>
      algebraMap F (v.adicCompletion F) ((s q : 𝓞 F) : F), ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Finset.card_univ, Nat.card_eq_fintype_card]
    · intro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
      rw [h2]
      exact v.valuation_le_one (s q)
    · intro x hx
      obtain ⟨a, ha⟩ := h3 x hx
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ a, Finset.mem_univ _, rfl⟩, ?_⟩
      have hm : a - s (Ideal.Quotient.mk _ a) ∈ v.asIdeal := Ideal.Quotient.eq.1 (hs _).symm
      have hl : v.valuation F (algebraMap (𝓞 F) F (a - s (Ideal.Quotient.mk _ a))) < 1 :=
        (v.valuation_lt_one_iff_mem _).2 hm
      rw [← h2, map_sub, map_sub] at hl
      rw [← sub_add_sub_cancel x (algebraMap F (v.adicCompletion F) (a : F))]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hl)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_uniformizer_residue_representatives : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  first | exact @GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | exact GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | (intros; apply GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem _root_.GlobalTheory.QNorm.exists_approx_mod_squares :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  intro F _ _ S y z hy hz
  set U : Set ((∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    (⋂ v : S, {p | ‖p.1 v * y v - 1‖ < min ‖(4 : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ 1}) ∩
      ⋂ σ, {p | 0 < p.2 σ * z σ} with hUdef
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · exact isOpen_lt
        ((((continuous_apply v).comp continuous_fst).mul continuous_const).sub continuous_const).norm
        continuous_const
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  have hne : U.Nonempty := by
    refine ⟨(fun v => (y v)⁻¹, z), ?_⟩
    simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun v => ?_, fun σ => mul_self_pos.2 (hz σ)⟩
    rw [inv_mul_cancel₀ (hy v), sub_self, norm_zero, lt_min_iff]
    have h4 := (map_ne_zero (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).2
      (by norm_num : (4 : F) ≠ 0)
    rw [map_ofNat] at h4
    exact ⟨norm_pos_iff.2 h4, one_pos⟩
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.LocalQuad.denseRange_finite_real F S).exists_mem_open hU hne
  simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨hxS, hxR⟩ := hx
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨1, one_ne_zero, fun v hv => ?_, fun σ => ?_⟩
    · have h := hxS ⟨v, hv⟩
      simp at h
    · have h := hxR σ
      simp at h
  refine ⟨x, hx0, fun v hv => ?_, hxR⟩
  have h := (hxS ⟨v, hv⟩).trans_le (min_le_left _ _)
  exact _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ (Valued.toNormedField.norm_lt_iff.1 h)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquaresStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_mod_local_squares : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  first | exact @GlobalTheory.QNorm.exists_approx_mod_squares | exact GlobalTheory.QNorm.exists_approx_mod_squares | (intros; apply GlobalTheory.QNorm.exists_approx_mod_squares <;> assumption)
end
end

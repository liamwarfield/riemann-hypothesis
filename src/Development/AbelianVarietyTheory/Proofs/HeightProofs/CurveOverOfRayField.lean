module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayField
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

end Quadratic

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  open Polynomial in
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

end GlobalTheory.FieldSize.RayExistCurve
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassField
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassField
set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.InRayAny

set_option autoImplicit false in
private theorem weberSet_subset_of_isRay_span_natCast :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R := by
  intro K _ _ h2 hd L hL n hn R _ _ hR
  obtain ⟨hM, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hL n hn
  have hn0 : 0 < n := by omega
  have hN : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn0.ne'
  have hMR : IntermediateField.adjoin (↥K) (_root_.GlobalTheory.FieldSize.weberSet L n) ≤ R := by
    apply _root_.GlobalTheory.Bauer.le_of_finite_split_not_split (↥K) ℂ R _
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
      (S.sup id + Ideal.absNorm (Ideal.span {(n : 𝓞 K)}))).preimage
      (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro 𝔭 ⟨hp, hsplit, hnot⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hpS : Ideal.absNorm 𝔭.asIdeal ∈ S
    · exact le_add_right (Finset.le_sup (f := id) hpS)
    by_cases hn𝔭 : (n : 𝓞 K) ∈ 𝔭.asIdeal
    · refine le_add_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ?_)
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hn𝔭)
    · exfalso
      obtain ⟨π, hπ, hπ1⟩ :=
        (_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff (↥K) (↥R) n hn0 hR 𝔭 hn𝔭).mp hsplit
      apply hnot
      rw [hπ] at hp hpS ⊢
      exact hS π _ hp hpS rfl hπ1
  exact fun x hx => hMR (IntermediateField.subset_adjoin _ _ hx)

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.InRayAny.weberSet_subset :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R :=
  weberSet_subset_of_isRay_span_natCast

end GlobalTheory.FieldSize.InRayAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassFieldStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R], IsRay R (Ideal.span {(n : 𝓞 K)}) → weberSet L n ⊆ R := by
  first | exact @GlobalTheory.FieldSize.InRayAny.weberSet_subset | exact GlobalTheory.FieldSize.InRayAny.weberSet_subset | (intros; apply GlobalTheory.FieldSize.InRayAny.weberSet_subset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberTransport

theorem absNorm_comap {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : 𝓞 K ≃+* 𝓞 K')
    (I : Ideal (𝓞 K')) : Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

theorem containsRayField_congr {K L K' L' : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] (φ : K →+* L) (φ' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (hc : ∀ x, φ' (eK x) = eL (φ x)) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ' n := by
  intro P hP
  let oK := RingOfIntegers.mapRingEquiv eK
  let oL := RingOfIntegers.mapRingEquiv eL
  let Q : HeightOneSpectrum (𝓞 L) := (HeightOneSpectrum.equivOfRingEquiv oL).symm P
  have hQ : Q.asIdeal = P.asIdeal.comap oL := rfl
  obtain ⟨f, α, h1, h2, h3⟩ := h Q (by rw [hQ, Ideal.mem_comap, map_natCast]; exact hP)
  have hcm : Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) =
      (P.asIdeal.comap (RingOfIntegers.mapRingHom φ')).comap oK := by
    ext x
    rw [hQ]
    simp only [Ideal.mem_comap]
    have : RingOfIntegers.mapRingHom φ' (oK x) = oL (RingOfIntegers.mapRingHom φ x) :=
      RingOfIntegers.ext (hc x)
    rw [this]
  rw [hcm, absNorm_comap, hQ, absNorm_comap] at h1
  rw [hcm] at h2
  refine ⟨f, oK α, h1, ?_, ?_⟩
  · have := congrArg (Ideal.map oK) h2
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ oK.surjective, Ideal.map_span, Set.image_singleton] at this
  · have := map_dvd oK h3
    rwa [map_natCast, map_sub, map_one] at this

theorem weberIn_of_containsRayField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (ψ : L →+* ℂ), Module.finrank ℚ K = 2 → (∃ a : K, a ^ 2 = -(H.d : K)) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n → GlobalTheory.FinalJoin.WeberIn H ψ.toRatAlgHom.fieldRange n ∧ H.rt0 ∈ ψ.toRatAlgHom.fieldRange := by
  intro E _ _ _ H K L _ _ _ _ φ ψ h2 ⟨a, ha⟩ n hn hC
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  let eK : K ≃ₐ[ℚ] (ψ.comp φ).toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField (ψ.comp φ).toRatAlgHom
  let eL : L ≃ₐ[ℚ] ψ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField ψ.toRatAlgHom
  have heK : ∀ x, ((eK x : (ψ.comp φ).toRatAlgHom.fieldRange) : ℂ) = ψ (φ x) := fun _ => rfl
  have heL : ∀ x, ((eL x : ψ.toRatAlgHom.fieldRange) : ℂ) = ψ x := fun _ => rfl
  have hr0 : H.rt0 ∈ (ψ.comp φ).toRatAlgHom.fieldRange := by
    have h1 : (ψ (φ a)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, ← map_pow, ha]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact ⟨a, h⟩
    · exact ⟨-a, by
        change ψ (φ (-a)) = _
        rw [map_neg, map_neg, h, neg_neg]⟩
  have hle : (ψ.comp φ).toRatAlgHom.fieldRange ≤ ψ.toRatAlgHom.fieldRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  clear_value eK eL
  generalize (ψ.comp φ).toRatAlgHom.fieldRange = K₀ at eK heK hr0 hle
  generalize ψ.toRatAlgHom.fieldRange = F at eL heL hle ⊢
  have hfK : FiniteDimensional ℚ K₀ := eK.toLinearEquiv.finiteDimensional
  have hfF : FiniteDimensional ℚ F := eL.toLinearEquiv.finiteDimensional
  have hNK : NumberField K₀ := NumberField.mk
  have hNF : NumberField F := NumberField.mk
  replace h2 : Module.finrank ℚ K₀ = 2 := by rw [← eK.toLinearEquiv.finrank_eq, h2]
  have hC' : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hle).toRingHom n :=
    containsRayField_congr φ _ eK.toRingEquiv eL.toRingEquiv
      (fun x => Subtype.ext ((heK x).trans (heL (φ x)).symm)) n hC
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let j : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : j w = (1 + H.rt0) / 2 := by
    have := congrArg j hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, j ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  refine ⟨fun P hP => ?_, hle hr0⟩
  have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField K₀ F hle h2 (by omega) P (fun z => ?_) n hn hC'
  · exact ⟨hW (Set.mem_insert _ _), fun s hs => hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end GlobalTheory.FieldSize.WeberTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayFieldStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberValues_mem_of_containsRayField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (ψ : L →+* ℂ), Module.finrank ℚ K = 2 → (∃ a : K, a ^ 2 = -(H.d : K)) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n → GlobalTheory.FinalJoin.WeberIn H ψ.toRatAlgHom.fieldRange n ∧ H.rt0 ∈ ψ.toRatAlgHom.fieldRange := by
  first | exact @GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField | exact GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField | (intros; apply GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.TwistLevels

open Formalism.L2.Host

theorem not_unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ¬ ψ.UnrAt v) : ¬ (d * ψ).UnrAt v := by
  intro h
  apply hψ
  intro x hx
  have := h x hx
  change d.loc v x * ψ.loc v x = 1 at this
  rw [hd x hx, one_mul] at this
  exact this

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ψ.UnrAt v) : (d * ψ).UnrAt v := by
  intro x hx
  change d.loc v x * ψ.loc v x = 1
  rw [hd x hx, hψ x hx, one_mul]

theorem card_residueField_ne_zero {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) : Nat.card (kP Q) ≠ 0 := by
  have h : Nat.card (kP Q) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h, Ne, Ideal.absNorm_eq_zero_iff]
  exact Q.ne_bot

def ramSet (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  {Q | ((P.host.pde * P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}

theorem not_unrAt_xiTw (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E))
    (hQ : Q ∈ T.Q w) (hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) : ¬ (T.xiTw f w).UnrAt Q := by
  have h1 : ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  have hψ : ¬ (T.psi w).UnrAt Q := fun h => ((T.psi_is w).ram Q).1 h hQ
  unfold TwDat.xiTw
  split_ifs
  · exact not_unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact not_unrAt_mul (f.isDel.unr Q h1) hψ

theorem ram_finite (B : Base) (f : Fr B.toPre) (T : TwDat B) (χ : HChar B.host.E) (hχ : χ ∈ T.set f) :
    {Q : HeightOneSpectrum (𝓞 B.host.E) | ¬ χ.UnrAt Q}.Finite := by
  have hpde : B.host.pde * B.host.pde' ≠ 0 :=
    mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
  have hZ := GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde
  have h1 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  rcases hχ with hχ | ⟨w, rfl⟩
  · rcases hχ with rfl | rfl | rfl
    · exact Set.finite_empty.subset fun Q hQ => hQ fun _ _ => rfl
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel.unr Q (h1 Q hn))
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel'.unr Q (h2 Q hn))
  · refine (hZ.union (T.Q w).finite_toSet).subset fun Q hQ => ?_
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hc
    have hψ : (T.psi w).UnrAt Q := ((T.psi_is w).ram Q).2 hc.2
    apply hQ
    unfold TwDat.xiTw
    split_ifs
    · exact unrAt_mul (f.isDel'.unr Q (h2 Q hc.1)) hψ
    · exact unrAt_mul (f.isDel.unr Q (h1 Q hc.1)) hψ

open Classical in
theorem levels_bounded : ∀ (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)), ∃ Ms : Finset ℕ, (∀ M ∈ Ms, M ≠ 0) ∧
    ∀ (B : Base) (hB : B.toPre = P) (T : TwDat B), HEq (T.set (hB ▸ f)) Ξ → ∀ (w : B.places.Pl)
      (S : Finset (HeightOneSpectrum (𝓞 B.host.E))),
      (∀ Q ∈ S, ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal ∨ Q ∈ T.Q w) →
      B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ∈ Ms := by
  intro P f Ξ
  by_cases hA : (ramSet P Ξ).Finite
  · refine ⟨hA.toFinset.powerset.image
      (fun S => P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q), ?_, ?_⟩
    · intro M hM
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.1 hM
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact card_residueField_ne_zero Q
    · intro B hB T hT w S hS
      subst hB
      have hT' : T.set f = Ξ := eq_of_heq hT
      refine Finset.mem_image.2 ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 ?_, rfl⟩
      rcases hS Q hQ with h | h
      · exact Or.inl h
      · by_cases hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal
        · exact Or.inl hn
        · refine Or.inr ⟨T.xiTw f w, ?_, not_unrAt_xiTw B f T w Q h hn⟩
          rw [← hT']
          exact Set.mem_union_right _ ⟨w, rfl⟩
  · refine ⟨∅, by simp, ?_⟩
    intro B hB T hT w S hS
    subst hB
    exfalso
    apply hA
    have hT' : T.set f = Ξ := eq_of_heq hT
    have hpde : B.host.pde * B.host.pde' ≠ 0 :=
      mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    refine ((GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde).union
      (hfin.biUnion fun χ hχ => ram_finite B f T χ hχ)).subset ?_
    rintro Q (h | ⟨χ, hχ, hr⟩)
    · exact Or.inl h
    · refine Or.inr (Set.mem_biUnion (x := χ) ?_ hr)
      rw [hT']
      exact hχ

end GlobalTheory.Plug.TwistLevels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSecCharVal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiFun

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CharRead

set_option maxHeartbeats 1000000 in
theorem exists_sec_char_val (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → FnAlgClosed (Xo := Xo) (c := c) → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → (∀ h : GA D V, ∃ a : c.F, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (h))) : ℂˣ)) → ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V (h))) ^ m = 1) → f ^ m = 1) ∧ (∀ y : FrPt Xo c (CAt σ), ∃ a : c.F, evR Xo c f y = algebraMap c.F (CAt σ) a) ∧ ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
  intro hio hpos hA hgood hW hD hdom hcl xi h1 h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h γ h' γ', MarkBy U V rfl dict io F ik φ h γ → MarkBy U V rfl dict io F ik φ h' γ' →
      ik (dict h).1 = ik (dict h').1 → xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) =
        xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) := by
    intro h γ h' γ' hm hm' hi
    refine xi_eq_of_index F V io hio.emb _ _ hi _ _ _ _ (SetLike.ext' (hm.2.1.trans (Set.image_id _)))
      (SetLike.ext' (hm'.2.1.trans (Set.image_id _))) (φ _) (φ _) _ ?_ (htr _) (htr _) hm.2.2 hm'.2.2 xi h1 h2
    rw [← (hW (dict h).1).2]
    exact neg_ne_zero.2 (U.X _).ξ0_ne
  have hv : ∀ i : Fin F.n, ∃ a : c.F, (∃ u : GA D V, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ)) ∧
      ∀ h γ, MarkBy U V rfl dict io F ik φ h γ → ik (dict h).1 = i →
        σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
    intro i
    by_cases hex : ∃ h γ, MarkBy U V rfl dict io F ik φ h γ ∧ ik (dict h).1 = i
    · obtain ⟨h, γ, hm, hi⟩ := hex
      obtain ⟨a, ha⟩ := h3 (γ * h)
      exact ⟨a, ⟨_, ha⟩, fun h' γ' hm' hi' => by rw [ha, key h γ h' γ' hm hm' (hi.trans hi'.symm)]⟩
    · obtain ⟨a, ha⟩ := h3 1
      exact ⟨a, ⟨_, ha⟩, fun h γ hm hi => absurd ⟨h, γ, hm, hi⟩ hex⟩
  choose v hv1 hv2 using hv
  obtain ⟨f, hf, hf1, hf2⟩ := GlobalTheory.T.exists_weightZero_section_of_periodSpace_function D.host.E H Dw l Xo c σ g _ F hpos hgood
    ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hgood).2.2.2 Dw g e) hA hcl v
  refine ⟨f, hf, fun m hm => hf1 m fun i => σ.injective ?_, fun y => ?_, fun h γ hm => ?_⟩
  · obtain ⟨u, hu⟩ := hv1 i
    rw [map_pow, map_one, hu, ← Units.val_pow_eq_pow_val, hm u, Units.val_one]
  · obtain ⟨i, P, hP, hx⟩ := F.onto y.x y.x_over
    exact ⟨v i, hf2 y i P hP hx.symm⟩
  · obtain ⟨Pm, -, hP, hx, -⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hdom h⟩
    rw [← hv2 _ h γ hm rfl, ← hf2 _ _ Pm hP hx]
    exact dif_pos (hdom h)

theorem evR_ne_zero_of_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f f' : Rul Xo c) (m : ℕ) (hm : 0 < m)
    (hf : f ^ m = 1) (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k) (h : evR Xo c f' y ≠ 0) :
    evR Xo c f y ≠ 0 := by
  unfold evR evalAt at h ⊢
  split_ifs at h ⊢ with hy
  · intro h0
    have h1 := congrArg (· ^ m) h0
    simp only [zero_pow hm.ne'] at h1
    rw [← map_pow, ← Pi.pow_apply, ← Pi.pow_apply, hf] at h1
    simp at h1
  · exact h

variable {D : D7}

theorem normOne_det (V : HSp D) (h : GA D V) : NormOne (D := D) (Matrix.GeneralLinearGroup.det (finHom V h)) := by
  have h1 := GlobalTheory.RecDict.det_finHom_norm V h
  have h2 : ∀ z : AfE D, barF D z = sigR (Af D.host.F) D.sp.cm.sig z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  unfold NormOne
  rw [h2, Matrix.GeneralLinearGroup.val_det_apply]
  exact h1

theorem det_rat (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ a : D.host.E, ((Matrix.GeneralLinearGroup.det (finHom V γ) : (AfE D)ˣ) : AfE D) = 1 ⊗ₜ a := by
  obtain ⟨γ', h⟩ := exists_isRat_of_mem_GQ V hγ
  refine ⟨γ'.1.det, ?_⟩
  unfold IsRat at h
  have : (finHom V γ).1 = ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (incA D)).mapMatrix γ'.1 := by
    unfold finHom
    rw [MonoidHom.comp_apply, h]
    rfl
  change (finHom V γ).1.det = _
  rw [this, ← RingHom.map_det]
  rfl

theorem FO_le_of_pins (Q : Par D) (h : Q.Pins) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have := h.2.2.1 (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at this
  have e : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := this
  rw [e]
  exact (Q.eO.symm y : Q.c.F).2

theorem iotaOK_of_latIsom (Q : Par D) (h : Q.Pins) (j : ℕ) (hj : InR D j) (V : HSp D) (hV : V = D.sp.W j)
    (ι : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (h1 : LatEmb V ι) (h2 : LatIsom V (Q.Dw j).EF ι) :
    IotaOK (Q.Dw j) V ι := by
  subst hV
  obtain ⟨ε, hε⟩ := h2
  let s : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (D.sp.W j).V := (D.sp.W j).frame.equivFun.symm
  have hs : ε = 1 := by
    refine sign_eq_one D Q.H (Q.Dw j) j hj h.1.2.1 h.1.2.2.1 (h.2.2.2 j hj).1 (h.2.2.2 j hj).2.1
      ((s.toLinearMap.restrictScalars (𝓞 D.host.E)) ∘ₗ ι) ε (s.injective.comp h1.1) ?_ hε
    have e1 : Set.range ((s.toLinearMap.restrictScalars (𝓞 D.host.E)) ∘ₗ ι) =
        s.toLinearMap '' (latG (D.sp.W j) 1 : Set _) := by
      rw [← h1.2, LinearMap.coe_range, ← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, (GlobalTheory.T.adelicElementLattice_full_and_completion D _ 1).2.1, Submodule.map_top, LinearEquiv.range]
  subst hs
  exact ⟨h.1.2.1, h.1.2.2.1, h1, fun x y => by simpa using hε x y⟩

set_option maxHeartbeats 1000000 in
theorem exists_fun_xiAt : ∀ (D : D7) (J : CoreJ D), LawsJ J → ∀ j, InR D j → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)) (d : DeltaDat (J.Q.Xo j) J.Q.c 0) (xi : (AfE D)ˣ →* ℂˣ), CoverOK d p I → FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) → XiOK D p xi → ∃ f : Rul d.Xo₂ d.c₂, CoverOK ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) p I ∧ RootOK ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) ∧ XiAt J j ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) xi := by
  intro D J hJ j hj p I d xi hd hcl hxi
  obtain ⟨hp, hI, hlev, hA, hnab⟩ := hd
  have hg := J.toCore.good_σ₀
  have hpin := hJ.pins
  obtain ⟨hr, -, -, -, -, -, -, hemb, hisom, -⟩ := hJ.adPin j hj _ hg
  have hio := iotaOK_of_latIsom J.Q hpin j hj _ (hJ.spaceW j hj _ hg) _ hemb hisom
  have hpq := (exists_iotaOK D J.Q hpin j hj).2
  have hpos : 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q := by omega
  have hσ : d.c₂.F.val.toRingHom = J.σ₀.comp (d.eF.symm : d.c₂.F →+* J.Q.c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ (J.σ₀.comp (d.eF.symm : d.c₂.F →+* J.Q.c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨hr', hW⟩ := hJ.modelW j hj _ hg
  have hU := hJ.unf j hj _ hg
  let k₀ := (J.dict j J.σ₀ 1).1
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D J.Q.H (J.Q.Dw j) d.l₂ d.Xo₂ d.c₂ _ _ D.R.r hr _ hio hpos hA hg₂).2.2
    (J.x₀ j J.σ₀) (fun τ hτ => by
      have h1 := hJ.familyUniformisationBasePointOrthogonal j hj _ hg k₀ τ (((hU.2.1 k₀).2 τ).2 hτ)
      rwa [(hW k₀).1, (hU.2.1 k₀).1] at h1)
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D (J.V j J.σ₀) d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  have hM : d.l₂.M = D.host.g 0 * D.host.g 1 * p := by rw [hlev.2.1, hpin.2.1.1, hp]
  obtain ⟨m, hm, hxm⟩ := hxi.fin
  obtain ⟨f, hf, hfm, hfv, hfx⟩ := exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => hxi.tame _ (normOne_det _ u) (by
      rw [← hM]; unfold CongOne; rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu))
    (fun γ hγ => by
      obtain ⟨a, ha⟩ := det_rat _ γ hγ
      exact hxi.rat _ a ha (normOne_det _ γ))
    (fun h => ⟨⟨_, d.hF.symm ▸ FO_le_of_pins J.Q hpin (hxi.val _ (normOne_det _ h))⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m fun h => hxm _ (normOne_det _ h)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨hp, hI, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hA, hnab⟩, ⟨⟨m, hm, hfm'⟩, ?_⟩, ?_⟩
  · exact evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · change ∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F,
      evR d.Xo₂ d.c₂ f y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a
    rw [hσ]
    exact hfv
  · refine ⟨hr, fun _ => C.unf un, fun _ => dict, 1, ⟨1, one_pos, one_pow 1⟩, fun _ => ⟨hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩⟩
    · rw [← hCι, ← hCx]
      exact hdl
    · rw [one_mul]
      rw [← hCι] at hmk
      exact hfx h γ hmk

end GlobalTheory.XiFun
end

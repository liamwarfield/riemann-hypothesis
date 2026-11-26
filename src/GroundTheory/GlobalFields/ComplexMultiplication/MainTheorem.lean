module

public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremAssembly

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremLevel
section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFields
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Torsion

variable {F : Type*} [Field F] [Algebra F ℂ] (A : WeierstrassCurve F)

theorem baseChange_map_algEquiv (ρ : ℂ ≃ₐ[F] ℂ) :
    (A.baseChange ℂ).map (ρ : ℂ →+* ℂ) = A.baseChange ℂ := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext a
  exact ρ.commutes a

theorem nsmul_some_congr {V₁ V₂ : WeierstrassCurve ℂ} (e : V₁ = V₂) {x y : ℂ}
    (h₁ : V₁.toAffine.Nonsingular x y) (h₂ : V₂.toAffine.Nonsingular x y) {m : ℕ}
    (h : m • (Point.some x y h₁ : V₁.toAffine.Point) = 0) :
    m • (Point.some x y h₂ : V₂.toAffine.Point) = 0 := by
  subst e
  exact h

theorem exists_nsmul_some_algEquiv (ρ : ℂ ≃ₐ[F] ℂ) {m : ℕ} {x y : ℂ}
    (h : (A.baseChange ℂ).toAffine.Nonsingular x y)
    (hP : m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0) :
    ∃ h' : (A.baseChange ℂ).toAffine.Nonsingular (ρ x) (ρ y),
      m • (Point.some (ρ x) (ρ y) h' : (A.baseChange ℂ).toAffine.Point) = 0 := by
  classical
  obtain ⟨h₁, e⟩ := pointMapRing_some (ρ : ℂ →+* ℂ) (A.baseChange ℂ) h
  have hA := baseChange_map_algEquiv A ρ
  have h₂ : (A.baseChange ℂ).toAffine.Nonsingular (ρ x) (ρ y) := by
    rw [← hA]
    exact h₁
  refine ⟨h₂, nsmul_some_congr hA h₁ h₂ ?_⟩
  have := congrArg (pointMapRing (ρ : ℂ →+* ℂ) (A.baseChange ℂ)) hP
  rwa [map_nsmul, e, map_zero] at this

theorem exists_nsmul_some_of_eq {V : WeierstrassCurve ℂ} {x y x' y' : ℂ} (hx : x = x') (hy : y = y')
    (h : V.toAffine.Nonsingular x y) {m : ℕ} (hm : m • (Point.some x y h : V.toAffine.Point) = 0) :
    ∃ h' : V.toAffine.Nonsingular x' y', m • (Point.some x' y' h' : V.toAffine.Point) = 0 := by
  subst hx
  subst hy
  exact ⟨h, hm⟩

omit [Algebra F ℂ] in
theorem isIntegral_of_isIntegral_add_natCast {B : Type*} [CommRing B] [Algebra F B] {x : B} (n : ℕ)
    (hx : IsIntegral F (x + n)) : IsIntegral F x := by
  have h := hx.sub (isIntegral_algebraMap (R := F) (x := (n : F)))
  rwa [map_natCast, add_sub_cancel_right] at h

variable [A.IsElliptic]

theorem isAlgebraic_of_nsmul_eq_zero {m : ℕ} (hm : m ≠ 0) {x y : ℂ}
    (h : (A.baseChange ℂ).toAffine.Nonsingular x y)
    (hP : m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0) :
    IsAlgebraic F x ∧ IsAlgebraic F y := by
  classical
  have hfin := finite_torsionBy_natCast (A.baseChange ℂ) hm
  have hmem : ∀ {u v : ℂ} (k : (A.baseChange ℂ).toAffine.Nonsingular u v),
      m • (Point.some u v k : (A.baseChange ℂ).toAffine.Point) = 0 →
        (Point.some u v k : (A.baseChange ℂ).toAffine.Point) ∈
          AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ) := fun k hk ↦
    (mem_torsionBy_natCast_iff _ m _).2 hk
  constructor
  · by_contra hx
    have ht : ∀ n : ℕ, Transcendental F (x + n) := fun n hn ↦
      hx (isIntegral_of_isIntegral_add_natCast n hn.isIntegral).isAlgebraic
    have hρ : ∀ n : ℕ, ∃ ρ : ℂ ≃ₐ[F] ℂ, ρ x = x + n := fun n ↦
      exists_algEquiv_apply_eq_of_transcendental (fun h' ↦ hx h') (ht n)
    choose ρ hρ using hρ
    have hpt : ∀ n : ℕ, ∃ k : (A.baseChange ℂ).toAffine.Nonsingular (x + n) (ρ n y),
        m • (Point.some (x + n) (ρ n y) k : (A.baseChange ℂ).toAffine.Point) = 0 := fun n ↦ by
      obtain ⟨k, hk⟩ := exists_nsmul_some_algEquiv A (ρ n) h hP
      exact exists_nsmul_some_of_eq (hρ n) rfl k hk
    choose k hk using hpt
    have hinj : Function.Injective fun n : ℕ ↦
        (⟨Point.some (x + n) (ρ n y) (k n), hmem (k n) (hk n)⟩ :
          AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [Point.some.injEq, add_right_inj, Nat.cast_inj] at this
      exact this.1
    have := Finite.of_injective _ hinj
    exact not_finite ℕ
  · by_contra hy
    have ht : ∀ n : ℕ, Transcendental F (y + n) := fun n hn ↦
      hy (isIntegral_of_isIntegral_add_natCast n hn.isIntegral).isAlgebraic
    have hρ : ∀ n : ℕ, ∃ ρ : ℂ ≃ₐ[F] ℂ, ρ y = y + n := fun n ↦
      exists_algEquiv_apply_eq_of_transcendental (fun h' ↦ hy h') (ht n)
    choose ρ hρ using hρ
    have hpt : ∀ n : ℕ, ∃ k : (A.baseChange ℂ).toAffine.Nonsingular (ρ n x) (y + n),
        m • (Point.some (ρ n x) (y + n) k : (A.baseChange ℂ).toAffine.Point) = 0 := fun n ↦ by
      obtain ⟨k, hk⟩ := exists_nsmul_some_algEquiv A (ρ n) h hP
      exact exists_nsmul_some_of_eq rfl (hρ n) k hk
    choose k hk using hpt
    have hinj : Function.Injective fun n : ℕ ↦
        (⟨Point.some (ρ n x) (y + n) (k n), hmem (k n) (hk n)⟩ :
          AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [Point.some.injEq, add_right_inj, Nat.cast_inj] at this
      exact this.2
    have := Finite.of_injective _ hinj
    exact not_finite ℕ

end Torsion

section TorsionField

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem exists_le_forall_torsion_mem (L₀ : IntermediateField K ℂ) [FiniteDimensional K L₀]
    (A : WeierstrassCurve L₀) [A.IsElliptic] {m : ℕ} (hm : m ≠ 0) :
    ∃ M : IntermediateField K ℂ, FiniteDimensional K M ∧ L₀ ≤ M ∧
      ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y),
        m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0 → x ∈ M ∧ y ∈ M := by
  classical
  set T := AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ)
  have : Finite T := finite_torsionBy_natCast (A.baseChange ℂ) hm
  let c : (A.baseChange ℂ).toAffine.Point → Set ℂ := fun P ↦
    match P with
    | .zero => ∅
    | .some x y _ => {x, y}
  have hc : ∀ P, (c P).Finite := fun P ↦ by
    rcases P with _ | ⟨x, y, h⟩
    · exact Set.finite_empty
    · exact (Set.finite_singleton y).insert x
  set S : Set ℂ := ⋃ P : T, c P.1
  have hSfin : S.Finite := Set.finite_iUnion fun P ↦ hc P.1
  have hcoord : ∀ z ∈ S, IsIntegral K z := by
    intro z hz
    obtain ⟨⟨P, hP⟩, hzP⟩ := Set.mem_iUnion.1 hz
    have hP' : m • P = 0 := (mem_torsionBy_natCast_iff _ m P).1 hP
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd hzP (Set.notMem_empty z)
    · obtain ⟨hx, hy⟩ := isAlgebraic_of_nsmul_eq_zero A hm h hP'
      have hz' : z = x ∨ z = y := hzP
      rcases hz' with rfl | rfl
      · exact isIntegral_trans (R := K) (A := L₀) _ hx.isIntegral
      · exact isIntegral_trans (R := K) (A := L₀) _ hy.isIntegral
  have : Finite S := hSfin.to_subtype
  have : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin hcoord
  refine ⟨L₀ ⊔ IntermediateField.adjoin K S, inferInstance, le_sup_left, fun x y h hP ↦ ?_⟩
  have hPT : (Point.some x y h : (A.baseChange ℂ).toAffine.Point) ∈ T :=
    (mem_torsionBy_natCast_iff _ m _).2 hP
  have hx : x ∈ S := Set.mem_iUnion.2 ⟨⟨_, hPT⟩, Set.mem_insert x _⟩
  have hy : y ∈ S := Set.mem_iUnion.2 ⟨⟨_, hPT⟩, Set.mem_insert_of_mem x rfl⟩
  exact ⟨le_sup_right (a := L₀) (IntermediateField.subset_adjoin K S hx),
    le_sup_right (a := L₀) (IntermediateField.subset_adjoin K S hy)⟩

end TorsionField

section Frobenius

open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem exists_isArithFrobAt (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (τ : L ≃ₐ[K] L) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ v ∈ degreeOnePrimes ℚ K ∧
      ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧
        w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ IsArithFrobAt (𝓞 K) τ w.asIdeal := by
  classical
  have : NumberField L := NumberField.of_module_finite K L
  set C : Set (L ≃ₐ[K] L) := {ρ | IsConj τ ρ}
  have hC : ∀ σ ∈ C, ∀ ρ : L ≃ₐ[K] L, ρ * σ * ρ⁻¹ ∈ C := fun σ hσ ρ ↦
    IsConj.trans hσ (isConj_iff.2 ⟨ρ, rfl⟩)
  have hdens := hasDirichletDensity_setOf_arithFrobAt_mem C hC
  rw [← hasDirichletDensity_inter_degreeOnePrimes_iff (K := ℚ) _ _] at hdens
  have : Nonempty C := ⟨⟨τ, IsConj.refl τ⟩⟩
  have hpos : (0 : ℝ) < Nat.card C / Nat.card (L ≃ₐ[K] L) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨hvA, hv1⟩, hvS⟩ :
      (({v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
          arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal ∈ C} ∩ degreeOnePrimes ℚ K) \ S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    have h0 := hasDirichletDensity_zero_of_finite (hS.subset hne)
    have := hdens.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq
    linarith
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  obtain ⟨c, hc⟩ := isConj_iff.1 (hvA w hw).2
  have hfrob : IsArithFrobAt (𝓞 K) (c * τ * c⁻¹) w.asIdeal := by
    rw [hc]
    exact IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal
  set w' : HeightOneSpectrum (𝓞 L) := ⟨c⁻¹ • w.asIdeal, Ideal.IsPrime.smul c⁻¹, fun h ↦ w.ne_bot (by
    rw [← smul_inv_smul c w.asIdeal, h, Ideal.smul_bot])⟩
  have hw' : w'.asIdeal.LiesOver v.asIdeal :=
    ⟨(hw.over).trans (Ideal.under_smul (𝓞 K) w.asIdeal c⁻¹).symm⟩
  refine ⟨v, hvS, hv1, w', hw', (hvA w' hw').1, ?_⟩
  have := hfrob.conj c⁻¹
  have e : c⁻¹ * (c * τ * c⁻¹) * c⁻¹⁻¹ = τ := by group
  rw [e] at this
  exact this

end Frobenius

end

end Elliptic
end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremModels
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IntermediateField WeierstrassCurve GroundTheory.Arith.Abelian

section ShortModel

variable {F F' : Type*} [Field F] [Field F']

theorem ofJ_map [DecidableEq F] [DecidableEq F'] (f : F →+* F') (j : F) :
    (ofJ j).map f = ofJ (f j) := by
  have h3 : (3 : F) = 0 ↔ (3 : F') = 0 := by
    rw [← map_ofNat f 3, map_eq_zero_iff f f.injective]
  have hj0 : j = 0 ↔ f j = 0 := (map_eq_zero_iff f f.injective).symm
  have hj1728 : j = 1728 ↔ f j = 1728 := by
    rw [← map_ofNat f 1728]
    exact f.injective.eq_iff.symm
  unfold ofJ
  by_cases a : j = 0
  · rw [if_pos a, if_pos (hj0.1 a)]
    by_cases b : (3 : F) = 0
    · rw [if_pos b, if_pos (h3.1 b)]
      ext <;> simp [ofJ1728]
    · rw [if_neg b, if_neg (mt h3.2 b)]
      ext <;> simp [ofJ0]
  · rw [if_neg a, if_neg (mt hj0.2 a)]
    by_cases b : j = 1728
    · rw [if_pos b, if_pos (hj1728.1 b)]
      ext <;> simp [ofJ1728]
    · rw [if_neg b, if_neg (mt hj1728.2 b)]
      ext <;> simp [ofJNe0Or1728, map_ofNat]

theorem toShortNF_map (W : WeierstrassCurve F) [Invertible (2 : F)] [Invertible (3 : F)]
    [Invertible (2 : F')] [Invertible (3 : F')] (f : F →+* F') :
    W.toShortNF.map f = (W.map f).toShortNF := by
  ext <;> simp [toShortNF, toCharNeTwoNF, VariableChange.map, variableChange_a₂,
    VariableChange.mul_def, map_ofNat]

variable [CharZero F]

def shortModel (j : F) : WeierstrassCurve F :=
  letI : DecidableEq F := Classical.decEq F
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (3 : F) := invertibleOfNonzero three_ne_zero
  (ofJ j).toShortNF • ofJ j

instance (j : F) : (shortModel j).IsElliptic := by
  unfold shortModel
  infer_instance

instance (j : F) : (shortModel j).IsShortNF := by
  unfold shortModel
  infer_instance

theorem shortModel_j (j : F) : (shortModel j).j = j := by
  unfold shortModel
  rw [variableChange_j, ofJ_j]

variable [CharZero F']

theorem shortModel_map (f : F →+* F') (j : F) : (shortModel j).map f = shortModel (f j) := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : F) := invertibleOfNonzero three_ne_zero
  let _ : Invertible (2 : F') := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : F') := invertibleOfNonzero three_ne_zero
  have e1 : shortModel j = (ofJ j).toShortNF • ofJ j := by
    unfold shortModel
    congr
  have e2 : shortModel (f j) = (ofJ (f j)).toShortNF • ofJ (f j) := by
    unfold shortModel
    congr
  rw [e1, e2, ← map_variableChange, toShortNF_map, ofJ_map]

end ShortModel

section Models

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]


include hK in
theorem exists_shortModels_isogenous (M : IntermediateField K ℂ) [FiniteDimensional K M] :
    ∃ L : IntermediateField K ℂ, M ≤ L ∧ FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ hL : ∀ x : ELL K, ELL.j x ∈ L,
        (∀ x, ∃ h : Nonempty (isogEnd ((shortModel (⟨ELL.j x, hL x⟩ : L)).baseChange ℂ) ≃+* 𝓞 K),
          (⟨(shortModel (⟨ELL.j x, hL x⟩ : L)).baseChange ℂ, h⟩ : CMCurve K).toEll = x) ∧
        ∀ x y, Nonempty (Isogeny (shortModel (⟨ELL.j x, hL x⟩ : L))
          (shortModel (⟨ELL.j y, hL y⟩ : L))) := by
  classical
  have := finite_ell hK
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯
  have hJ : ∀ y, ELL.j y ∈ J := fun y ↦ ELL.j_mem_adjoin hK x₀ y
  have : FiniteDimensional K J :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  have : NumberField J := NumberField.of_module_finite K J
  set E₀ : ELL K → WeierstrassCurve J := fun y ↦ shortModel (⟨ELL.j y, hJ y⟩ : J)
  have hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y := fun y ↦ by
    simp only [E₀, shortModel_j]
    rfl
  have hE₀ : ∀ y, ∃ h : Nonempty (isogEnd ((E₀ y).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E₀ y).baseChange ℂ, h⟩ : CMCurve K).toEll = y := fun y ↦
    exists_cmCurve_toEll_of_j_eq y _ (by
      show ((E₀ y).map (algebraMap J ℂ)).j = _
      rw [map_j, hE₀j])
  have hF : ∀ p : ELL K × ELL K, ∃ F₁ : IntermediateField J ℂ, NumberField F₁ ∧
      Nonempty (Isogeny ((E₀ p.1).baseChange F₁) ((E₀ p.2).baseChange F₁)) := by
    rintro ⟨y, z⟩
    obtain ⟨hy, -⟩ := hE₀ y
    obtain ⟨hz, -⟩ := hE₀ z
    obtain ⟨ψ⟩ := nonempty_isogeny_of_cmCurve hK ⟨_, hy⟩ ⟨_, hz⟩
    obtain ⟨F₁, hF₁, φ, -⟩ := Isogeny.exists_numberField_mapOf_eq ψ
    exact ⟨F₁, hF₁, ⟨φ⟩⟩
  choose F hFnum hFiso using hF
  have hFfin : ∀ p, FiniteDimensional K ((F p).restrictScalars K) := fun p ↦ by
    have := hFnum p
    have : FiniteDimensional ℚ ((F p).restrictScalars K) := (inferInstance : FiniteDimensional ℚ (F p))
    exact Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)
  set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K
  have : FiniteDimensional K M' := by
    have := hFfin
    infer_instance
  obtain ⟨L, hM'L, hLfin, hLgal⟩ := exists_isGalois_le M'
  have hJL : J ≤ L := le_trans (le_trans le_sup_right le_sup_left) hM'L
  have hFL : ∀ p, (F p).restrictScalars K ≤ L := fun p ↦
    le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L
  set ι : J →+* L := (inclusion hJL).toRingHom
  have hmodel : ∀ y, (E₀ y).map ι = shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L) := fun y ↦ by
    rw [shortModel_map]
    rfl
  refine ⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, fun y ↦ hJL (hJ y),
    fun y ↦ ?_, fun y z ↦ ?_⟩
  · refine exists_cmCurve_toEll_of_j_eq y _ ?_
    show ((shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L)).map (algebraMap L ℂ)).j = _
    rw [map_j, shortModel_j]
    rfl
  · obtain ⟨φ⟩ := hFiso (y, z)
    let κ : F (y, z) →+* L := (inclusion (hFL (y, z))).toRingHom
    have hκ : κ.comp (algebraMap J (F (y, z))) = ι := by
      ext a
      rfl
    have e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = shortModel (⟨ELL.j w, hJL (hJ w)⟩ : L) :=
      fun w ↦ by
        show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _
        rw [WeierstrassCurve.map_map, hκ, hmodel]
    exact ⟨(φ.map κ).congr (e y) (e z)⟩

end Models

end

end Elliptic
end GroundTheory.Global
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
  IntermediateField
open GroundTheory.LocalField (maximalAbelianExtension)
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] in
theorem exists_isogeny_homConstSet_congr {L : Type} [Field L] [Algebra L ℂ]
    {A A' B B' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic] [B.IsElliptic] [B'.IsElliptic]
    (eA : A = A') (eB : B = B') {S : Set ℂ}
    (h : ∃ φ : Isogeny A B, (homConstSet (A.baseChange ℂ) (B.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) '' S) :
    ∃ φ : Isogeny A' B', (homConstSet (A'.baseChange ℂ) (B'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) '' S := by
  subst eA eB
  exact h

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra K ℂ] in
theorem nonempty_isogEnd_congr {L : Type} [Field L] [Algebra L ℂ] {B B' : WeierstrassCurve L}
    [B.IsElliptic] [B'.IsElliptic] (e : B = B') (h : Nonempty (isogEnd (B.baseChange ℂ) ≃+* 𝓞 K)) :
    Nonempty (isogEnd (B'.baseChange ℂ) ≃+* 𝓞 K) := by
  subst e
  exact h


include hK in
theorem exists_uniformization_level (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical

  have hL₁ := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hL₁end := latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hf₁ := hf
  rw [← hL₁] at hf₁
  obtain ⟨C₁, hC₁, -⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  have hEend : Nonempty (isogEnd E ≃+* 𝓞 K) :=
    ⟨(vcEndEquiv C₁ hC₁).symm.trans (CMCurve.ofLattice (algebraMap K ℂ) _ hL₁end).endIso.some⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ELL K, x₀ = (⟨E, hEend⟩ : CMCurve K).toEll := ⟨_, rfl⟩
  have hx₀ell : x₀ = ellOf (algebraMap K ℂ) _ hL₁end := by
    rw [hx₀]
    exact (CMCurve.toEll_eq_iff _ _).2 ⟨C₁⁻¹, inv_smul_eq_of_smul_eq C₁ hC₁⟩
  have hjE : ELL.j x₀ = E.j := by
    rw [hx₀]
    exact ELL.j_toEll _

  have hJfin : FiniteDimensional K K⟮ELL.j x₀⟯ :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  set aJ : K⟮ELL.j x₀⟯ := ⟨ELL.j x₀, mem_adjoin_simple_self K _⟩
  obtain ⟨M₁, hM₁fin, -, htorsJ⟩ := exists_le_forall_torsion_mem K⟮ELL.j x₀⟯ (shortModel aJ) hm

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ))
  have hζ : IsPrimitiveRoot ζ 12 := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  have hM₃fin : FiniteDimensional K K⟮ζ⟯ :=
    adjoin.finiteDimensional ((hζ.isIntegral (by norm_num)).tower_top)

  obtain ⟨L, hML, hLfin, hLgal, hL, hE, hiso⟩ := exists_shortModels_isogenous hK
    (M₁ ⊔ (Modulus.ofNat (K := K) m hm).rayClassField ℂ ⊔ K⟮ζ⟯)
  have : NumberField L := NumberField.of_module_finite K L
  have hM₁L : M₁ ≤ L := le_trans (le_trans le_sup_left le_sup_left) hML
  have hM₂L : (Modulus.ofNat (K := K) m hm).rayClassField ℂ ≤ L :=
    le_trans (le_trans le_sup_right le_sup_left) hML
  have hζL : ζ ∈ L := hML (le_sup_right (a := M₁ ⊔ _) (mem_adjoin_simple_self K ζ))
  have hζL' : IsPrimitiveRoot (⟨ζ, hζL⟩ : L) 12 :=
    (IsPrimitiveRoot.map_iff_of_injective (algebraMap L ℂ).injective).1 hζ

  obtain ⟨A, hAdef⟩ : ∃ A : WeierstrassCurve L, A = shortModel (⟨ELL.j x₀, hL x₀⟩ : L) := ⟨_, rfl⟩
  have : A.IsElliptic := by rw [hAdef]; infer_instance
  have : A.IsShortNF := by rw [hAdef]; infer_instance
  have hAℂ : A.baseChange ℂ = (shortModel aJ).baseChange ℂ := by
    rw [hAdef, WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, shortModel_map, shortModel_map]
    rfl
  obtain ⟨V₀, hV₀⟩ := exists_variableChange_of_j_eq E (A.baseChange ℂ) (by
    rw [j_congr hAℂ]
    show E.j = ((shortModel aJ).map (algebraMap _ ℂ)).j
    rw [map_j, shortModel_j, ← hjE]
    rfl)
  have htors : ∀ (a b : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular a b),
      m • (Point.some a b h : (A.baseChange ℂ).toAffine.Point) = 0 →
        a ∈ (algebraMap L ℂ).range ∧ b ∈ (algebraMap L ℂ).range := by
    intro a b h hP
    have h' : ((shortModel aJ).baseChange ℂ).toAffine.Nonsingular a b := hAℂ ▸ h
    have hP' : m • (Point.some a b h' : ((shortModel aJ).baseChange ℂ).toAffine.Point) = 0 :=
      nsmul_some_congr hAℂ h h' hP
    obtain ⟨ha, hb⟩ := htorsJ a b h' hP'
    exact ⟨⟨⟨a, hM₁L ha⟩, rfl⟩, ⟨⟨b, hM₁L hb⟩, rfl⟩⟩

  have hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (σ.restrictNormal L a) :=
    fun a ↦ (AlgEquiv.restrictNormal_commutes σ L a).symm

  obtain ⟨S₀, hS₀, hS₀p⟩ := frobenius_at_primes_of_degree_one hK hL
    (fun x ↦ shortModel (⟨ELL.j x, hL x⟩ : L)) hE hiso
  have hgood : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L w), W.IsElliptic ∧
        W.map (algebraMap (localizationAt L w) L) = A ∧ (W.a₄ = 0 ∨ IsUnit W.a₄) ∧
          (W.a₆ = 0 ∨ IsUnit W.a₆) := by
    have h4 : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        A.a₄ = 0 ∨ ∃ h : A.a₄ ∈ localizationAt L w, IsUnit (⟨A.a₄, h⟩ : localizationAt L w) := by
      by_cases h0 : A.a₄ = 0
      · exact Filter.Eventually.of_forall fun _ ↦ Or.inl h0
      · exact (eventually_isUnit_localizationAt h0).mono fun _ h ↦ Or.inr h
    have h6 : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        A.a₆ = 0 ∨ ∃ h : A.a₆ ∈ localizationAt L w, IsUnit (⟨A.a₆, h⟩ : localizationAt L w) := by
      by_cases h0 : A.a₆ = 0
      · exact Filter.Eventually.of_forall fun _ ↦ Or.inl h0
      · exact (eventually_isUnit_localizationAt h0).mono fun _ h ↦ Or.inr h
    filter_upwards [eventually_exists_model A, h4, h6] with w ⟨W, hW, hWA⟩ h4w h6w
    have e4 : algebraMap (localizationAt L w) L W.a₄ = A.a₄ := by rw [← hWA]; rfl
    have e6 : algebraMap (localizationAt L w) L W.a₆ = A.a₆ := by rw [← hWA]; rfl
    refine ⟨W, hW, hWA, ?_, ?_⟩
    · rcases h4w with h0 | ⟨h, hu⟩
      · left
        exact Subtype.ext (e4.trans h0)
      · right
        have : W.a₄ = ⟨A.a₄, h⟩ := Subtype.ext e4
        rwa [this]
    · rcases h6w with h0 | ⟨h, hu⟩
      · left
        exact Subtype.ext (e6.trans h0)
      · right
        have : W.a₆ = ⟨A.a₆, h⟩ := Subtype.ext e6
        rwa [this]
  obtain ⟨S₁, hS₁, hS₁p⟩ := exists_finite_forall_liesOver (K := K) hgood
  have h6m : ((6 * m : ℕ) : 𝓞 K) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    omega
  have hS : (S₀ ∪ S₁ ∪ {v : HeightOneSpectrum (𝓞 K) | ((6 * m : ℕ) : 𝓞 K) ∈ v.asIdeal}).Finite :=
    (hS₀.union hS₁).union (finite_setOf_mem_asIdeal h6m)

  obtain ⟨𝔭, h𝔭S, h𝔭1, 𝔓, hlies, -, hfrob⟩ := exists_isArithFrobAt L (σ.restrictNormal L) hS
  have : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := hlies
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at h𝔭S
  obtain ⟨⟨h𝔭S₀, h𝔭S₁⟩, h𝔭6m⟩ := h𝔭S
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  have hm𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal := fun h ↦ h𝔭6m (by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  have hnorm : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.absNorm_mem _
  have h5 : 5 ≤ Ideal.absNorm 𝔭.asIdeal := by
    refine hv.five_le_of_ne_two_of_ne_three (fun h2 ↦ h𝔭6m ?_) (fun h3 ↦ h𝔭6m ?_)
    · rw [h2] at hnorm
      rw [show ((6 * m : ℕ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) * ((3 * m : ℕ) : 𝓞 K) by push_cast; ring]
      exact Ideal.mul_mem_right _ _ hnorm
    · rw [h3] at hnorm
      rw [show ((6 * m : ℕ) : 𝓞 K) = ((3 : ℕ) : 𝓞 K) * ((2 * m : ℕ) : 𝓞 K) by push_cast; ring]
      exact Ideal.mul_mem_right _ _ hnorm

  obtain ⟨-, hcls, -⟩ := hS₀p 𝔭 h𝔭S₀ h𝔭1 𝔓
  obtain ⟨-, hτj⟩ := hcls (σ.restrictNormal L) hfrob
  have hAτ : A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L) = shortModel (⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀), hL _⟩ : L) := by
    rw [hAdef, shortModel_map]
    congr 1
    exact hτj x₀

  have hφex : ∃ φ : Isogeny A (A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)),
      (homConstSet (A.baseChange ℂ) ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ) :
        Set ℂ) = (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK (fun x ↦ shortModel (⟨ELL.j x, hL x⟩ : L))
      hE hiso 𝔭 x₀
    exact exists_isogeny_homConstSet_congr hAdef.symm hAτ.symm ⟨φ, hφ⟩
  obtain ⟨φ, hφ⟩ := hφex
  have hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K) :=
    nonempty_isogEnd_congr hAdef.symm (hE x₀).1
  have hEA' : Nonempty (isogEnd ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ) ≃+*
      𝓞 K) :=
    nonempty_isogEnd_congr hAτ.symm (hE _).1

  obtain ⟨W, hW, hWA, ha₄, ha₆⟩ := hS₁p 𝔭 h𝔭S₁ 𝔓 hlies
  have : W.IsShortNF := by
    have hinj : Function.Injective (algebraMap (localizationAt L 𝔓) L) := Subtype.val_injective
    refine ⟨hinj ?_, hinj ?_, hinj ?_⟩ <;> rw [map_zero]
    · rw [← a₁_of_isShortNF A, ← hWA]; rfl
    · rw [← a₂_of_isShortNF A, ← hWA]; rfl
    · rw [← a₃_of_isShortNF A, ← hWA]; rfl

  obtain ⟨D, hD, hDφ⟩ := exists_vcPoint_pointHomOver_eq hK 𝔭 hv h5 𝔓 hfrob hEA hEA' φ hφ hWA ha₄ ha₆
    hζL' hm𝔭

  obtain ⟨x, hx⟩ := exists_diagonal_of_isArithFrobAt m hm σ s hs 𝔭 hm𝔭 L hM₂L 𝔓 hfrob

  have hL₂ := lattice_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  have hL₂end := latticeEnd_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  have hsmul := classGroup_smul_ellOf (algebraMap K ℂ) hK _ _ hL₁end hL₂end (primeIdealUnit 𝔭)
    (by rw [hL₂, hL₁, Units.val_mul, idealLattice_mul])
  have hcl : primeClass 𝔭 = ClassGroup.mk K (primeIdealUnit 𝔭) := by
    rw [primeClass, ← classGroup_mk_primeUnit]
    rfl
  have hyL₂ : (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀ =
      ellOf (algebraMap K ℂ) _ hL₂end := by
    rw [hcl, hx₀ell, hsmul]
  have hjV' : (weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞))).j =
      ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ).j := by
    rw [j_congr (congrArg (fun B : WeierstrassCurve L ↦ B.baseChange ℂ) hAτ)]
    show _ = ((shortModel (⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀), hL _⟩ : L)).map (algebraMap L ℂ)).j
    rw [map_j, shortModel_j]
    show _ = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀)
    set_option backward.isDefEq.respectTransparency false in
      rw [hyL₂, ellOf, ELL.j_toEll]
    exact j_congr rfl
  obtain ⟨V', hV'⟩ := exists_variableChange_of_j_eq _ _ hjV'
  exact exists_uniformization_of_data hK σ s 𝔞 hf (σ.restrictNormal L) hτσ V₀ hV₀ htors 𝔭 x
    (hx 𝔞).1 (hx 𝔞).2 φ hφ D hD hDφ V' hV'

end

end Elliptic
end GroundTheory.Global
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open GroundTheory.LocalField (maximalAbelianExtension)
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]


omit [Algebra K ℂ] in
include hK in
theorem finite_units : Finite (𝓞 K)ˣ := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, hK] at h1
  have hr : Units.rank K = 0 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have : IsEmpty (Fin (Units.rank K)) := by rw [hr]; infer_instance
  have htors : ∀ x : (𝓞 K)ˣ, x ∈ Units.torsion K := fun x ↦ by
    obtain ⟨⟨ζ, e⟩, hx, -⟩ := Units.exist_unique_eq_mul_prod K x
    rw [Fintype.prod_empty, mul_one] at hx
    rw [hx]
    exact ζ.2
  exact Finite.of_injective (fun x ↦ (⟨x, htors x⟩ : Units.torsion K)) fun a b h ↦
    congrArg Subtype.val h


omit [Algebra K ℂ] [_root_.NumberField.IsTotallyComplex K] in
theorem exists_nat_mul_mem (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : K) :
    ∃ k : ℕ, 0 < k ∧ (k : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.2 (Units.ne_zero 𝔞))
  have halg : IsAlgebraic ℤ (t / a) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy0) 2, ?_⟩
  have hint : ((y.natAbs ^ 2 : ℕ) : K) * (t / a) ∈ (algebraMap (𝓞 K) K).range := by
    have h2 : IsIntegral ℤ (y • (y • (t / a))) := hy.smul y
    have e : ((y.natAbs ^ 2 : ℕ) : K) * (t / a) = y • (y • (t / a)) := by
      rw [smul_smul, zsmul_eq_mul]
      have hsq : ((y.natAbs : ℕ) : K) ^ 2 = (y : K) ^ 2 := by
        rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
      push_cast
      rw [hsq]
      ring
    rw [e]
    exact ⟨⟨_, h2⟩, rfl⟩
  obtain ⟨b, hb⟩ := hint
  have : ((y.natAbs ^ 2 : ℕ) : K) * t = algebraMap (𝓞 K) K b * a := by
    rw [hb]
    field_simp
  rw [this, ← Algebra.smul_def]
  exact (𝔞 : Submodule (𝓞 K) K).smul_mem b ha


include hK in
theorem main_theorem_complexMultiplication (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f) :
    ∃! f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
        f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical
  have := finite_units hK
  have hLs := lattice_idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)

  have hlev : ∀ n : ℕ, ∃ F : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) F ∧
      ∀ t y : K, (((n + 1).factorial : ℕ) : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          F (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) :=
    fun n ↦ exists_uniformization_level hK σ s hs 𝔞 hf (Nat.factorial_ne_zero (n + 1))
  choose F hF hFp using hlev
  have hF' : ∀ n, IsAnalyticUniformization
      (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)).lattice (F n) := fun n ↦ by
    rw [hLs]
    exact hF n

  have hc : ∀ n, ∃ ε : (𝓞 K)ˣ, ∀ z, F n z = F 0 (algebraMap K ℂ (algebraMap (𝓞 K) K ε) * z) := by
    intro n
    obtain ⟨c, -, hcl, hcz⟩ := exists_mul_eq_of_isAnalyticUniformization (hF' 0) (hF' n)
    rw [hLs] at hcl
    obtain ⟨ε, rfl⟩ := exists_unit_of_forall_mem_iff (algebraMap K ℂ) hK _ hcl
    exact ⟨ε, hcz⟩
  choose ε hε using hc

  obtain ⟨ε₀, hinf⟩ := Finite.exists_infinite_fiber ε
  have hinf' : (ε ⁻¹' {ε₀}).Infinite := Set.infinite_coe_iff.1 hinf
  obtain ⟨n₀, hn₀⟩ := hinf'.nonempty
  have hprop : ∀ t y : K,
      IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
        F n₀ (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
    intro t y hq
    obtain ⟨k, hk0, hk⟩ := exists_nat_mul_mem 𝔞 t
    obtain ⟨n, hn, hkn⟩ := hinf'.exists_gt k
    obtain ⟨q, hq'⟩ := Nat.dvd_factorial hk0 (show k ≤ n + 1 by omega)
    have hmt : (((n + 1).factorial : ℕ) : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hq', Nat.cast_mul, mul_comm (k : K), mul_assoc]
      have h := (𝔞 : Submodule (𝓞 K) K).smul_mem (q : 𝓞 K) hk
      rwa [Algebra.smul_def, map_natCast] at h
    have e₀ : ε n₀ = ε₀ := hn₀
    have e₁ : ε n = ε₀ := hn
    rw [hε n₀, e₀, ← e₁, ← hε n]
    exact hFp n t y hmt hq
  refine ⟨F n₀, ⟨hF n₀, hprop⟩, fun g ⟨hg, hgp⟩ ↦ ?_⟩

  have hg' : IsAnalyticUniformization (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)).lattice g := by
    rw [hLs]
    exact hg
  obtain ⟨c, -, -, hcz⟩ := exists_mul_eq_of_isAnalyticUniformization (hF' n₀) hg'
  have hker : ∀ y : K, (c - 1) * algebraMap K ℂ y ∈
      (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞)).lattice := by
    intro y
    obtain ⟨q, hq⟩ := (IdeleGroup.smulQuotient s⁻¹ 𝔞).surjective (Submodule.Quotient.mk y)
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 := hgp t y hq
    have h2 := hprop t y hq
    rw [hcz] at h1
    have h3 : F n₀ ((c - 1) * algebraMap K ℂ y) = 0 := by
      rw [sub_mul, one_mul, map_sub, h1, h2, sub_self]
    exact ((hF' n₀).map_eq_zero_iff _).1 h3
  have hc1 : c = 1 := by
    by_contra hne
    obtain ⟨δ, hδ, hδl⟩ := exists_pos_le_norm (idealPeriodPair (algebraMap K ℂ) hK (s⁻¹ • 𝔞))
    obtain ⟨N, hN⟩ := exists_nat_gt (‖c - 1‖ / δ)
    have hmem := hker ((N + 1 : ℕ) : K)⁻¹
    have hval : algebraMap K ℂ ((N + 1 : ℕ) : K)⁻¹ = ((N + 1 : ℕ) : ℂ)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [hval] at hmem
    have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hne' : (c - 1) * ((N + 1 : ℕ) : ℂ)⁻¹ ≠ 0 :=
      mul_ne_zero (sub_ne_zero.2 hne) (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N)))
    have hle := hδl _ hmem hne'
    rw [norm_mul, norm_inv, Complex.norm_natCast] at hle
    have h1 : ‖c - 1‖ < δ * (N + 1 : ℕ) := by
      rw [div_lt_iff₀ hδ] at hN
      push_cast
      nlinarith
    have h2 : δ * (N + 1 : ℕ) ≤ ‖c - 1‖ := by
      rw [← le_div_iff₀ hpos, div_eq_mul_inv]
      exact hle
    linarith
  ext z
  rw [hcz, hc1, one_mul]

end

end Elliptic
end GroundTheory.Global

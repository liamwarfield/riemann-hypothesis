module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem locallyOfFiniteType_baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    (K : Type u) [Field K] [Algebra k K] :
    AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType p))

theorem quasiCompact_baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.QuasiCompact p]
    (K : Type u) [Field K] [Algebra k K] :
    AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (AlgebraicGeometry.QuasiCompact p))

theorem smooth_baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (K : Type u) [Field K] [Algebra k K] :
    AlgebraicGeometry.Smooth (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (AlgebraicGeometry.Smooth p))

structure EmbeddingDatum (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) where
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  emb : Y ⟶ ambient
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  isClosedImmersion_emb : AlgebraicGeometry.IsClosedImmersion emb
  nonzeroOnComponents_ker : NonzeroOnComponents emb.ker
  comp_eq : emb ≫ ambientStruct = p
  sncEmpty : InStrictNormalCrossingPosition ambientStruct ([] : List ambient.IdealSheafData)

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

instance instIsAffineAmbient (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.IsAffine D.ambient := D.isAffine_ambient

instance instSmoothAmbientStruct (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.Smooth D.ambientStruct := D.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.LocallyOfFiniteType D.ambientStruct :=
  D.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.QuasiCompact D.ambientStruct := D.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.IsClosedImmersion D.emb := D.isClosedImmersion_emb

end EmbeddingDatum

def embeddingDatumOfClosedImmersion {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A]
    (q : A ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (e : Y ⟶ A) [AlgebraicGeometry.IsClosedImmersion e]
    (hker : NonzeroOnComponents e.ker) (hcomp : e ≫ q = p)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A.IdealSheafData)) :
    EmbeddingDatum k Y p where
  ambient := A
  ambientStruct := q
  emb := e
  isAffine_ambient := inferInstance
  smooth_ambientStruct := inferInstance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := hsnc

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

theorem pullbackCondition_baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    (baseChangeProjection p K ≫ D.emb) ≫ D.ambientStruct =
      baseChangeToSpec p K ≫ specMapAlgebraMap k K := by
  rw [Category.assoc, D.comp_eq]
  exact pullback.condition

def baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [Algebra k K] :
    baseChange p K ⟶ baseChange D.ambientStruct K :=
  pullback.lift (baseChangeProjection p K ≫ D.emb) (baseChangeToSpec p K)
    (by exact pullbackCondition_baseChangeEmb D K)

@[simp]
theorem baseChangeEmb_comp_baseChangeProjection (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    D.baseChangeEmb K ≫ baseChangeProjection D.ambientStruct K = baseChangeProjection p K ≫ D.emb :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeEmb_comp_baseChangeToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K = baseChangeToSpec p K :=
  pullback.lift_snd _ _ _

theorem isPullback_baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    IsPullback (D.baseChangeEmb K) (baseChangeProjection p K) (baseChangeProjection D.ambientStruct K)
      D.emb := by
  have hbig : IsPullback (D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K)
      (baseChangeProjection p K) (specMapAlgebraMap k K) (D.emb ≫ D.ambientStruct) := by
    rw [baseChangeEmb_comp_baseChangeToSpec D K, D.comp_eq]
    exact (IsPullback.of_hasPullback p (specMapAlgebraMap k K)).flip
  exact IsPullback.of_right hbig (baseChangeEmb_comp_baseChangeProjection D K)
    (IsPullback.of_hasPullback D.ambientStruct (specMapAlgebraMap k K)).flip

theorem isClosedImmersion_baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : AlgebraicGeometry.IsClosedImmersion (D.baseChangeEmb K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeEmb D K).flip D.isClosedImmersion_emb

instance instIsClosedImmersionBaseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : AlgebraicGeometry.IsClosedImmersion (D.baseChangeEmb K) :=
  isClosedImmersion_baseChangeEmb D K

theorem isAffine_baseChange_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : AlgebraicGeometry.IsAffine (baseChange D.ambientStruct K) :=
  isAffine_baseChange D.ambientStruct K

theorem smooth_baseChangeToSpec_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    AlgebraicGeometry.Smooth (baseChangeToSpec D.ambientStruct K) :=
  smooth_baseChangeToSpec D.ambientStruct K

theorem locallyOfFiniteType_baseChangeToSpec_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
  locallyOfFiniteType_baseChangeToSpec D.ambientStruct K

theorem quasiCompact_baseChangeToSpec_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    AlgebraicGeometry.QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
  quasiCompact_baseChangeToSpec D.ambientStruct K

def baseChange (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [CharZero K]
    [Algebra k K]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (EmbeddedResolution.baseChange D.ambientStruct K).IdealSheafData)) :
    EmbeddingDatum K (EmbeddedResolution.baseChange p K) (baseChangeToSpec p K) where
  ambient := EmbeddedResolution.baseChange D.ambientStruct K
  ambientStruct := baseChangeToSpec D.ambientStruct K
  emb := D.baseChangeEmb K
  isAffine_ambient := isAffine_baseChange_ambientToSpec D K
  smooth_ambientStruct := smooth_baseChangeToSpec_ambientToSpec D K
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  quasiCompact_ambientStruct := quasiCompact_baseChangeToSpec_ambientToSpec D K
  isClosedImmersion_emb := isClosedImmersion_baseChangeEmb D K
  nonzeroOnComponents_ker := hker
  comp_eq := baseChangeEmb_comp_baseChangeToSpec D K
  sncEmpty := hsnc

end EmbeddingDatum

abbrev EmbeddedResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], EmbeddingDatum k Y p → SequenceOfBlowups Y

abbrev EmbeddingChoice : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], EmbeddingDatum k Y p

def EmbeddedResolutionRule.toAffineResolutionRule (R : EmbeddedResolutionRule.{u}) (S : EmbeddingChoice.{u}) :
    AffineResolutionRule.{u} :=
  fun k _ _ Y p _ _ _ _ => R k Y p (S k Y p)

@[simp]
theorem EmbeddedResolutionRule.toAffineResolutionRule_apply (R : EmbeddedResolutionRule.{u}) (S : EmbeddingChoice.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    R.toAffineResolutionRule S k Y p = R k Y p (S k Y p) := rfl

def EmbeddedResolutionRule.HasProperCenters (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y p) (i : ℕ),
    i < (R k Y p D).length → (R k Y p D).center i ≠ ⊤

def EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [AlgebraicGeometry.Smooth φ] (ψ : Y' ⟶ Y),
    φ ≫ D.ambientStruct = D'.ambientStruct →
    IsPullback D'.emb ψ φ D.emb →
    IsPullbackBlowupSequence ψ (R k Y' p' D') (R k Y p D)

def EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [CharZero K] [Algebra k K] [AlgebraicGeometry.IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)),
    haveI : AlgebraicGeometry.IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K) (D.baseChange K hker hsnc))
      (R k Y p D)

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem iso_hom_comp_projectionToBase {X' : Scheme.{u}} {s' s'' : SequenceOfBlowups X'}
    (ε : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ≅ s''.schemeAt i))
    (h0 : (ε 0 (Nat.zero_le _)).hom ≫ s''.isoZero.hom = s'.isoZero.hom)
    (hst : ∀ i : ℕ, ∀ hi : i < s'.length,
      (ε (i + 1) hi).hom ≫ s''.transitionMapSucc i = s'.transitionMapSucc i ≫ (ε i hi.le).hom) :
    ∀ i : ℕ, ∀ hi : i ≤ s'.length, (ε i hi).hom ≫ s''.projectionToBase i = s'.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [s''.projectionToBase_zero, s'.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    rw [s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← Category.assoc,
      hst n hi, Category.assoc, ih (Nat.le_of_succ_le hi)]

private def pullbackProjectionToBaseIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) :
    Limits.pullback φ (s.projectionToBase a) ≅ Limits.pullback φ (s.projectionToBase b) :=
  eqToIso (by rw [h])

private theorem pullbackIsoOfEq_hom_fst {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (h : a = b) :
    (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.fst φ (s.projectionToBase b)
      = Limits.pullback.fst φ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

private theorem pullbackIsoOfEq_hom_comp_pullbackTransitionMap {X X' : Scheme.{u}} (φ : X' ⟶ X)
    (s : SequenceOfBlowups X) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    (pullbackProjectionToBaseIsoOfEq φ s hb).hom ≫ s.pullbackTransitionMap φ hab'
      = s.pullbackTransitionMap φ hab ≫ (pullbackProjectionToBaseIsoOfEq φ s ha).hom := by
  subst ha
  subst hb
  have hpr : hab = hab' := rfl
  subst hpr
  simp [pullbackProjectionToBaseIsoOfEq]

private theorem comap_pullbackIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) {W : Scheme.{u}} (g : W ⟶ Limits.pullback φ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.snd φ (s.projectionToBase b))
      = (s.center a).comap (g ≫ Limits.pullback.snd φ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

private theorem strictMono_enumeration_le {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    ∀ i, i < n → i < m → r i ≤ q i := by
  have main : ∀ k i : ℕ, i < k → i < n → i < m → r i ≤ q i := by
    intro k
    induction k with
    | zero => intro i hik; exact absurd hik (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hik hin him
      by_contra hcon
      push Not at hcon
      have hqL : q i < L := hq1 i him
      obtain ⟨j, hjn, hj⟩ := (hr4 (q i) hqL).mp ((hq4 (q i) hqL).mpr ⟨i, him, rfl⟩)
      have hji : j < i := by
        by_contra hc
        push Not at hc
        rcases Nat.eq_or_lt_of_le hc with h' | h'
        · rw [← h'] at hj
          omega
        · have hlt := hr2 i j hjn.le h'
          omega
      have h1 : r j ≤ q j := ih j (by omega) (by omega) (by omega)
      have h2 : q j < q i := hq2 j i him.le hji
      omega
  intro i hin him
  exact main (i + 1) i (Nat.lt_succ_self i) hin him

private theorem strictMono_enumeration_unique {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr1 : ∀ i, i < n → r i < L)
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hrn : r n = L)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hqm : q m = L)
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    n = m ∧ ∀ i, i ≤ n → r i = q i := by
  have le1 := strictMono_enumeration_le hr2 hq1 hq2 hr4 hq4
  have le2 := strictMono_enumeration_le hq2 hr1 hr2 hq4 hr4
  have heq : ∀ i, i < n → i < m → r i = q i := fun i h1 h2 =>
    le_antisymm (le1 i h1 h2) (le2 i h2 h1)
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heqnm | hgt
    · exfalso
      have hqn : q n < L := hq1 n hlt
      obtain ⟨j, hjn, hj⟩ := (hr4 (q n) hqn).mp ((hq4 (q n) hqn).mpr ⟨n, hlt, rfl⟩)
      have ha : r j = q j := heq j hjn (hjn.trans hlt)
      have hb : q j < q n := hq2 j n hlt.le hjn
      omega
    · exact heqnm
    · exfalso
      have hrm : r m < L := hr1 m hgt
      obtain ⟨j, hjm, hj⟩ := (hq4 (r m) hrm).mp ((hr4 (r m) hrm).mpr ⟨m, hgt, rfl⟩)
      have ha : r j = q j := heq j (hjm.trans hgt) hjm
      have hb : r j < r m := hr2 j m hgt.le hjm
      omega
  refine ⟨hnm, ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [h, hrn, hnm, hqm]
  · exact heq i h (by omega)

namespace IsPullbackBlowupSequence

theorem of_isomorphic {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (e : s'.Isomorphic s'') : IsPullbackBlowupSequence φ s'' s := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨hlen, ε, h0, hst, hc⟩ := e
  have hcl : ∀ i : ℕ, i ≤ s''.length → i ≤ s'.length := fun i hi => le_of_le_of_eq hi hlen.symm
  have hcl' : ∀ i : ℕ, i < s''.length → i < s'.length := fun i hi => lt_of_lt_of_eq hi hlen.symm
  have hproj := iso_hom_comp_projectionToBase ε h0 hst
  refine ⟨r, fun i hi => (ε i (hcl i hi)).symm ≪≫ E i (hcl i hi),
    fun i hi => hr1 i (hcl' i hi), fun i j hj hij => hr2 i j (hcl j hj) hij,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlen]; exact hr3
  · intro i hi
    rw [hr4 i hi, hlen]
  · intro i hi
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst i (hcl i hi)]
    rw [← hproj i (hcl i hi)]
    simp
  · intro i hi hr
    have h1 := hstepE i (hcl' i hi) hr
    have h2 := hst i (hcl' i hi)
    have key : s''.transitionMapSucc i ≫ (ε i (hcl i hi.le)).inv
        = (ε (i + 1) (hcl' i hi)).inv ≫ s'.transitionMapSucc i := by
      rw [← Iso.cancel_iso_hom_left (ε (i + 1) (hcl' i hi)), ← Category.assoc, h2]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, key, Category.assoc, h1, Category.assoc]
  · intro i hi
    have h1 := hcen i (hcl' i hi)
    have h2 := hc i (hcl' i hi)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Scheme.IdealSheafData.comap_comp, ← h1, ← h2, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

theorem isomorphic {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (h' : IsPullbackBlowupSequence φ s'' s) : s'.Isomorphic s'' := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩ := h'
  obtain ⟨hnm, hall⟩ := strictMono_enumeration_unique hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4
  refine ⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq φ s (hall i hi) ≪≫
    (G i (le_of_le_of_eq hi hnm)).symm, ?_, ?_, ?_⟩
  · have hG0 : (G 0 (le_of_le_of_eq (Nat.zero_le _) hnm)).inv ≫ s''.projectionToBase 0
        = Limits.pullback.fst φ (s.projectionToBase (q 0)) := by
      rw [← gfst 0 (le_of_le_of_eq (Nat.zero_le _) hnm)]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst, hfst 0 (Nat.zero_le _),
      s'.projectionToBase_zero]
  · intro i hi
    have hr : r i ≤ r (i + 1) := (hr2 i (i + 1) hi (Nat.lt_succ_self i)).le
    have hq' : q i ≤ q (i + 1) :=
      (hq2 i (i + 1) (le_of_le_of_eq hi hnm) (Nat.lt_succ_self i)).le
    have h1 := hstepE i hi hr
    have h2 := gstep i (lt_of_lt_of_eq hi hnm) hq'
    have hGinv : (G (i + 1) (le_of_le_of_eq hi hnm)).inv ≫ s''.transitionMapSucc i
        = s.pullbackTransitionMap φ hq' ≫ (G i (le_of_le_of_eq (Nat.le_of_succ_le hi) hnm)).inv := by
      rw [← Iso.cancel_iso_hom_left (G (i + 1) (le_of_le_of_eq hi hnm)), ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp, ← Category.assoc, ← h2]
      simp
    have htrans := pullbackIsoOfEq_hom_comp_pullbackTransitionMap φ s (hall i (Nat.le_of_succ_le hi))
      (hall (i + 1) hi) hr hq'
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hGinv]
    rw [reassoc_of% h1, reassoc_of% htrans]
  · intro i hi
    have h1 := hcen i hi
    have h2 := gcen i (lt_of_lt_of_eq hi hnm)
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [h2, h1, ← Scheme.IdealSheafData.comap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact comap_pullbackIsoOfEq φ s (hall i (Nat.le_of_succ_le hi)) _

end IsPullbackBlowupSequence

end FunctorialResolution.EmbeddedResolution
end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def SmoothPullbackHasLocalAmbientEmbedding : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X Y A : Scheme.{u})
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pA : A ⟶ Spec (CommRingCat.of k)) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M c : ℕ) (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) [IsClosedImmersion ρ],
      ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA →
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) ρ c →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Scheme.{u}) (pA' : A' ⟶ Spec (CommRingCat.of k)),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : V.toScheme ⟶ A', IsClosedImmersion j ∧
            IsPullback j (V.ι ≫ h) g i ∧
            ∃ N₀ : ℕ, r ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin (M + N))),
                IsClosedImmersion σ ∧
                σ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N))) = pA' ∧
                HasSmoothCoordCodim
                  (affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N)))) σ (c + (N - r))

end FunctorialResolution.EmbeddedResolution

end
end

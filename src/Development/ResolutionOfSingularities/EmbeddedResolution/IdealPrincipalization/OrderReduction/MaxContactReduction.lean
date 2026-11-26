module

public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped Classical

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactReduction

def emptyMarkedSeq (T : MarkedIdealWithBoundary.{u}) : T.SequenceOfBlowups :=
  (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups

def IsMaxContactCoord (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

structure FiniteOpenCoverWithIdeals (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) where
  idx : Type u
  finiteIdx : Finite idx
  opens : idx → T.scheme.Opens
  localIdeal : (i : idx) → (opens i).toScheme.IdealSheafData

instance instFiniteCoverIdx {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : Finite D.idx :=
  D.finiteIdx

structure IsMaxContactCover (T : MarkedIdealWithBoundary.{u}) (D : FiniteOpenCoverWithIdeals T)
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (μ : ℕ) : Prop where
  covers : iSup D.opens = ⊤
  isAffine : ∀ i : D.idx, IsAffineOpen (D.opens i)
  dichotomy : ∀ i : D.idx,
    (Disjoint (orderAtLeastLocus W μ) ((D.opens i : T.scheme.Opens) : Set ↥T.scheme) ∧
      D.localIdeal i = ⊤) ∨
    (∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
      D.localIdeal i = c.coordIdeal {j} ∧
        @IsMaxContactCoord T.base _ T.scheme T.structMap hft W μ (D.opens i) n c j)

def trivialCover (T : MarkedIdealWithBoundary.{u}) : FiniteOpenCoverWithIdeals T where
  idx := PUnit.{u + 1}
  finiteIdx := inferInstance
  opens := fun _ => ⊤
  localIdeal := fun _ => ⊤

def maxContactCover (T : MarkedIdealWithBoundary.{u}) (hft : LocallyOfFiniteType T.structMap)
    (W : T.scheme.IdealSheafData) (μ : ℕ) : FiniteOpenCoverWithIdeals T :=
  if h : ∃ D : FiniteOpenCoverWithIdeals T, IsMaxContactCover T D hft W μ then h.choose else trivialCover T

def FiniteOpenCoverWithIdeals.disjointUnion {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : Scheme.{u} :=
  sigmaOpens T.scheme D.opens

def FiniteOpenCoverWithIdeals.disjointUnionMap {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : D.disjointUnion ⟶ T.scheme :=
  sigmaOpensDesc T.scheme D.opens

def FiniteOpenCoverWithIdeals.ι {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.opens i).toScheme ⟶ D.disjointUnion :=
  Sigma.ι (fun i => (D.opens i).toScheme) i

def FiniteOpenCoverWithIdeals.iInfImageIdeal {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : D.disjointUnion.IdealSheafData :=
  ⨅ i : D.idx, imageIdealSheaf (D.ι i) (D.localIdeal i)

def FiniteOpenCoverWithIdeals.markedTriple {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) (W : T.scheme.IdealSheafData)
    (μ : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := D.disjointUnion
  structMap := D.disjointUnionMap ≫ T.structMap
  ideal := W.comap D.disjointUnionMap
  mult := μ
  boundary := T.boundary.map (fun Dv => Dv.comap D.disjointUnionMap)

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def iteratedStrictTransform (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    (i : ℕ) → (s.obj i).IdealSheafData
  | 0 => H.comap s.isoZero.hom
  | i + 1 => Blowup.strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i)

theorem iteratedStrictTransform_zero (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    iteratedStrictTransform s H 0 = H.comap s.isoZero.hom := rfl

theorem iteratedStrictTransform_succ (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (i : ℕ) :
    iteratedStrictTransform s H (i + 1) =
      Blowup.strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i) := rfl

def strictTransformAtLength (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    (s.obj s.length).IdealSheafData :=
  iteratedStrictTransform s H s.length

theorem strictTransformAtLength_eq (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    strictTransformAtLength s H = iteratedStrictTransform s H s.length := rfl

def asMarkedData (s : MarkedBlowupSequenceData p I m E) (d : BlowupSequenceData (s.obj s.length)) :
    Option (MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :=
  if h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) then
    some (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h)
  else
    none

def concatOfIsMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData (s.obj s.length)) : MarkedBlowupSequenceData p I m E :=
  match asMarkedData s d with
  | some t => s.append t hinv
  | none => s

end

def tunedIdeal (S : MarkedIdealWithBoundary.{u}) (hft : LocallyOfFiniteType S.structMap) :
    S.scheme.IdealSheafData :=
  @balancedTunedSheaf S.base _ _ S.scheme S.structMap hft S.ideal S.mult

def tunedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary.{u} where
  base := S.base
  instField := S.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ S.structMap
  ideal :=
    @balancedTunedSheaf S.base _ _ (s.obj s.length) (s.proj s.length ≫ S.structMap) hft
      (s.ideal s.length) S.mult
  mult := tuningExponent S.mult
  boundary := extra ++ (s.boundary s.length).drop keep

def appendLowerDimReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    (S : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ) :
    MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  if hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) then
    if hdim : (tunedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc then
      concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (resolveLower (tunedTriple S s hft extra keep) hdim n).toSequenceOfBlowups)
    else s
  else s

def separateBoundary (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) :
    ℕ → MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary
  | 0 => emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary
  | j + 1 => appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S j) [] 0 j

def reduceAlongHypersurface (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (H : S.scheme.IdealSheafData) : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S S.boundary.length)
    [strictTransformAtLength (separateBoundary hinv T resolveLower S S.boundary.length) H] S.boundary.length 0

def descendStrictPullback (T S : MarkedIdealWithBoundary.{u}) (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    Option (BlowupSequenceData T.scheme) :=
  if h : ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups then
    some h.choose
  else
    none

def asMarkedSeq (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if h : d.IsMarked T.structMap T.ideal T.mult T.boundary then
    (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h).toMarkedSequenceOfBlowups
  else
    emptyMarkedSeq T

def dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) : MarkedIdealWithBoundary.{u} :=
  T.withBoundary (T.boundary.filter (fun D => decide (D ≠ ⊤)))

theorem dropTrivialBoundary_def (T : MarkedIdealWithBoundary.{u}) :
    dropTrivialBoundary T = T.withBoundary (T.boundary.filter (fun D => decide (D ≠ ⊤))) := rfl

@[simp] theorem dropTrivialBoundary_mult (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).mult = T.mult := rfl

@[simp] theorem dropTrivialBoundary_dim (T : MarkedIdealWithBoundary.{u}) : (dropTrivialBoundary T).krullDimSucc = T.krullDimSucc := rfl

theorem dropTrivialBoundary_boundary (T : MarkedIdealWithBoundary.{u}) :
    (dropTrivialBoundary T).boundary = T.boundary.filter (fun D => decide (D ≠ ⊤)) := rfl

def reduceOrderOfValid (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible) : T.SequenceOfBlowups :=
  have hft : LocallyOfFiniteType (dropTrivialBoundary T).structMap := hv.locallyOfFiniteType
  let W := tunedIdeal (dropTrivialBoundary T) hft
  let μ := tuningExponent (dropTrivialBoundary T).mult
  let D := maxContactCover (dropTrivialBoundary T) hft W μ
  let S := D.markedTriple W μ
  match descendStrictPullback (dropTrivialBoundary T) S D.disjointUnionMap (reduceAlongHypersurface hinv (dropTrivialBoundary T) resolveLower S D.iInfImageIdeal) with
  | some d => asMarkedSeq T d
  | none => emptyMarkedSeq T

def reduceOrder (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) : T.SequenceOfBlowups :=
  if hv : T.IsAdmissible then
    if orderAtLeastLocus T.ideal T.mult = ∅ then emptyMarkedSeq T else reduceOrderOfValid hinv T resolveLower hv
  else
    emptyMarkedSeq T

theorem reduceOrder_of_orderAtLeastLocus_eq_empty (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (h : orderAtLeastLocus T.ideal T.mult = ∅) : reduceOrder hinv T resolveLower = emptyMarkedSeq T := by
  unfold reduceOrder
  rw [dite_eq_left hv, if_pos h]

end MaxContactReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IndependenceOfHypersurface
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionIndependence

private theorem toSequenceOfBlowups_eq_of_heq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : X.IdealSheafData} {m₁ m₂ : ℕ}
    {E₁ E₂ : List X.IdealSheafData} (s₁ : MarkedSequenceOfBlowups p I₁ m₁ E₁)
    (s₂ : MarkedSequenceOfBlowups p I₂ m₂ E₂) (hI : I₁ = I₂) (hm : m₁ = m₂) (hE : E₁ = E₂)
    (h : HEq s₁ s₂) : s₁.toSequenceOfBlowups = s₂.toSequenceOfBlowups := by
  subst hI
  subst hm
  subst hE
  rw [eq_of_heq h]

theorem subschemeι_comap_comp_comp_eq {A B C : Scheme.{u}} (e : A ⟶ B) (J : B.IdealSheafData)
    (f g : B ⟶ C) (h : J.subschemeι ≫ f = J.subschemeι ≫ g) :
    (J.comap e).subschemeι ≫ (e ≫ f) = (J.comap e).subschemeι ≫ (e ≫ g) := by
  have : IsClosedImmersion (Limits.pullback.fst e J.subschemeι) := inferInstance
  have hker : J.comap e = Scheme.Hom.ker (Limits.pullback.fst e J.subschemeι) := rfl
  have hc := Limits.pullback.condition (f := e) (g := J.subschemeι)
  have key : Limits.pullback.fst e J.subschemeι ≫ (e ≫ f)
      = Limits.pullback.fst e J.subschemeι ≫ (e ≫ g) := by
    calc Limits.pullback.fst e J.subschemeι ≫ (e ≫ f)
        = (Limits.pullback.fst e J.subschemeι ≫ e) ≫ f := by rw [Category.assoc]
      _ = (Limits.pullback.snd e J.subschemeι ≫ J.subschemeι) ≫ f := by rw [hc]
      _ = Limits.pullback.snd e J.subschemeι ≫ (J.subschemeι ≫ f) := by rw [Category.assoc]
      _ = Limits.pullback.snd e J.subschemeι ≫ (J.subschemeι ≫ g) := by rw [h]
      _ = (Limits.pullback.snd e J.subschemeι ≫ J.subschemeι) ≫ g := by rw [Category.assoc]
      _ = (Limits.pullback.fst e J.subschemeι ≫ e) ≫ g := by rw [hc]
      _ = Limits.pullback.fst e J.subschemeι ≫ (e ≫ g) := by rw [Category.assoc]
  rw [hker, ← kerSubschemeIso_hom_comp (Limits.pullback.fst e J.subschemeι), Category.assoc,
    Category.assoc, key]

theorem le_center_of_center_support_subset (hin : OrderReduction.OrderReductionHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    (i : ℕ) (hi : i < s.length) (J : (s.schemeAt i).IdealSheafData)
    (hJ : (((s.center i).support : Set ↥(s.schemeAt i))) ⊆ ((J.support : Set ↥(s.schemeAt i)))) :
    J ≤ s.center i :=
  hin.smooth_center_radical T.base (s.schemeAt i) (s.projectionToBase i ≫ T.structMap) (s.center i)
    (s.center_smooth i hi) J hJ

theorem isAdmissible_and_isStrictPullbackBlowupSeq_of_etale
    (hin : OrderReduction.OrderReductionHypotheses.{u})
    (P : ℕ → Prop) (hPdown : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsBoundaryDivisorReduction P 0 A B)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hD : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hlen : 0 < T.boundary.length)
    (V : Scheme.{u}) (q : V ⟶ Spec (CommRingCat.of T.base)) (ψ : V ⟶ T.scheme)
    (hψ : AlgebraicGeometry.Etale ψ) (hq : AlgebraicGeometry.QuasiCompact q)
    (hcomp : ψ ≫ T.structMap = q)
    (hcov : orderAtLeastLocus T.ideal T.mult ⊆ Set.range ψ.base) :
    (T.pullbackAlong V q ψ).IsAdmissible ∧
      IsStrictPullbackBlowupSeq ψ (A (T.pullbackAlong V q ψ)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  have := hV.charZero
  have hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : AlgebraicGeometry.QuasiCompact T.structMap := hV.quasiCompact
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have : AlgebraicGeometry.Etale ψ := hψ
  have : AlgebraicGeometry.QuasiCompact q := hq
  have : AlgebraicGeometry.Smooth ψ := inferInstance
  have := hV.isNoetherian
  have : AlgebraicGeometry.IsLocallyNoetherian T.scheme := inferInstance
  have hVal : (T.pullbackAlong V q ψ).IsAdmissible := hin.valid_pullbackAlong T hV V q ψ hcomp
  have hftq : AlgebraicGeometry.LocallyOfFiniteType q := hVal.locallyOfFiniteType
  have hOT : T.IsOrderBoundedByMult := (T.isOrderBoundedByMult_iff).2 hO
  have hP' : P (T.pullbackAlong V q ψ).krullDimSucc := by
    refine hPdown _ _ ?_ hP
    exact hin.schemeDim_le_of_etale V T.scheme ψ hV.topologicalKrullDim_lt_top
  have hO' : (T.pullbackAlong V q ψ).IsOrderBoundedByMult := by
    rw [MarkedIdealWithBoundary.isOrderBoundedByMult_iff]
    intro x
    exact le_of_eq_of_le (orderAt_comap T.base T.structMap ψ T.ideal x) (hO _)
  have hderivBal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hD hft
  have hDB' : IsDerivBalanced T.base q (T.ideal.comap ψ) T.mult :=
    hin.dBalanced_comap T hV V q ψ hcomp hderivBal
  have hD' : ∀ hft2 : AlgebraicGeometry.LocallyOfFiniteType (T.pullbackAlong V q ψ).structMap,
      (T.pullbackAlong V q ψ).IsBalanced hft2 := fun _ => hDB'
  have hj' : 0 < (T.pullbackAlong V q ψ).boundary.length := by
    change 0 < (T.boundary.map (fun D => D.comap ψ)).length
    rw [List.length_map]
    exact hlen
  have hpull : IsPullbackBlowupSequence ψ (A (T.pullbackAlong V q ψ)).toSequenceOfBlowups (A T).toSequenceOfBlowups :=
    hspec.isPullbackBlowupSequence_of_smooth T hV hP hOT (hD _) hlen V q ψ hcomp hVal hP' hO' (hD' _) hj'
  refine ⟨hVal, hin.isStrictPullbackSeq V T.scheme ψ _ _ hpull ?_ ?_⟩
  · intro i hi
    exact hspec.center_nonempty T hV hP hOT (hD _) hlen i hi
  · intro i hi x hx
    exact hcov (hin.center_mem_coSupport T hV (A T) i hi x hx)

theorem isomorphic_withBoundary_cons_of_isMaxContactHypersurface
    (hin : OrderReduction.OrderReductionHypotheses.{u})
    (P : ℕ → Prop) (hPdown : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsBoundaryDivisorReduction P 0 A B)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hD : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hMC : ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsMaxContactInvariant T.base T.structMap T.ideal T.mult)
    (N : List T.scheme.IdealSheafData) (H₁ H₂ : T.scheme.IdealSheafData)
    (hbd : T.boundary = H₁ :: N)
    (hV₂ : (T.withBoundary (H₂ :: N)).IsAdmissible)
    (hH₁ : ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult H₁)
    (hH₂ : ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult H₂) :
    (A T).toSequenceOfBlowups.Isomorphic (A (T.withBoundary (H₂ :: N))).toSequenceOfBlowups := by
  have := hV.charZero
  have hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : AlgebraicGeometry.QuasiCompact T.structMap := hV.quasiCompact
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hsnc₁ : InStrictNormalCrossingPosition T.structMap (H₁ :: N) := by
    rw [← hbd]; exact hV.snc
  have hsnc₂ : InStrictNormalCrossingPosition T.structMap (H₂ :: N) := hV₂.snc
  obtain ⟨V, ψ₁, ψ₂, hψ₁, hψ₂, hqc, hftq, hcompeq, hcov₁, hcov₂, hidl, hHH, hNN, hmax⟩ :=
    hin.etaleEqualization T.base T.scheme T.structMap T.ideal T.mult hV.one_le_mult hMC hO
      N H₁ H₂ hsnc₁ hsnc₂ hH₁ hH₂
  have : AlgebraicGeometry.Etale ψ₁ := hψ₁
  have : AlgebraicGeometry.Etale ψ₂ := hψ₂
  have : AlgebraicGeometry.QuasiCompact (ψ₁ ≫ T.structMap) := hqc
  have hcomp₂ : ψ₂ ≫ (T.withBoundary (H₂ :: N)).structMap = ψ₁ ≫ T.structMap := hcompeq.symm
  obtain ⟨hVal₁, hstr₁⟩ :=
    isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hPdown A B hspec T hV hP hO hD
      (by simp [hbd]) V (ψ₁ ≫ T.structMap) ψ₁ hψ₁ hqc rfl hcov₁
  obtain ⟨hVal₂, hstr₂⟩ :=
    isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hPdown A B hspec (T.withBoundary (H₂ :: N)) hV₂
      (by rw [MarkedIdealWithBoundary.withBoundary_dim]; exact hP) (fun x => hO x) (fun h2 => hD h2)
      (by change 0 < (H₂ :: N).length; exact Nat.zero_lt_succ _)
      V (ψ₁ ≫ T.structMap) ψ₂ hψ₂ hqc hcomp₂ hcov₂
  have : AlgebraicGeometry.Smooth (ψ₁ ≫ T.structMap) := hVal₁.smooth
  have : AlgebraicGeometry.LocallyOfFiniteType (ψ₁ ≫ T.structMap) := hftq
  have hbdy : List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₁) T.boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₂) (H₂ :: N) := by
    rw [hbd]
    simp only [List.map_cons]
    rw [hHH, hNN]
  have hTT : T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁
      = (T.withBoundary (H₂ :: N)).pullbackAlong V (ψ₁ ≫ T.structMap) ψ₂ := by
    show MarkedIdealWithBoundary.mk T.base V (ψ₁ ≫ T.structMap) (T.ideal.comap ψ₁) T.mult
        (List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₁) T.boundary)
      = MarkedIdealWithBoundary.mk T.base V (ψ₁ ≫ T.structMap) (T.ideal.comap ψ₂) T.mult
        (List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₂) (H₂ :: N))
    rw [hidl, hbdy]
  have hDeq : (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)).toSequenceOfBlowups
      = (A ((T.withBoundary (H₂ :: N)).pullbackAlong V (ψ₁ ≫ T.structMap) ψ₂)).toSequenceOfBlowups :=
    toSequenceOfBlowups_eq_of_heq _ _ hidl rfl hbdy (congr_arg_heq A hTT)
  rw [← hDeq] at hstr₂
  obtain ⟨c, hc0, hcsucc, hcle⟩ :=
    hin.maxContactChain T.base V (ψ₁ ≫ T.structMap) (T.ideal.comap ψ₁) T.mult hV.one_le_mult
      (List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₁) T.boundary)
      (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁))
      (fun i hi => hin.isLocallyNoetherian_obj (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁) hVal₁
        (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)) i hi)
      (fun i hi J hJ => le_center_of_center_support_subset hin (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)
        (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)) i hi J hJ)
  refine SequenceOfBlowups.isomorphic_of_isStrictPullback_same_source (A T).toSequenceOfBlowups
    (A (T.withBoundary (H₂ :: N))).toSequenceOfBlowups hin.lifting hstr₁ hstr₂ ?_ ?_ ?_ ?_ c ?_ hcsucc hcle
  · intro i hi x hx
    exact hcov₁ (hin.center_mem_coSupport T hV (A T) i hi x hx)
  · intro i hi x hx
    exact hcov₂ (hin.center_mem_coSupport (T.withBoundary (H₂ :: N)) hV₂
      (A (T.withBoundary (H₂ :: N))) i hi x hx)
  · intro i hi J hJ
    exact le_center_of_center_support_subset hin T (A T) i hi J (SetLike.coe_subset_coe.mpr hJ)
  · intro i hi J hJ
    exact le_center_of_center_support_subset hin (T.withBoundary (H₂ :: N)) (A (T.withBoundary (H₂ :: N))) i hi J
      (SetLike.coe_subset_coe.mpr hJ)
  · rw [hc0]
    exact subschemeι_comap_comp_comp_eq _ _ ψ₁ ψ₂ hmax

end DivisorReductionIndependence

end FunctorialResolution.EmbeddedResolution
end

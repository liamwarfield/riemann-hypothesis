module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BalancedDivisorReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PrependedAmbientSequence

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport
namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

theorem support_ker_comp_subset_support_ker {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by
  intro x hx
  exact Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp g f) hx

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem exists_lift_pullback_subschemeι_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    ∃ ψ : Limits.pullback h D.subschemeι ⟶ D'.subscheme,
      ψ ≫ D'.subschemeι = Limits.pullback.fst h D.subschemeι := by
  have hle : D'.subschemeι.ker ≤ (Limits.pullback.fst h D.subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD]
    exact le_rfl
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift D'.subschemeι
      (Limits.pullback.fst h D.subschemeι) hle, by simp⟩

theorem isPullback_subschemeMapOfComap (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h := by
  have hcomm : subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
    subschemeMapOfComap_comp h D D' hD
  obtain ⟨ψ, hψ⟩ := exists_lift_pullback_subschemeι_comap h D D' hD
  have h1 : Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono D'.subschemeι, Category.assoc, hψ, Category.id_comp]
    exact Limits.pullback.lift_fst _ _ _
  have h2 : ψ ≫ Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hψ
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        ← cancel_mono D.subschemeι, Category.assoc, hcomm, ← Category.assoc, hψ]
      exact Limits.pullback.condition
  refine (IsPullback.of_iso_pullback ⟨hcomm.symm⟩
    { hom := Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm
      inv := ψ
      hom_inv_id := h1
      inv_hom_id := h2 } ?_ ?_).flip
  · exact Limits.pullback.lift_fst _ _ _
  · exact Limits.pullback.lift_snd _ _ _

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBaseChangeComparison
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem smooth_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] :
    AlgebraicGeometry.Smooth g := inferInstance

private theorem surjective_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] :
    AlgebraicGeometry.Surjective g := inferInstance

private theorem comap_congr {X W : Scheme.{u}} {a b : W ⟶ X} (h : a = b)
    (I : X.IdealSheafData) : I.comap a = I.comap b := by
  subst h
  rfl

private theorem map_comap_map_comap_eq_map_comap_comp {X Y W : Scheme.{u}} (a : W ⟶ Y) (b : Y ⟶ X)
    (M : List X.IdealSheafData) :
    List.map (fun D : Y.IdealSheafData => D.comap a)
        (List.map (fun D : X.IdealSheafData => D.comap b) M)
      = List.map (fun D : X.IdealSheafData => D.comap (a ≫ b)) M := by
  induction M with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [← Scheme.IdealSheafData.comap_comp, ih]

private theorem map_comap_congr {X W : Scheme.{u}} {a b : W ⟶ X} (h : a = b)
    (M : List X.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap a) M
      = List.map (fun D : X.IdealSheafData => D.comap b) M := by
  subst h
  rfl

private theorem sameNontrivialBoundary_of_eq_right {X : Scheme.{u}} {A B B' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) (hB : B = B') : MarkedIdealWithBoundary.SameNontrivialBoundary A B' :=
  hB ▸ h

private theorem isPullback_subschemeMapOfComap_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] (f : T.base →+* K)
    (Z : (T.baseChange K f).scheme.IdealSheafData)
    (hZ : Z = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f)) :
    IsPullback (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) Z hZ)
      (Z.subschemeι ≫ (T.baseChange K f).structMap)
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (specMapOfFieldHom T.base K f) := by
  have h2 : IsPullback (fieldBaseChangeProjection T K f) ((T.baseChange K f).structMap) T.structMap
      (specMapOfFieldHom T.base K f) := IsPullback.of_hasPullback _ _
  exact (isPullback_subschemeMapOfComap _ _ (fieldBaseChangeProjection T K f)
    (T.boundary.get ⟨j, hj⟩) Z hZ).paste_vert h2

theorem exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (hjE : j < E'.length)
    (hget : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : (T.baseChange K f).scheme.IdealSheafData)
    (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
    (hI₀' : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
    (hE₀' : MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j)))) :
    ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme.IdealSheafData)
      (e : (E'.get ⟨j, hjE⟩).subscheme ⟶ ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme),
      AlgebraicGeometry.Smooth e ∧
      AlgebraicGeometry.Surjective e ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary E'' ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).boundary ∧
      e ≫ CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
            (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
          divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
            (E'.get ⟨j, hjE⟩) hget ∧
      e ≫ (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').structMap =
          (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))
        (List.map (fun D => D.comap e) E'') ∧
      (((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
            ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
            (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.take (E'.length - 1) (E₀'.eraseIdx j)))).IsAdmissible →
          (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').IsAdmissible) ∧
      (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').krullDimSucc =
        ((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
            ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
            (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc := by
  classical
  subst hI₀'
  have hsq : IsPullback
      (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hget)
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
      (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    isPullback_subschemeMapOfComap_comp_structureMorphism T j hj K f (E'.get ⟨j, hjE⟩) hget
  have hQ : IsPullback
      (CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
        (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f))
      (CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
        (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f))
      (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨ee, hfst, hsnd, hinv1, hinv2⟩ :
      ∃ ee : _ ≅ _,
        ee.hom ≫ CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
            subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget ∧
          ee.hom ≫ CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
            (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
          ee.inv ≫ subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget =
            CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) ∧
          ee.inv ≫ ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) =
            CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    ⟨hsq.isoIsPullback _ _ hQ, hsq.isoIsPullback_hom_fst _ _ hQ,
      hsq.isoIsPullback_hom_snd _ _ hQ, hsq.isoIsPullback_inv_fst _ _ hQ,
      hsq.isoIsPullback_inv_snd _ _ hQ⟩
  have hlbc : divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hget
      = subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
          (E'.get ⟨j, hjE⟩) hget := rfl
  have hbe := sameNontrivialBoundary_comap_subschemeι (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
      (E'.get ⟨j, hjE⟩) hget (List.take (T.boundary.length - 1) (E₀.eraseIdx j))
      (List.take (E'.length - 1) (E₀'.eraseIdx j)) hE₀'
  refine ⟨List.map (fun D : (E'.get ⟨j, hjE⟩).subscheme.IdealSheafData => D.comap ee.inv)
      (List.map (fun D : (T.baseChange K f).scheme.IdealSheafData =>
        D.comap (E'.get ⟨j, hjE⟩).subschemeι) (List.take (E'.length - 1) (E₀'.eraseIdx j))),
      ee.hom, ?_, ?_, ?_, hfst.trans hlbc.symm, hsnd, ?_, ?_,
      krullDimSucc_eq_of_iso ee.symm⟩
  · exact smooth_of_isIso ee.hom
  · exact surjective_of_isIso ee.hom
  · exact sameNontrivialBoundary_of_eq_right (MarkedIdealWithBoundary.SameNontrivialBoundary.comap ee.inv hbe)
      (((map_comap_map_comap_eq_map_comap_comp ee.inv (subschemeMapOfComap (fieldBaseChangeProjection T K f)
            (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hget) _).trans
          (map_comap_congr hinv1 _)).trans
        (MarkedIdealWithBoundary.baseChange_boundary (restrictToBoundaryDivisor T j hj I₀ E₀) K f).symm)
  · exact sameNontrivialBoundary_of_eq_right (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
      (((map_comap_map_comap_eq_map_comap_comp ee.hom ee.inv _).trans
          (map_comap_congr ee.hom_inv_id _)).trans (list_map_comap_id _ _)).symm
  · intro hS
    have hval := isAdmissible_comap_of_iso ee.symm
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
      ((I₀.comap (fieldBaseChangeProjection T K f)).comap (E'.get ⟨j, hjE⟩).subschemeι) T.mult
      (List.map (fun D : (T.baseChange K f).scheme.IdealSheafData =>
        D.comap (E'.get ⟨j, hjE⟩).subschemeι) (List.take (E'.length - 1) (E₀'.eraseIdx j))) hS
    have hp : ee.symm.hom ≫ ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
        = ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).structMap := hinv2
    have s1 : (I₀.comap (fieldBaseChangeProjection T K f)).comap (E'.get ⟨j, hjE⟩).subschemeι
        = (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
            (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget) :=
      (comap_subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
        (E'.get ⟨j, hjE⟩) hget I₀).symm
    have hI : ((I₀.comap (fieldBaseChangeProjection T K f)).comap
          (E'.get ⟨j, hjE⟩).subschemeι).comap ee.symm.hom
        = ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).ideal :=
      (congrArg (fun J : (E'.get ⟨j, hjE⟩).subscheme.IdealSheafData => J.comap ee.symm.hom)
          s1).trans
        (((Scheme.IdealSheafData.comap_comp _ ee.symm.hom _).symm.trans
            (comap_congr hinv1 _)).trans
          (MarkedIdealWithBoundary.baseChange_ideal (restrictToBoundaryDivisor T j hj I₀ E₀) K f).symm)
    exact isAdmissible_congr hp hI rfl rfl hval

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem filter_map_eq_of_filter_eq {α : Type*} (p : α → Bool) (g : α → α)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List α}
    (hAB : List.filter p A = List.filter p B) :
    List.filter p (A.map g) = List.filter p (B.map g) := by
  have key : ∀ L : List α,
      List.filter p (L.map g) = List.filter p ((List.filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        have hga : p (g a) = false := hpg a ha'
        simp [ha', hga, ih]
  rw [key A, key B, hAB]

private theorem sameNontrivialBoundary_map {X : Scheme.{u}} (g : X.IdealSheafData → X.IdealSheafData)
    (hg : g ⊤ = ⊤) {A B : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (A.map g) (B.map g) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  unfold MarkedIdealWithBoundary.nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

private theorem sameNontrivialBoundary_take_eraseIdx_strictTransform {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A B : List X.IdealSheafData) (a b : ℕ) (ha : a < A.length) (hb : b < B.length)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (A.eraseIdx a) (B.eraseIdx b)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (A.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) A)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (List.take (B.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤
      = (⊤ : X.IdealSheafData) := by
    show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length →
      List.take (C.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c)
        = List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (List.map (fun D : X.IdealSheafData =>
        Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1 := by
      rw [List.length_map]
      exact List.length_eraseIdx_of_lt hc
    have hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length := by
      intro f
      rw [List.length_map]
      exact hc
    simp only [List.map_map, Function.comp_def]
    rw [List.eraseIdx_append_of_lt_length (hmap _)]
    rw [List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
    hgtop h

theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  rfl

theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
      (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁)) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform
    (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE

theorem boundaryReindexingInvariance : BoundaryReindexingInvariance.{u} :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFieldBaseChange
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isAdmissible_of_withBoundary_isAdmissible
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible)
    (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hV : (T.withBoundary E').IsAdmissible) : T.IsAdmissible := by
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary (T.withBoundary E').boundary T.boundary := hBE.symm
  have h := hvbr (T.withBoundary E') T.boundary hV hBE'
  have he : (T.withBoundary E').withBoundary T.boundary = T := MarkedIdealWithBoundary.withBoundary_self T
  rwa [he] at h

private theorem containedComponentsIdeal_withBoundary_of_get_eq (S : MarkedIdealWithBoundary.{u})
    (E' : List S.scheme.IdealSheafData) (j : ℕ) (hjE : j < E'.length)
    (hj : j < S.boundary.length)
    (hget : E'.get ⟨j, hjE⟩ = S.boundary.get ⟨j, hj⟩) :
    DivisorReduction.containedComponentsIdeal (S.withBoundary E') j hjE = DivisorReduction.containedComponentsIdeal S j hj := by
  rw [DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal (S.withBoundary E') j hjE,
    DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal S j hj]
  exact congrArg (fun D => DivisorReduction.componentsInOrderLocusIdeal S.ideal S.mult D) hget

private theorem lowerIdealWithoutBlowup_eq_ideal (S : MarkedIdealWithBoundary.{u}) :
    DivisorReduction.lowerIdealWithoutBlowup S = S.ideal := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  simp [Scheme.IdealSheafData.comap_id]

theorem containedComponentsIdeal_withBoundary_baseChange
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
        (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
            DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
              (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) := by
  intro T hV K iK iCZ f E' hBE j hj hjE htake hV'
  have hVb : (T.baseChange K f).IsAdmissible :=
    isAdmissible_of_withBoundary_isAdmissible hvbr (T.baseChange K f) E' hBE hV'
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    rw [List.length_take, List.length_take] at h
    omega
  have hget : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  rw [containedComponentsIdeal_withBoundary_of_get_eq (T.baseChange K f) E' j hjE hj' hget]
  exact hfacts.preIdeal_baseChange T hV K f hVb j hj hj'

theorem lowerIdealWithoutBlowup_withBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      DivisorReduction.lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (DivisorReduction.lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f) := by
  intro T K iK iCZ f E'
  rw [lowerIdealWithoutBlowup_eq_ideal, lowerIdealWithoutBlowup_eq_ideal, MarkedIdealWithBoundary.withBoundary_ideal]
  exact MarkedIdealWithBoundary.baseChange_ideal T K f

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem map_comap_id {W : Scheme.{u}} (l : List W.IdealSheafData) :
    List.map (fun D : W.IdealSheafData => D.comap (𝟙 W)) l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

private theorem take_eraseIdx_append_singleton {α : Type*} (A : List α) (e : α) (j n : ℕ)
    (hj : j < A.length) (hn : n = A.length - 1) :
    List.take n ((A ++ [e]).eraseIdx j) = A.eraseIdx j := by
  subst hn
  have hlen : (A.eraseIdx j).length = A.length - 1 := by
    rw [List.length_eraseIdx, if_pos hj]
  rw [List.eraseIdx_append_of_lt_length hj, ← hlen, List.take_left]

private theorem take_length_sub_one_eraseIdx {α : Type*} (A : List α) (j n : ℕ) (hj : j < A.length)
    (hn : n = A.length - 1) : List.take n (A.eraseIdx j) = A.eraseIdx j := by
  subst hn
  refine List.take_of_length_le ?_
  rw [List.length_eraseIdx, if_pos hj]

private theorem top_pow {Y : Scheme.{u}} (m : ℕ) :
    (⊤ : Y.IdealSheafData) ^ m = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

private theorem residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A F : X.IdealSheafData) (F' : Y.IdealSheafData) (m : ℕ) (hF' : F' = F.comap g)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor F') (hex : ∃ B : X.IdealSheafData, F ^ m * B = A) :
    residualByPow (A.comap g) F' m = (residualByPow A F m).comap g := by
  have hdown : F ^ m * residualByPow A F m = A := pow_mul_residualByPow A F m hex
  have hup : F' ^ m * (residualByPow A F m).comap g = A.comap g := by
    rw [hF', ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hdown]
  have hup2 : F' ^ m * residualByPow (A.comap g) F' m = A.comap g :=
    pow_mul_residualByPow (A.comap g) F' m ⟨_, hup⟩
  exact (hcart.pow m).eq_of_mul_eq_mul (hup2.trans hup.symm)

private theorem sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hX : AlgebraicGeometry.IsNoetherian X) (hY : AlgebraicGeometry.IsNoetherian Y)
    (hflat : AlgebraicGeometry.Flat g)
    (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (Z' : Y.IdealSheafData) (hZ' : Z' = Z.comap g)
    (B : List X.IdealSheafData) (E : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap g) B) E)
    (j : ℕ) (hj : j < B.length) (hjE : j < E.length)
    (htake : List.take (j + 1) E = List.take (j + 1) (List.map (fun D => D.comap g) B)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 Y) Z') (List.map (fun D => D.comap (𝟙 Y)) E)
          ++ [Blowup.exceptionalIdeal (𝟙 Y) Z']).eraseIdx j))
      (List.map (fun D => D.comap g)
        (List.take (B.length - 1)
          ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
            ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx j))) := by
  have := hX
  have := hY
  have := hflat
  subst hZ'
  have hst : ∀ D : X.IdealSheafData,
      (Blowup.strictTransform (𝟙 X) Z D).comap g
        = Blowup.strictTransform (𝟙 Y) (Z.comap g) (D.comap g) := fun D =>
    comap_strictTransform_of_flat_of_isLocallyNoetherian (𝟙 X) g (𝟙 Y) g
      (CategoryTheory.IsPullback.id_vert g) Z D hZ
  have hcomp : List.map ((fun D : X.IdealSheafData => D.comap g)
        ∘ Blowup.strictTransform (𝟙 X) Z) B
      = List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
          (List.map (fun D : X.IdealSheafData => D.comap g) B) := by
    rw [List.map_map]
    exact List.map_congr_left (fun D _ => hst D)
  rw [map_comap_id, map_comap_id,
    take_eraseIdx_append_singleton (List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g)) E)
      (Blowup.exceptionalIdeal (𝟙 Y) (Z.comap g)) j (E.length - 1) (by simpa using hjE) (by simp),
    take_eraseIdx_append_singleton (List.map (Blowup.strictTransform (𝟙 X) Z) B)
      (Blowup.exceptionalIdeal (𝟙 X) Z) j (B.length - 1) (by simpa using hj) (by simp),
    ← List.eraseIdx_map, List.map_map, hcomp]
  refine ((MarkedIdealWithBoundary.SameNontrivialBoundary.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
    (strictTransform_top (𝟙 Y) (Z.comap g)) hBE).eraseIdx j ?_).symm
  rw [← List.map_take, ← List.map_take, ← List.map_take, htake, List.map_take]

theorem lowerIdealAfterBlowup_pullbackAlong_of_smooth
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (lowerIdealAfterBlowup T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hOx : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).1 hO
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hOx j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) := by
    have hb := hblow ((T.pullbackAlong Y q h).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor h T.ideal (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              MarkedIdealWithBoundary.SameNontrivialBoundary
                (List.take (E'.length - 1)
                  ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
                (List.map (fun D => D.comap h)
                  (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hsmooth : AlgebraicGeometry.Smooth h := hsm
  have hbdry : (T.pullbackAlong Y q h).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat h hV.isNoetherian hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) hpre
    T.boundary E' hBE j hj hjE htake

theorem comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (_hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    (lowerIdealAfterBlowup T j hj).comap h = (lowerIdealWithoutBlowup T).comap h := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hdown : containedComponentsIdeal T j hj ^ T.mult * residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult = T.ideal :=
    pow_mul_residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult hex
  have hup := congrArg (fun I : T.scheme.IdealSheafData => I.comap h) hdown
  simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, htop,
    top_pow, Scheme.IdealSheafData.top_mul] at hup
  simp only [lowerIdealAfterBlowup, lowerIdealWithoutBlowup, Blowup.exceptionalIdeal_eq_comap,
    Scheme.IdealSheafData.comap_id]
  exact hup

theorem comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (_hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  have hnoT : AlgebraicGeometry.IsNoetherian T.scheme := hV.isNoetherian
  have hstT : ∀ D : T.scheme.IdealSheafData,
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj) D).comap h = D.comap h := by
    intro D
    have hg : ((containedComponentsIdeal T j hj).comap (𝟙 T.scheme)).comap h = ⊤ := by
      rw [Scheme.IdealSheafData.comap_id]; exact htop
    have h2 := strictTransform_comap_of_comap_center_eq_top (𝟙 T.scheme) (containedComponentsIdeal T j hj) D h hg
    rw [h2, Scheme.IdealSheafData.comap_id]
  have hR0 : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
          (List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary)
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := rfl
  have hR : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := by
    rw [hR0, map_comap_id]
  have key : List.map (fun D : T.scheme.IdealSheafData => D.comap h)
        ((List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j)
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) (T.boundary.eraseIdx j) := by
    rw [← List.eraseIdx_map, ← List.eraseIdx_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun D _ => hstT D)
  rw [hR, lowerBoundaryWithoutBlowup_eq T,
    take_eraseIdx_append_singleton
      (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary)
      (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) j (T.boundary.length - 1)
      (by simpa using hj) (by simp),
    take_length_sub_one_eraseIdx T.boundary j (T.boundary.length - 1) hj rfl, key]
  exact MonomialCenter.sameNontrivialBoundary_refl _

theorem lowerIdealAfterBlowup_fieldBaseChange
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.baseChange K f).boundary)
    (hjE : j < E'.length)
    (_htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hpre : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)) :
    lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE =
      (lowerIdealAfterBlowup T j hj).comap (fieldBaseChangeProjection T K f) := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) := by
    have hb := hblow ((T.baseChange K f).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor (fieldBaseChangeProjection T K f) T.ideal
      (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_fieldBaseChange
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.baseChange K f).boundary)
    (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hpre : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  have hbdry : (T.baseChange K f).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap (fieldBaseChangeProjection T K f))
          T.boundary := MarkedIdealWithBoundary.baseChange_boundary T K f
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat (fieldBaseChangeProjection T K f) hV.isNoetherian
    hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) hpre
    T.boundary E' hBE.symm j hj hjE htake

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusFieldBaseChange
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI : CharZero T.base := hV.charZero
  haveI : CharZero K := (RingHom.charZero_iff f.injective).mp hV.charZero
  haveI : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m

end FunctorialResolution.EmbeddedResolution
end

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ B : T.scheme.IdealSheafData, B * DivisorReduction.containedComponentsIdeal T j hj ^ T.mult = T.ideal := by
  intro T hV _ j hj
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  exact ⟨J, by rw [mul_comm]; exact hJ⟩

private theorem orderAtComapOffExceptionalLocus : OrderAtComapOffExceptionalLocus.{u} := by
  delta OrderAtComapOffExceptionalLocus
  exact fun T hT X' π Z hπ x' hx' A =>
    orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A

private theorem smoothPullbackCompatibility_of_divisorReductionTermination (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) :
    DivisorReduction.SmoothPullbackCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact comap_ne_top_of_surjective
  · intro T hV Y q h inst hq m
    exact DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq m
  · exact DivisorReduction.isPullback_subschemeMapOfComap
  · exact DivisorReduction.smooth_of_isPullback
  · exact DivisorReduction.lowerIdealAfterBlowup_pullbackAlong_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.containedComponentsIdeal_pullbackAlong_of_smooth hfacts

private theorem fieldBaseChangeCompatibility_of_divisorReductionTermination (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) :
    FieldBaseChangeCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hV K inst f E' m
    exact orderAtLeastLocus_withBoundary_baseChange_eq_preimage T hV K f E' m
  · exact flat_fieldBaseChangeProjection
  · exact surjective_fieldBaseChangeProjection
  · exact containedComponentsIdeal_withBoundary_baseChange hfacts MarkedIdealWithBoundary.validOfSameNontrivialBoundary

private theorem divisorRestrictionFieldBaseChange : DivisorReduction.DivisorRestrictionFieldBaseChange.{u} := by
  refine ⟨comap_comap, comap_fieldBaseChangeProjection_ne_top, ?_, ?_, ?_, ?_, ?_⟩
  · intro T j hj K inst1 inst2 f E' hjE hD I₀ E₀ I₀' E₀' hI hE
    obtain ⟨E'', e, hs, hsu, h1, h2, h3, h4, h5, h6⟩ :=
      DivisorReduction.exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange T j hj K f E' hjE hD I₀ E₀ I₀' E₀' hI hE
    exact ⟨E'', e, hs, hsu, h1.symm, h2, h3, h4, h5, h6⟩
  · intro T K inst1 inst2 f E'
    exact lowerIdealWithoutBlowup_withBoundary_baseChange T K f E'
  · intro T j hj K inst1 inst2 f E' hBE htake hjE
    exact DivisorReduction.lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary T j hj K f E' hBE htake hjE
  · intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
    exact DivisorReduction.lowerIdealAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV
      hO j hj K f E' hBE.symm hjE htake hV' hpre
  · intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
    exact DivisorReduction.lowerBoundaryAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO
      j hj K f E' hBE.symm hjE htake hV' hpre

private theorem emptyPulledBackCenterCompatibility : DivisorReduction.EmptyPulledBackCenterCompatibility.{u} := by
  refine ⟨?_, ?_⟩
  · intro T hV hO j hj Y h htop
    exact DivisorReduction.comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO j hj Y h htop
  · intro T hV j hj Y h htop
    exact DivisorReduction.comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj Y h htop

private theorem pushedBlowupSequenceProperties_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    PushedBlowupSequenceProperties hres blowupPreservesNoetherian := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV j hj
    exact DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
      (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)
  · intro T inst j hj s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero hres blowupPreservesNoetherian T j hj s hpr hmk
  · intro T inst j hj hb s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres blowupPreservesNoetherian T j hj hb s hpr
      hmk
  · intro T hV j hj S
    exact DivisorReduction.isSmoothDivisor_boundary_comap_isoObjZero T hV j hj S
  · intro T inst j hj s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus hres blowupPreservesNoetherian T j hj s hpr
      hmk t ht
  · intro T inst j hj hb s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus_succ hres blowupPreservesNoetherian T j hj hb s
      hpr hmk t ht
  · intro T hV
    exact DivisorReduction.one_le_mult_of_isAdmissible T hV
  · intro T hV hOB hbal j hj hpre hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top hres blowupPreservesNoetherian T hV
      hOB hbal j hj hpre hlow s hpr hmk t ht
  · intro T hV hOB hbal j hj hne hb hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient hres blowupPreservesNoetherian
      orderAtComapOffExceptionalLocus T hV hOB j hj hb hlow s hpr hmk
      (fun t _ => DivisorReduction.embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres
        blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
        (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t) t ht
  · intro T inst j hj s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_ambientMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk t
  · intro T inst j hj hb s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_prependedAmbientSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk t
  · intro X Y f inst I
    exact support_ker_comp_subset_support_ker I.subschemeι f
  · intro T hV j hj
    exact DivisorReduction.support_containedComponentsIdeal_subset_support_boundary T j hj

private theorem divisorReductionStepProperties_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    DivisorReductionStepProperties hres blowupPreservesNoetherian :=
  (divisorReductionProperties_of_blowupPreservesNoetherian hres blowupPreservesNoetherian).toDivisorReductionStepProperties

theorem divisorReductionHypotheses_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    DivisorReduction.DivisorReductionHypotheses hres := by
  have hstepProps := divisorReductionStepProperties_canonicalAlgorithmRules hres
  have hfacts := hstepProps.toDivisorReductionTerminationProperties
  refine
    { trivial_of_coSupport_empty := ?_
      baseChange := smoothPullbackCompatibility_of_divisorReductionTermination hres hfacts
      smoothImpliesFlat := ⟨fun X Y f hf => by have := hf; infer_instance⟩
      degenerateTransversal := emptyPulledBackCenterCompatibility
      fieldBaseChangeCompatibility := fieldBaseChangeCompatibility_of_divisorReductionTermination hres hfacts
      boundaryReindexingInvariance := DivisorReduction.boundaryReindexingInvariance
      fieldLower := divisorRestrictionFieldBaseChange
      divisorReduction := hstepProps
      pushedBlowupSequenceProperties := pushedBlowupSequenceProperties_canonicalAlgorithmRules hres }
  intro L j T hV hj Y q h inst hq E' hV' hne hempty B' hB'
  exact DivisorReductionEmptyOrderLocus.divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty hres L j T hV hj Y q h hq E' hV'
    hne hempty B' hB'

end FunctorialResolution.EmbeddedResolution

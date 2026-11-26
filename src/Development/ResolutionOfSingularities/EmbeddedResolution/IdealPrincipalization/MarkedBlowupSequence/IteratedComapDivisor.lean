module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothDivisorEtaleChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.SmoothDivisorOperations
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem restrictIdeal_mul {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (I * J) U = restrictIdeal I U * restrictIdeal J U :=
  Scheme.IdealSheafData.comap_mul I J U.ι

theorem etaleChart_comap_map_comp_affineSpaceFinToSpec {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U) :
    (π.resLE U V hV ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ (π ≫ p) := by
  have h1 : π.resLE U V hV ≫ U.ι = V.ι ≫ π := by simp
  rw [Category.assoc, c.comp_struct, ← Category.assoc, h1, Category.assoc]

theorem etale_etaleChart_comap_map {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) :
    AlgebraicGeometry.Etale (π.resLE U V hV ≫ c.map) := by
  have := he
  have := c.isEtale
  infer_instance

def EtaleChart.comap {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) : EtaleChart (π ≫ p) V m where
  map := π.resLE U V hV ≫ c.map
  comp_struct := etaleChart_comap_map_comp_affineSpaceFinToSpec p π c V hV
  isEtale := etale_etaleChart_comap_map p π c V hV he

theorem EtaleChart.comap_map {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) :
    (EtaleChart.comap p π c V hV he).map = π.resLE U V hV ≫ c.map := rfl

theorem EtaleChart.comap_coordIdeal {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : AlgebraicGeometry.Etale (π.resLE U V hV)) (S : Finset (Fin m)) :
    (EtaleChart.comap p π c V hV he).coordIdeal S =
      (c.coordIdeal S).comap (π.resLE U V hV) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.comap_map,
    Scheme.IdealSheafData.comap_comp]

theorem isSmoothDivisor_mul_of_disjoint_support {X : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (A B : X.IdealSheafData) (hA : IsSmoothDivisor p A) (hB : IsSmoothDivisor p B)
    (hAB : Disjoint (A.support : Set X) (B.support : Set X)) :
    IsSmoothDivisor p (A * B) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) (A * B) ?_
  intro x
  by_cases hxA : x ∈ A.support
  · have hxB : x ∉ B.support := fun h => Set.disjoint_left.mp hAB hxA h
    obtain ⟨U, m, c, j, hxU, hAU⟩ :=
      exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p A hA x hxA
    refine ⟨U ⊓ B.support.compl, ⟨hxU, hxB⟩, m, c.restrict inf_le_left, Or.inr ⟨j, ?_⟩⟩
    have hBtop : restrictIdeal B (U ⊓ B.support.compl) = ⊤ := by
      refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
      intro y hy
      exact hy.2
    have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ B.support.compl)
      inf_le_left c A {j} hAU
    rw [restrictIdeal_mul, hBtop, Scheme.IdealSheafData.mul_top, hc]
  · by_cases hxB : x ∈ B.support
    · obtain ⟨U, m, c, j, hxU, hBU⟩ :=
        exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB x hxB
      refine ⟨U ⊓ A.support.compl, ⟨hxU, hxA⟩, m, c.restrict inf_le_left, Or.inr ⟨j, ?_⟩⟩
      have hAtop : restrictIdeal A (U ⊓ A.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.2
      have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ A.support.compl)
        inf_le_left c B {j} hBU
      rw [restrictIdeal_mul, hAtop, Scheme.IdealSheafData.top_mul, hc]
    · obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
        exists_etaleChart_le p x (A.support.compl ⊓ B.support.compl) ⟨hxA, hxB⟩
      refine ⟨U, hxU, m, c, Or.inl ?_⟩
      have hAtopW : restrictIdeal A (A.support.compl ⊓ B.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.1
      have hBtopW : restrictIdeal B (A.support.compl ⊓ B.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.2
      have hAtop : restrictIdeal A U = ⊤ := restrictIdeal_eq_top_of_le A hUW hAtopW
      have hBtop : restrictIdeal B U = ⊤ := restrictIdeal_eq_top_of_le B hUW hBtopW
      rw [restrictIdeal_mul, hAtop, hBtop, Scheme.IdealSheafData.mul_top]

private theorem restrictIdeal_comap_eq_top_of_notMem_support {X X' : Scheme.{u}} (π : X' ⟶ X)
    (B : X.IdealSheafData) (V : X'.Opens) (hV : ∀ y : X', y ∈ V → π.base y ∉ B.support) :
    restrictIdeal (B.comap π) V = ⊤ := by
  have hcc : B.comap (V.ι ≫ π) = (B.comap π).comap V.ι := by
    rw [Scheme.IdealSheafData.comap_comp]
  have htop : B.comap (V.ι ≫ π) = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support (V.ι ≫ π) B ?_
    intro y
    have hy : V.ι.base y ∈ Set.range V.ι.base := Set.mem_range_self y
    rw [Scheme.Opens.range_ι] at hy
    have h2 : π.base (V.ι.base y) ∉ B.support := hV _ hy
    simpa using h2
  rw [restrictIdeal_eq_comap_ι, ← hcc]
  exact htop

theorem isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X' ⟶ X) [AlgebraicGeometry.Smooth (π ≫ p)] (Z B : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hB : IsSmoothDivisor p B)
    (hdisj : Disjoint (Z.support : Set X) (B.support : Set X)) :
    IsSmoothDivisor (π ≫ p) (B.comap π) := by
  refine isSmoothDivisor_of_locally_coordIdeal (B.comap π) ?_
  intro x'
  by_cases hx : π.base x' ∈ B.support
  · obtain ⟨U, m, c, j, hxU, hBU⟩ :=
      exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB (π.base x') hx
    have hxZ : π.base x' ∉ Z.support := fun hZ => (Set.disjoint_left.mp hdisj hZ) hx
    have hWle : (U ⊓ Z.support.compl : X.Opens) ≤ U := inf_le_left
    have hWsup : ∀ y : X, y ∈ (U ⊓ Z.support.compl : X.Opens) → y ∉ Z.support :=
      fun y hy => hy.2
    have hiso : IsIso (π ∣_ (U ⊓ Z.support.compl : X.Opens)) :=
      isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (U ⊓ Z.support.compl : X.Opens) hWsup
    have hiso2 : IsIso (π.resLE (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact hiso
    have he : AlgebraicGeometry.Etale (π.resLE (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl) := inferInstance
    have hxV : x' ∈ (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) := ⟨hxU, hxZ⟩
    refine ⟨π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens), hxV, m,
      EtaleChart.comap p π (c.restrict hWle)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl he, Or.inr ⟨j, ?_⟩⟩
    rw [EtaleChart.comap_coordIdeal,
      restrictIdeal_comap_eq_comap_resLE_restrictIdeal π B (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl,
      restrictIdeal_eq_restrict_coordIdeal_of_le hWle c B {j} hBU]
  · obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
      exists_etaleChart_le (π ≫ p) x' (π ⁻¹ᵁ B.support.compl) hx
    refine ⟨U, hxU, m, c, Or.inl ?_⟩
    refine restrictIdeal_comap_eq_top_of_notMem_support π B U ?_
    intro y hy
    have hy' : y ∈ π ⁻¹ᵁ B.support.compl := hUW hy
    exact hy'

theorem strictTransform_mul_of_disjoint_support {X X' : Scheme.{u}} [IsLocallyNoetherian X']
    (π : X' ⟶ X) (Z A B : X.IdealSheafData)
    (hBZ : Disjoint (B.support : Set X) (Z.support : Set X)) :
    Blowup.strictTransform π Z (A * B) = Blowup.strictTransform π Z A * B.comap π := by
  have hqAB : QuasiCompact (strictTransformι π Z (A * B)) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z (A * B)
  have hqA : QuasiCompact (strictTransformι π Z A) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z A
  refine eq_of_locally_restrictIdeal_eq _ _ ?_
  intro x
  by_cases hx : π.base x ∈ Z.support
  · have hxB : π.base x ∉ B.support := fun hB => (Set.disjoint_left.mp hBZ hB) hx
    refine ⟨π ⁻¹ᵁ B.support.compl, ?_, ?_⟩
    · exact hxB
    · have hVmem : ∀ y : X', y ∈ π ⁻¹ᵁ B.support.compl → π.base y ∉ B.support := by
        intro y hy
        exact hy
      have hBtop : restrictIdeal (B.comap π) (π ⁻¹ᵁ B.support.compl) = ⊤ :=
        restrictIdeal_comap_eq_top_of_notMem_support π B _ hVmem
      have hcomapB : B.comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π) = ⊤ := by
        rw [Scheme.IdealSheafData.comap_comp]
        exact hBtop
      have hD : (A * B).comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π)
          = A.comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π) := by
        rw [Scheme.IdealSheafData.comap_mul, hcomapB, Scheme.IdealSheafData.mul_top]
      rw [restrictIdeal_mul, hBtop, Scheme.IdealSheafData.mul_top,
        restrictIdeal_strictTransform π Z (A * B) (π ⁻¹ᵁ B.support.compl),
        restrictIdeal_strictTransform π Z A (π ⁻¹ᵁ B.support.compl)]
      exact strictTransform_eq_of_comap_eq _ _ Z (A * B) Z A rfl hD
  · refine ⟨π ⁻¹ᵁ Z.support.compl, ?_, ?_⟩
    · exact hx
    · have hVmem : ∀ y : X', y ∈ π ⁻¹ᵁ Z.support.compl → π.base y ∉ Z.support := by
        intro y hy
        exact hy
      rw [restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z (A * B) _ hVmem,
        Scheme.IdealSheafData.comap_mul, restrictIdeal_mul, restrictIdeal_mul,
        restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z A _ hVmem]

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace TransportedDivisor

def iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData) (t : ℕ) :
    (d.obj t).IdealSheafData :=
  Nat.rec (motive := fun n => (d.obj n).IdealSheafData) B
    (fun n ih => ih.comap (d.map n)) t

@[simp]
theorem iteratedComap_zero {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData) :
    iteratedComap d B 0 = B := rfl

@[simp]
theorem iteratedComap_succ {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData)
    (t : ℕ) : iteratedComap d B (t + 1) = (iteratedComap d B t).comap (d.map t) := rfl

theorem support_strictTransform_subset_preimage {Y Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    (π : Y' ⟶ Y) (Z D : Y.IdealSheafData) :
    ((Blowup.strictTransform π Z D).support : Set Y') ⊆ ⇑π.base ⁻¹' (D.support : Set Y) := by
  have hpre : (((D.comap π).support : Closeds Y') : Set Y') =
      ⇑π.base ⁻¹' (D.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hclosed : IsClosed (((D.comap π).support : Closeds Y') : Set Y') :=
    (D.comap π).support.2
  rw [support_strictTransform_eq_closure_sdiff π Z D, ← hpre]
  exact closure_minimal Set.sdiff_subset hclosed

theorem isSmoothDivisor_iteratedComap {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hsm : ∀ t, t ≤ L → AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p))
    (B₀ : (d.obj 0).IdealSheafData)
    (hB₀ : IsSmoothDivisor (BlowupSequenceData.projectionToBase d 0 ≫ p) B₀)
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (iteratedComap d B₀ t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact hB₀
  | succ n ih =>
    intro hn
    have hlt : n < L := Nat.lt_of_succ_le hn
    have hle : n ≤ L := le_of_lt hlt
    have hs1 : AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d n ≫ p) := hsm n hle
    have heq : BlowupSequenceData.projectionToBase d (n + 1) ≫ p = d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p := by
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
    have hs2 : AlgebraicGeometry.Smooth (d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p) := by
      rw [← heq]
      exact hsm (n + 1) hn
    have hblow : Blowup.IsBlowupAlongIdealSheaf (d.map n) (d.center n) := d.isBlowup n (lt_of_lt_of_le hlt hL)
    have key := isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf (BlowupSequenceData.projectionToBase d n ≫ p) (d.map n)
      (d.center n) (iteratedComap d B₀ n) hblow (ih hle) (hcent n hlt)
    rw [iteratedComap_succ, heq]
    exact key

theorem strictTransform_eq_mul_iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (L : ℕ)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (K A : ∀ t : ℕ, (d.obj t).IdealSheafData) (B₀ : (d.obj 0).IdealSheafData)
    (hK0 : K 0 = A 0 * B₀)
    (hdisj0 : Disjoint ((A 0).support : Set (d.obj 0)) ((B₀).support : Set (d.obj 0)))
    (hKsucc : ∀ t, t < L → K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L →
      K t = A t * iteratedComap d B₀ t ∧
        Disjoint ((A t).support : Set (d.obj t))
          ((iteratedComap d B₀ t).support : Set (d.obj t)) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨hK0, hdisj0⟩
  | succ n ih =>
    intro hn
    have hlt : n < L := Nat.lt_of_succ_le hn
    have hle : n ≤ L := le_of_lt hlt
    obtain ⟨hKn, hdn⟩ := ih hle
    have hnoe : IsLocallyNoetherian (d.obj (n + 1)) := hnoeth (n + 1) hn
    have hmul : K (n + 1) = A (n + 1) * iteratedComap d B₀ (n + 1) := by
      rw [hKsucc n hlt, hKn, strictTransform_mul_of_disjoint_support (d.map n) (d.center n)
        (A n) (iteratedComap d B₀ n) (hcent n hlt).symm, hAsucc n hlt, iteratedComap_succ]
    refine ⟨hmul, ?_⟩
    have hsub : ((A (n + 1)).support : Set (d.obj (n + 1))) ⊆
        ⇑(d.map n).base ⁻¹' ((A n).support : Set (d.obj n)) := by
      rw [hAsucc n hlt]
      exact support_strictTransform_subset_preimage (d.map n) (d.center n) (A n)
    have hpre : ((((iteratedComap d B₀ n).comap (d.map n)).support : Closeds (d.obj (n + 1))) :
          Set (d.obj (n + 1))) =
        ⇑(d.map n).base ⁻¹' ((iteratedComap d B₀ n).support : Set (d.obj n)) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    rw [iteratedComap_succ, hpre]
    rw [Set.disjoint_left] at hdn ⊢
    intro x hx hx'
    exact hdn (hsub hx) hx'

theorem isSmoothDivisor_strictTransform_of_disjoint_center {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (hsm : ∀ t, t ≤ L → AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p))
    (K A : ∀ t : ℕ, (d.obj t).IdealSheafData) (B₀ : (d.obj 0).IdealSheafData)
    (hK0 : K 0 = A 0 * B₀)
    (hdisj0 : Disjoint ((A 0).support : Set (d.obj 0)) ((B₀).support : Set (d.obj 0)))
    (hKsucc : ∀ t, t < L → K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (A t))
    (hB₀ : IsSmoothDivisor (BlowupSequenceData.projectionToBase d 0 ≫ p) B₀)
    (hA : ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (K t) := by
  intro t ht
  have hst : AlgebraicGeometry.Smooth (BlowupSequenceData.projectionToBase d t ≫ p) := hsm t ht
  have hfac := strictTransform_eq_mul_iteratedComap d L hnoeth K A B₀ hK0 hdisj0 hKsucc hAsucc hcent t ht
  have hB := isSmoothDivisor_iteratedComap p d L hL hsm B₀ hB₀ hcent t ht
  rw [hfac.1]
  exact isSmoothDivisor_mul_of_disjoint_support (BlowupSequenceData.projectionToBase d t ≫ p) (A t)
    (iteratedComap d B₀ t) (hA t ht) hB hfac.2

end TransportedDivisor

end FunctorialResolution.EmbeddedResolution

end

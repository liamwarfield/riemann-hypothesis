module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplication
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnitDescent

theorem one_left_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f =
      f ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  erw [Functor.obj.η_def]
  have hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T := by
    simpa using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
  have hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S := by
    simpa using Over.w (toUnit (Over.mk (𝟙 S)))
  have hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
    simpa using this
  have hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  simp only [Over.comp_left, Category.assoc] at hw ⊢
  rw [hm, hc, hb]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp

theorem unit_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI := N.isOpen
  have hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S := by
    simpa using Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  let x₀ := IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr
  have hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left := IsOpenImmersion.lift_fac _ _ _
  have hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S := by
    rw [← N.u_over, ← Category.assoc, hx₀u, hone_w]
  let h := x₀ ≫ pullback.fst N.U.hom π
  have hh : h ≫ N.U.hom = π := by
    simp only [h, Category.assoc, pullback.condition]
    rw [← Category.assoc, hx₀s]
    simp
  obtain ⟨φ, hmon, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hSA N hL
  let x := (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left
  have hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')
  have hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  have hφ1 : x ≫ φ.hom.left =
      (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
    rw [← Over.comp_left]
    congr 1
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h)
      (x ≫ pullback.fst G'.hom (pullback.fst π π)) := by
    rw [reassoc_of% hxs, hxf]
    exact ⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id],
      by rw [Category.assoc, hx₀u]⟩
  obtain ⟨y₀, hy1, -, hy3⟩ := hφ _ _ x hprem
  rw [← Category.assoc, hφ1, one_left_pullback] at hy3
  have hy : y₀ = pullback.snd π π ≫ x₀ := by
    rw [← cancel_mono N.u, hy3, Category.assoc, hx₀u]
  have heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h := by
    rw [← hy1, hy, Category.assoc]
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq
  obtain ⟨e₁, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π
    pullback.condition
  refine ⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩
  rw [huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]),
    huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]

end GlobalTheory.UnitDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitSection_near_closedFibre_descends_to_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  first | exact @GlobalTheory.UnitDescent.unit_descends | exact GlobalTheory.UnitDescent.unit_descends | (intros; apply GlobalTheory.UnitDescent.unit_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoveNear

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π G' _ _ _ N e he hPt Ω _ s g hT hs
  haveI := N.isOpen
  haveI := hR.1
  let xR := s ≫ π
  let UΩ := pullback N.U.hom xR
  let T := pullback G'.hom s
  let m : UΩ ⟶ pullback N.U.hom π := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [Category.assoc]; exact pullback.condition)
  let k : UΩ ⟶ T := pullback.lift (m ≫ N.u) (pullback.snd _ _)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd])
  have sqP : IsPullback m (pullback.snd N.U.hom xR) (pullback.snd N.U.hom π) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback N.U.hom π)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback N.U.hom xR
  have sqk : IsPullback m k N.u (pullback.fst G'.hom s) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G'.hom s) (v₂₂ := G'.hom) (h₃₁ := s) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback G'.hom s)
    rw [pullback.lift_snd, N.u_over]
    exact sqP
  have hk : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqk N.isOpen
  let TO : Over S := Over.mk (pullback.snd G'.hom s ≫ s)
  let yT : TO ⟶ G' := Over.homMk (pullback.fst G'.hom s) pullback.condition
  let qT : TO ⟶ Over.mk s := Over.homMk (pullback.snd G'.hom s) rfl
  let zT : TO ⟶ G' := (qT ≫ g) * yT
  let UO : Over S := Over.mk (pullback.snd N.U.hom xR ≫ s)
  let kO : UO ⟶ TO := Over.homMk k (by
    change k ≫ pullback.snd _ _ ≫ s = _
    rw [pullback.lift_snd_assoc]
    rfl)
  have sec : ∀ h : Over.mk s ⟶ G', ∃ σ : Over.mk s ⟶ TO, σ ≫ yT = h ∧ σ ≫ qT = 𝟙 _ := fun h =>
    ⟨Over.homMk (pullback.lift h.left (𝟙 _) ((Over.w h).trans (Category.id_comp _).symm))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd G'.hom s ≫ s = s
        rw [pullback.lift_snd_assoc]
        exact Category.id_comp _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  have hone : ∀ p, (1 : Over.mk s ⟶ G').left p ∈ Set.range N.u := by
    obtain ⟨x₀, -, -, hx₀⟩ := hPt
    have e₁ : (1 : Over.mk s ⟶ G').left = s ≫ (1 : Over.mk (𝟙 S) ⟶ G').left := congrArg (fun f => f.left)
      (MonObj.comp_one (M := G') (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))).symm
    intro p
    rw [e₁, ← hx₀]
    exact ⟨x₀ (s p), rfl⟩
  have hoU : IsOpen (Set.range N.u) := N.u.isOpenEmbedding.isOpen_range
  obtain ⟨σ₁, h₁, -⟩ := sec 1
  obtain ⟨σ₂, h₂, h₂'⟩ := sec g⁻¹
  have e₂ : σ₂ ≫ zT = 1 := by
    rw [MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]
  have : IrreducibleSpace T := hT
  obtain ⟨t, ⟨p₀, hp₀⟩, ht⟩ := nonempty_preirreducible_inter (hoU.preimage (pullback.fst G'.hom s).continuous)
    (hoU.preimage zT.left.continuous)
    ⟨σ₁.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← h₁] at this
      exact this⟩
    ⟨σ₂.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← e₂] at this
      exact this⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback sqk p₀ t hp₀
  let O : UΩ.Opens := ⟨(kO ≫ zT).left ⁻¹' Set.range N.u, hoU.preimage (kO ≫ zT).left.continuous⟩
  have hwO : w ∈ O := by
    show (kO ≫ zT).left w ∈ Set.range N.u
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change zT.left (k w) ∈ Set.range N.u
    rw [hw]; exact ht
  have hirr : IrreducibleSpace UΩ := by
    refine (irreducibleSpace_def _).2 ⟨⟨w, trivial⟩, ?_⟩
    have := (IrreducibleSpace.isIrreducible_univ T).2.preimage k.isOpenEmbedding
    simpa using this
  obtain ⟨a, aΩ, ha, haf, has, hao⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR.2.2.2 N.U N.smooth e he Ω xR hs hirr O ⟨w, hwO⟩
  let x : Over.mk (𝟙 S) ⟶ G' := Over.homMk
    (pullback.lift (π ≫ a) (𝟙 S) (by rw [Category.assoc, ha, Category.comp_id]; exact (Category.id_comp π).symm) ≫ N.u)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
  refine ⟨a, x, ha, ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ?_⟩
  let rO : Over.mk s ⟶ UO := Over.homMk aΩ (by
    change aΩ ≫ pullback.snd _ _ ≫ s = s
    rw [← Category.assoc, has, Category.id_comp])
  have hq : rO ≫ kO ≫ qT = 𝟙 _ := by
    ext
    change aΩ ≫ k ≫ pullback.snd _ _ = 𝟙 _
    rw [pullback.lift_snd, has]
  have hy : rO ≫ kO ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
    ext
    change aΩ ≫ k ≫ pullback.fst _ _ = s ≫ pullback.lift (π ≫ a) (𝟙 S) _ ≫ N.u
    rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      show aΩ ≫ pullback.lift (pullback.fst N.U.hom xR) _ _ ≫ pullback.fst N.U.hom π = s ≫ π ≫ a
      rw [pullback.lift_fst, haf]
      simp only [xR, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, has,
        Category.id_comp, Category.comp_id]
  have hz : g * ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x) = rO ≫ kO ≫ zT := by
    have hq' : (rO ≫ kO) ≫ qT = 𝟙 _ := by rw [Category.assoc]; exact hq
    have hy' : (rO ≫ kO) ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
      rw [Category.assoc]; exact hy
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, hq', Category.id_comp, hy']
  rintro _ ⟨p, rfl⟩
  rw [hz]
  exact hao ⟨p, rfl⟩

end GlobalTheory.MoveNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_translate_mem_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.MoveNear.exists_section_translate_mem | exact GlobalTheory.MoveNear.exists_section_translate_mem | (intros; apply GlobalTheory.MoveNear.exists_section_translate_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_sec_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)
    (g : Over.mk s ⟶ G) (x : Over.mk (𝟙 S) ⟶ G) :
    (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left = g.left ≫ (transl x).left := by
  have h2 : g ≫ (Over.homMk G.hom (by simp) : G ⟶ Over.mk (𝟙 S)) = Over.homMk s (by simp) := by
    ext; exact Over.w g
  rw [← Over.comp_left, transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, h2]

theorem irreducibleSpace_fibre_of_semiAbelian {S : Scheme.{0}} (G' : Over S) [GrpObj G'] (hG : IsSemiAbelian G')
    (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) : IrreducibleSpace (pullback G'.hom s : Scheme.{0}) := by
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have hc : ConnectedSpace (pullback G'.hom s : Scheme.{0}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) s _ _ (IsPullback.of_hasPullback G'.hom s)
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace Ω _ (pullback.snd G'.hom s) inferInstance hc

theorem range_one_subset_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (hπ : IsProper π)
    (G' : Over S) [GrpObj G'] (N : Near π G') :
    Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u := by
  have hW : IsOpen ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u) :=
    N.isOpen.isOpen_range.preimage (1 : Over.mk (𝟙 S) ⟶ G').left.continuous
  have hcl : IsClosed (π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ) :=
    π.isClosedMap _ hW.isClosed_compl
  have hover : ∀ z : S, G'.hom ((1 : Over.mk (𝟙 S) ⟶ G').left z) = z := fun z => by
    have := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
    change ((1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom) z = z
    rw [this]; rfl
  rintro _ ⟨z, rfl⟩
  by_contra hz
  have hmem : π z ∈ π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwc⟩ := (IsLocalRing.specializes_closedPoint (π z)).mem_closed hcl hmem
  apply hw
  apply N.all
  rw [hover]; exact hwc

theorem cover_by_translates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π hπ hs hS G' _ _ hG N hL
  obtain ⟨e, he, hPe⟩ := GlobalTheory.T.unitSection_near_closedFibre_descends_to_base R hR S π hπ hs hS G' hG N hL (range_one_subset_near π hπ G' N)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  let Idx := {ax : (Sp R ⟶ N.U.left) × (Over.mk (𝟙 S) ⟶ G') // ax.1 ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ ax.1) ax.2.left}
  let V : Idx → Set G'.left := fun i => Set.range N.u ∪ (transl i.1.2).left ⁻¹' Set.range N.u
  have hopen : IsOpen (Set.range N.u) := N.isOpen.isOpen_range
  have hV : ∀ i, IsOpen (V i) := fun i => hopen.union (hopen.preimage (transl _).left.continuous)
  have hcov : Set.univ ⊆ ⋃ i, V i := by
    intro p _
    by_cases hp : p ∈ Set.range N.u
    · exact Set.mem_iUnion.2 ⟨⟨(e, 1), he, hPe⟩, Or.inl hp⟩
    · have hfp : (G'.left.fromSpecResidueField p) (closedPoint _) = p := G'.left.fromSpecResidueField_apply p _
      have hnc : closedPoint R ∉ Set.range (G'.left.fromSpecResidueField p ≫ G'.hom ≫ π) := by
        rintro ⟨y, hy⟩
        apply hp
        apply N.all
        rw [← hy, Subsingleton.elim y (closedPoint _)]
        change π (G'.hom p) = π (G'.hom ((G'.left.fromSpecResidueField p) _))
        rw [hfp]
      obtain ⟨a, x, ha, hPa, hr⟩ := GlobalTheory.T.exists_section_translate_mem_near_closedFibre R hR S π G' hG N e he hPe (G'.left.residueField p)
        (G'.left.fromSpecResidueField p ≫ G'.hom) (Over.homMk (G'.left.fromSpecResidueField p) rfl)
        (irreducibleSpace_fibre_of_semiAbelian G' hG _ _) (by simpa [Category.assoc] using hnc)
      rw [mul_sec_left_eq] at hr
      refine Set.mem_iUnion.2 ⟨⟨(a, x), ha, hPa⟩, Or.inr ?_⟩
      have := hr ⟨closedPoint _, rfl⟩
      change (transl x).left ((G'.left.fromSpecResidueField p) (closedPoint _)) ∈ _ at this
      rwa [hfp] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcov
  refine ⟨t.card, fun k => (t.equivFin.symm k).1.1.1, fun k => (t.equivFin.symm k).1.1.2,
    fun k => (t.equivFin.symm k).1.2, ?_⟩
  intro Ω _ s g
  have hpt : ∀ y : Sp Ω, y = closedPoint Ω := fun y => Subsingleton.elim _ _
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (g.left (closedPoint Ω))))
  rcases hi with hi | hi
  · left
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi
  · right
    refine ⟨t.equivFin ⟨i, hit⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [mul_sec_left_eq]
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_section_translates_cover_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.Mum.cover_by_translates | exact GlobalTheory.Mum.cover_by_translates | (intros; apply GlobalTheory.Mum.cover_by_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem transl_toTerm_eq {S : Scheme.{0}} {X : Over S} (f g : X ⟶ Over.mk (𝟙 S)) : f = g := by
  ext
  have hf := Over.w f
  have hg := Over.w g
  simp only [Over.mk_hom] at hf hg
  exact (Category.comp_id f.left).symm.trans (hf.trans (hg.symm.trans (Category.comp_id g.left)))

theorem transl_comp {S : Scheme.{0}} {G : Over S} [GrpObj G] (y z : Over.mk (𝟙 S) ⟶ G) :
    transl y ≫ transl z = transl (y * z) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc,
    transl_toTerm_eq (_ ≫ Over.homMk G.hom (by simp)) (Over.homMk G.hom (by simp)), _root_.mul_assoc, ← comp_mul]

theorem transl_one {S : Scheme.{0}} {G : Over S} [GrpObj G] : transl (1 : Over.mk (𝟙 S) ⟶ G) = 𝟙 G := by
  unfold transl
  rw [comp_one, _root_.mul_one]

instance transl_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y) :=
  ⟨⟨transl y⁻¹, by rw [transl_comp, _root_.mul_inv_cancel, transl_one], by rw [transl_comp, _root_.inv_mul_cancel, transl_one]⟩⟩

instance transl_left_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y).left :=
  inferInstanceAs (IsIso ((Over.forget S).map (transl y)))

theorem Near.chart_isOpenImmersion_over {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)) :
    IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  have := N.isOpen
  cases j with
  | none => exact ⟨N.isOpen, N.u_over⟩
  | some k =>
    refine ⟨?_, ?_⟩
    · rw [Near.chart_some]; infer_instance
    · rw [Near.chart_some, Category.assoc, Over.w, N.u_over]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_isOpenImmersion_over_base : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)), IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  first | exact @GlobalTheory.Mum.Near.chart_isOpenImmersion_over | exact GlobalTheory.Mum.Near.chart_isOpenImmersion_over | (intros; apply GlobalTheory.Mum.Near.chart_isOpenImmersion_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G' : Over S} [GrpObj G']

theorem Near.datum_pt (N : Near π G') {φ} (hφ : N.Datum φ) {T : Scheme.{0}} (s : T ⟶ pullback π π)
    (x₀ x₀' : T ⟶ pullback N.U.hom π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (h₁ : x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _) (h₂ : x₀ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₃ : x₀' ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (hz₁ : z ≫ pullback.fst _ _ = x₀ ≫ N.u)
    (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = x₀' ≫ N.u := by
  obtain ⟨x₁, e₁, e₂, e₃⟩ := hφ.2 T (x₀ ≫ pullback.fst _ _) z
    ⟨x₀, rfl, by rw [← Category.assoc, hz₂, h₂], hz₁.symm⟩
  have : x₁ = x₀' := pullback.hom_ext (e₁.trans h₁.symm) (by rw [e₂, ← Category.assoc, hz₂, h₃])
  rw [← e₃, this]

theorem transl_pt {T : Scheme.{0}} (t : T ⟶ S) (g : Over.mk t ⟶ G') (y : Over.mk (𝟙 S) ⟶ G') :
    g ≫ transl y = g * (Over.homMk t (Category.comp_id t) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  ext
  simp [Over.w g]

theorem pull_pt_ext {S' : Scheme.{0}} (f : S' ⟶ S) {T : Scheme.{0}} {s : T ⟶ S'}
    (a b : Over.mk s ⟶ (Over.pullback f).obj G') (h : a.left ≫ pullback.fst G'.hom f = b.left ≫ pullback.fst G'.hom f) :
    a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

end

theorem Near.datum_chart {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G'))
    (hx : ∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) (φ) (hφ : N.Datum φ) (j : Option (Fin n)) (T : Scheme.{0})
    (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π)
    (hy : y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _) (h₁ : y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₂ : y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (hz₁ : z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j) (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  cases j with
  | none => exact N.datum_pt hφ s y₁ y₂ z hy.symm h₁ h₂ hz₁ hz₂
  | some k =>
  haveI := hφ.1
  rw [Near.chart_some] at hz₁ ⊢
  obtain ⟨x₀, e₁, e₂, e₃⟩ := hx k
  have hxo : (x k).left ≫ G'.hom = 𝟙 S := Over.w (x k)
  have c₁ : (y₁ ≫ N.u) ≫ G'.hom = s ≫ pullback.fst π π := by rw [Category.assoc, N.u_over, h₁]
  have c₂ : (y₂ ≫ N.u) ≫ G'.hom = s ≫ pullback.snd π π := by rw [Category.assoc, N.u_over, h₂]
  have d₁ : (s ≫ pullback.fst π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.fst π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  have d₂ : (s ≫ pullback.snd π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.snd π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  let G₁ := (Over.pullback (pullback.fst π π)).obj G'
  let G₂ := (Over.pullback (pullback.snd π π)).obj G'
  let W₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ c₁) (pullback.lift_snd _ _ _)
  let X₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ d₁) (pullback.lift_snd _ _ _)
  let W₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ c₂) (pullback.lift_snd _ _ _)
  let X₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ d₂) (pullback.lift_snd _ _ _)
  let Z₁ : Over.mk s ⟶ G₁ := Over.homMk z hz₂
  let P₁ := pushHom (isGrpPullback_pullback G' (pullback.fst π π)) (Over.mk s)
  let P₂ := pushHom (isGrpPullback_pullback G' (pullback.snd π π)) (Over.mk s)
  let w₁ : Over.mk (s ≫ pullback.fst π π) ⟶ G' := Over.homMk (y₁ ≫ N.u) c₁
  let w₂ : Over.mk (s ≫ pullback.snd π π) ⟶ G' := Over.homMk (y₂ ≫ N.u) c₂
  have pW₁ : P₁ W₁ = w₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pW₂ : P₂ W₂ = w₂ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₁ : P₁ X₁ = Over.homMk (s ≫ pullback.fst π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₂ : P₂ X₂ = Over.homMk (s ≫ pullback.snd π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)

  have hZ : Z₁ = W₁ * X₁⁻¹ := by
    apply pull_pt_ext
    have e : P₁ Z₁ = P₁ (W₁ * X₁⁻¹) := by
      rw [map_mul, map_inv, pW₁, pX₁, ← GrpObj.comp_inv, ← transl_pt]
      exact Over.OverMorphism.ext (by
        show z ≫ pullback.fst _ _ = (y₁ ≫ N.u) ≫ (transl (x k)⁻¹).left
        rw [hz₁, Category.assoc])
    exact congrArg (fun q => q.left) e
  have hW : W₁ ≫ φ.hom = W₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s y₁ y₂ _ hy.symm h₁ h₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans ?_
    exact (pullback.lift_fst _ _ _).symm
  have hX : X₁ ≫ φ.hom = X₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s (s ≫ pullback.fst π π ≫ x₀) (s ≫ pullback.snd π π ≫ x₀) _ ?_ ?_ ?_ ?_
      (pullback.lift_snd _ _ _)).trans ?_
    · simp only [Category.assoc, e₁]
      rw [← Category.assoc (pullback.snd π π), ← pullback.condition, Category.assoc]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · rw [pullback.lift_fst]; simp only [Category.assoc, e₃]
    · refine Eq.trans ?_ (pullback.lift_fst _ _ d₂).symm
      simp only [Category.assoc, e₃]
  have e : P₂ (Z₁ ≫ φ.hom) = w₂ ≫ transl (x k)⁻¹ := by
    rw [hZ, mul_comp, GrpObj.inv_comp, hW, hX, map_mul, map_inv, pW₂, pX₂, ← GrpObj.comp_inv, ← transl_pt]
  have e' : (z ≫ φ.hom.left) ≫ pullback.fst G'.hom (pullback.snd π π) = (y₂ ≫ N.u) ≫ (transl (x k)⁻¹).left :=
    congrArg (fun q => q.left) e
  simpa only [Category.assoc] using e'

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentDatum_carries_translateChart : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) → ∀ φ, N.Datum φ → ∀ (j : Option (Fin n)) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback G'.hom (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j → z ≫ pullback.snd _ _ = s → z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  first | exact @GlobalTheory.Mum.Near.datum_chart | exact GlobalTheory.Mum.Near.datum_chart | (intros; apply GlobalTheory.Mum.Near.datum_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartCover_toTerm {S : Scheme.{0}} {A : Over S} (f : A ⟶ Over.mk (𝟙 S)) :
    f = Over.homMk A.hom (by simp) := by
  ext1
  simpa using Over.w f

theorem comp_transl {S : Scheme.{0}} {G A : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) (h : A ⟶ G) :
    h ≫ transl y = h * (Over.homMk A.hom (by simp) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  exact chartCover_toTerm _

theorem chart_cover : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G']
    (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')),
    (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨
      ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) →
    ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  intro R _ _ S π G' _ N n x H p
  let t : Sp (G'.left.residueField p) ⟶ G'.left := G'.left.fromSpecResidueField p
  let s : Sp (G'.left.residueField p) ⟶ S := t ≫ G'.hom
  let g : Over.mk s ⟶ G' := Over.homMk t rfl
  have hp : g.left (IsLocalRing.closedPoint _) = p := Scheme.fromSpecResidueField_apply p _
  rcases H (G'.left.residueField p) s g with h1 | ⟨i, h2⟩
  · exact ⟨none, by simpa [Near.chart] using h1 ⟨_, hp⟩⟩
  · let c : Over.mk s ⟶ G' := (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i
    obtain ⟨b, hb⟩ := h2 ⟨IsLocalRing.closedPoint _, rfl⟩
    have key : (g * c) ≫ transl (x i)⁻¹ = g := by
      rw [comp_transl]
      have e : (Over.homMk (Over.mk s).hom (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ (x i)⁻¹ = c⁻¹ := by
        rw [GrpObj.comp_inv]; rfl
      rw [e, mul_inv_cancel_right]
    refine ⟨some i, b, ?_⟩
    rw [Near.chart_some, Scheme.Hom.comp_apply, hb]
    have e2 : ((g * c) ≫ transl (x i)⁻¹).left (IsLocalRing.closedPoint _) = p := by rw [key]; exact hp
    rw [Over.comp_left] at e2
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothNeighbourhood_translates_cover_group : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) → ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  first | exact @GlobalTheory.Mum.chart_cover | exact GlobalTheory.Mum.chart_cover | (intros; apply GlobalTheory.Mum.chart_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem smooth_of_charts_cover : ∀ (Y G U : Scheme.{0}) (J : Type) (ψ : J → (U ⟶ G)) (g : G ⟶ Y) (h : U ⟶ Y), (∀ j, IsOpenImmersion (ψ j)) → (∀ x : G, ∃ j, x ∈ Set.range (ψ j)) → (∀ j, ψ j ≫ g = h) → Smooth h → Smooth g := by
  intro Y G U J ψ g h ho hc hw hs
  let 𝒰 : G.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => U) ψ (fun x => by
    obtain ⟨j, hj⟩ := hc x; exact ⟨j, hj⟩) ho
  haveI : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 ?_
  intro j
  have h2 : 𝒰.f j ≫ g = h := hw j
  rw [h2]; exact hs

theorem descends_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  intro R _ _ _ hA S π hp hs hS G' _ _ hG N hL φ hφ
  obtain ⟨n, a, x, hx, hcov⟩ := GlobalTheory.T.finite_section_translates_cover_semiAbelian R hA S π hp hs hS G' hG N hL
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : Smooth N.U.hom := N.smooth
  obtain ⟨G, β, ψ, hψ, hcovG, hpb, hφβ⟩ := GlobalTheory.T.exists_descent_of_charts_pulled_back_from_flat R S G'.left π G'.hom hp hs hS φ.hom.left (Over.w φ.hom)
    N.U inferInstance (Option (Fin n)) (N.chart x) (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).1)
    (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).2) (GlobalTheory.T.smoothNeighbourhood_translates_cover_group S π G' N n x hcov)
    (GlobalTheory.T.descentDatum_carries_translateChart S π G' N n a x (fun i => (hx i).2) φ hφ)
  refine ⟨G, β, Over.homMk (ψ none) (hψ none).2.1, ?_, hpb, (hψ none).1, ?_, hφβ⟩
  · exact smooth_of_charts_cover _ _ _ _ ψ G.hom N.U.hom (fun j => (hψ j).1) hcovG (fun j => (hψ j).2.1) N.smooth
  · simpa [Near.chart] using (hψ none).2.2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.descends_near_closed_fibre | exact GlobalTheory.Mum.descends_near_closed_fibre | (intros; apply GlobalTheory.Mum.descends_near_closed_fibre <;> assumption)
end

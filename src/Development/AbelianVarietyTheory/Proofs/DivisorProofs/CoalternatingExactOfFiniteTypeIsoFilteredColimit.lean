module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_descends_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
      IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g →
      ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B),
        EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  intro J _ _ D c hc B g hg
  obtain ⟨-, hsurj⟩ := (etFF_iff_spec g).1 hg
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hgh, hcov⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc Unit (fun _ ↦ B)
      (fun _ ↦ g) (fun _ ↦ hg.1)
      (fun p ↦ by
        obtain ⟨v, hv⟩ := hsurj.surj p
        exact ⟨(), v, hv⟩) j₀
  refine ⟨j, B' (), g' (), h (), ?_, (hgh ()).2⟩
  rw [etFF_iff_spec]
  refine ⟨HasRingHomProperty.Spec_iff.2 (hgh ()).1, ⟨fun p ↦ ?_⟩⟩
  obtain ⟨i, v, hv⟩ := hcov p
  cases i
  exact ⟨v, hv⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g → ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B), EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  first | (exact @GlobalTheory.EtC.etFF_descends_of_isColimit) | (exact GlobalTheory.EtC.etFF_descends_of_isColimit) | (intros; apply GlobalTheory.EtC.etFF_descends_of_isColimit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtFFApprox

variable {J : Type} [SmallCategory J] (D0 : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}} (g' : D0.obj j ⟶ B')

def pmap {k k' : Under j} (φ : k ⟶ k') : pushout g' (D0.map k.hom) ⟶ pushout g' (D0.map k'.hom) :=
  pushout.desc (pushout.inl _ _) (D0.map φ.right ≫ pushout.inr _ _)
    (by rw [pushout.condition, ← Category.assoc, ← D0.map_comp, Under.w φ])

@[reassoc (attr := simp)] lemma inl_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inl _ _ ≫ pmap D0 j g' φ = pushout.inl _ _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma inr_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inr _ _ ≫ pmap D0 j g' φ = D0.map φ.right ≫ pushout.inr _ _ := pushout.inr_desc _ _ _

def arrF : Under j ⥤ Arrow CommRingCat.{0} where
  obj k := Arrow.mk (pushout.inr g' (D0.map k.hom))
  map {k k'} φ := Arrow.homMk' (D0.map φ.right) (pmap D0 j g' φ) (inr_pmap D0 j g' φ).symm
  map_id k := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp
  map_comp φ ψ := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp

@[simp] lemma arrF_map_left {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).left = D0.map φ.right := rfl
@[simp] lemma arrF_map_right {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).right = pmap D0 j g' φ := rfl

variable {A B : CommRingCat.{0}} (ι0 : D0 ⟶ (Functor.const J).obj A) (g : A ⟶ B) (h : B' ⟶ B)
  (hnat : ∀ k : Under j, g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g)

def pdesc (k : Under j) : pushout g' (D0.map k.hom) ⟶ B := pushout.desc h (ι0.app k.right ≫ g) (hnat k)

def coc : arrF D0 j g' ⟶ (Functor.const (Under j)).obj (Arrow.mk g) where
  app k := Arrow.homMk (f := (arrF D0 j g').obj k) (g := Arrow.mk g) (ι0.app k.right) (pdesc D0 j g' ι0 g h hnat k)
    (pushout.inr_desc _ _ (hnat k)).symm
  naturality k k' φ := by
    ext : 1
    · simp only [Arrow.comp_left, Functor.const_obj_map, Arrow.id_left, Category.comp_id, Arrow.homMk_left, arrF_map_left]
      rw [ι0.naturality φ.right]
      simp
    · simp only [Arrow.comp_right, Functor.const_obj_map, Arrow.id_right, Category.comp_id, Arrow.homMk_right, arrF_map_right]
      apply pushout.hom_ext
      · simp [pdesc]
      · simp only [pdesc, inr_pmap_assoc, pushout.inr_desc]
        rw [ι0.naturality_assoc φ.right]
        simp

lemma snd_coc (k : Under j) : (Comma.snd (𝟭 _) (𝟭 _)).map ((coc D0 j g' ι0 g h hnat).app k) = pdesc D0 j g' ι0 g h hnat k := rfl

@[reassoc] lemma inl_pdesc (k : Under j) : pushout.inl _ _ ≫ pdesc D0 j g' ι0 g h hnat k = h := pushout.inl_desc _ _ _
@[reassoc] lemma inr_pdesc (k : Under j) : pushout.inr _ _ ≫ pdesc D0 j g' ι0 g h hnat k = ι0.app k.right ≫ g := pushout.inr_desc _ _ _

def leftOf (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) : Cocone (Under.forget j ⋙ D0) where
  pt := s.pt
  ι := { app := fun k => pushout.inr g' (D0.map k.hom) ≫ s.ι.app k
         naturality := fun k k' φ => by
           have hw := s.w φ
           simp only [Functor.comp_map, Comma.snd_map] at hw
           dsimp
           rw [← hw, Category.comp_id]
           simp }

@[simp] lemma leftOf_ι_app (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) (k : Under j) :
    (leftOf D0 j g' s).ι.app k = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k := rfl

def rightIsColimit (hP : IsPushout g' (ι0.app j) h g) (hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j))) :
    IsColimit ((Comma.snd (𝟭 _) (𝟭 _)).mapCocone (Cocone.mk (Arrow.mk g) (coc D0 j g' ι0 g h hnat))) where
  desc s := hP.desc (pushout.inl _ _ ≫ s.ι.app (Under.mk (𝟙 j))) (hL.desc (leftOf D0 j g' s)) (by
      have := hL.fac (leftOf D0 j g' s) (Under.mk (𝟙 j))
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [pushout.condition_assoc]
      simp only [Under.mk_right] at this
      rw [this]
      simp)
  fac s k := by
    change pdesc D0 j g' ι0 g h hnat k ≫ _ = s.ι.app k
    apply pushout.hom_ext
    · have hw := s.w (Under.homMk k.hom (by simp) : Under.mk (𝟙 j) ⟶ k)
      simp only [Functor.comp_map, Comma.snd_map, arrF_map_right] at hw
      rw [inl_pdesc_assoc, IsPushout.inl_desc, ← hw]
      exact inl_pmap_assoc D0 j g' _ _
    · have := hL.fac (leftOf D0 j g' s) k
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [inr_pdesc_assoc, IsPushout.inr_desc, this]
  uniq s m hm := by
    apply hP.hom_ext
    · rw [IsPushout.inl_desc]
      have h1 := hm (Under.mk (𝟙 j))
      change pdesc D0 j g' ι0 g h hnat (Under.mk (𝟙 j)) ≫ m = s.ι.app (Under.mk (𝟙 j)) at h1
      rw [← h1, inl_pdesc_assoc]
    · rw [IsPushout.inr_desc]
      apply hL.hom_ext
      intro k
      have h1 := hL.fac (leftOf D0 j g' s) k
      have h2 := hm k
      change ι0.app k.right ≫ _ = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k at h1
      change pdesc D0 j g' ι0 g h hnat k ≫ m = s.ι.app k at h2
      change ι0.app k.right ≫ _ = ι0.app k.right ≫ _
      rw [h1, ← h2, inr_pdesc_assoc]

end GlobalTheory.EtFFApprox


open GlobalTheory.EtFFApprox in
theorem GlobalTheory.EtC.etFF_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  intro A B g hg
  obtain ⟨J, _, _, D0, ι0, ⟨hc⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨j, B', g', h, hg', hP⟩ := GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit J D0 (Cocone.mk A ι0) hc B g hg
  have hb := GlobalTheory.EtC.etFF_basic
  haveI := hb.1.2.1
  have hP' : IsPushout g' (ι0.app j) h g := hP
  have hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm hc
  have hnat : ∀ (k : Under j), g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g := by
    intro k
    rw [← Category.assoc, ι0.naturality k.hom]
    simpa using hP'.w
  refine ⟨Under j, inferInstance, inferInstance, arrF D0 j g', coc D0 j g' ι0 g h hnat, ⟨?_⟩, fun k => ?_⟩
  · exact Comma.fstSndJointlyReflectColimit hL (rightIsColimit D0 j g' ι0 g h hnat hP' hL)
  · have hk : EtFF (pushout.inr g' (D0.map k.hom)) :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_hasPushout g' (D0.map k.hom)).flip hg'
    exact ⟨hk, hft k.right, hb.2.2 _ _ _ hk (hft k.right)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteTypeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  first | (exact @GlobalTheory.EtC.etFF_filtered_colimit_finiteType) | (exact GlobalTheory.EtC.etFF_filtered_colimit_finiteType) | (intros; apply GlobalTheory.EtC.etFF_filtered_colimit_finiteType  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactColim

abbrev altC {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

abbrev altM {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1}) :
    altC X F ⟶ altC Y F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerRight g F)

theorem altM_d {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1})
    (n m : ℕ) (w : (altC X F).X n) :
    (altC Y F).d n m ((altM g F).f n w) = (altM g F).f m ((altC X F).d n m w) := by
  have h := ConcreteCategory.congr_hom ((altM g F).comm n m) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

theorem altM_comp {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM (g ≫ h) F).f n w := by
  show F.map (h.app _) (F.map (g.app _) w) = F.map (g.app _ ≫ h.app _) w
  rw [F.map_comp]
  rfl

theorem altM_comp' {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (g' : X ⟶ Z) (e : g ≫ h = g') (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM g' F).f n w := by
  subst e
  exact altM_comp g h F n w

theorem exact_elt {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ)
    (h : (altC X F).ExactAt (n + 1)) (w : (altC X F).X (n + 1)) (hw : (altC X F).d (n + 1) (n + 2) w = 0) :
    ∃ v : (altC X F).X n, (altC X F).d n (n + 1) v = w := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem wExact_colimit : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (U : J ⥤ T) (X : J ⥤ CosimplicialObject T) (a : U ⋙ CosimplicialObject.const T ⟶ X) (cU : Cocone U) (cX : Cocone X) (b : (CosimplicialObject.const T).obj cU.pt ⟶ cX.pt), IsColimit cU → (∀ k : SimplexCategory, Nonempty (IsColimit (((evaluation SimplexCategory T).obj k).mapCocone cX))) → (∀ j, a.app j ≫ cX.ι.app j = (CosimplicialObject.const T).map (cU.ι.app j) ≫ b) → (∀ j, WExact N (a.app j)) → WExact N b := by
  intro T _ N hN J _ _ U X a cU cX b hU hX hab hW
  have fe := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements T N).1 hN
  have hNc : ∀ {A B C : T} (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A), N.map (f ≫ g) x = N.map g (N.map f x) := by
    intros; simp
  have hab' : ∀ j (k : SimplexCategory), (a.app j).app k ≫ (cX.ι.app j).app k = cU.ι.app j ≫ b.app k := by
    intro j k
    exact NatTrans.congr_app (hab j) k
  have hnat : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (a.app j).app k ≫ (X.map f).app k = U.map f ≫ (a.app j').app k := by
    intro j j' f k
    exact (NatTrans.congr_app (a.naturality f) k).symm
  have hXι : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (X.map f).app k ≫ (cX.ι.app j').app k = (cX.ι.app j).app k := by
    intro j j' f k
    exact NatTrans.congr_app (cX.w f) k
  have feX : ∀ k : SimplexCategory, (∀ x : N.obj (cX.pt.obj k), ∃ j y, N.map ((cX.ι.app j).app k) y = x) ∧
      ∀ j (y : N.obj ((X.obj j).obj k)), N.map ((cX.ι.app j).app k) y = 0 → ∃ (j' : J) (f : j ⟶ j'), N.map ((X.map f).app k) y = 0 := by
    intro k
    exact fe J (X ⋙ (evaluation SimplexCategory T).obj k) _ (hX k).some
  have feU := fe J U cU hU
  refine ⟨?_, ?_, ?_⟩
  ·
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := feU.1 x
    have h0 : N.map ((cX.ι.app j).app (SimplexCategory.mk 0)) (N.map ((a.app j).app (SimplexCategory.mk 0)) y) = 0 := by
      rw [← hNc, hab', hNc]; simpa using hx
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h0
    rw [← hNc, hnat, hNc] at hf
    have hk := (hW k).1 (hf.trans (map_zero _).symm)
    rw [← cU.w f, hNc]
    simp only [Functor.comp_obj] at hk
    rw [hk, map_zero]
  ·
    intro y hy
    obtain ⟨j, y', rfl⟩ := (feX _).1 y
    have hδ : ∀ {Y Z : CosimplicialObject T} (g : Y ⟶ Z) (i : Fin 2),
        Y.δ (n := 0) i ≫ g.app (SimplexCategory.mk 1) = g.app (SimplexCategory.mk 0) ≫ Z.δ (n := 0) i :=
      fun g i => g.naturality _
    set d' := N.map ((X.obj j).δ (n := 0) 0) y' - N.map ((X.obj j).δ (n := 0) 1) y' with hd'
    have h1 : N.map ((cX.ι.app j).app (SimplexCategory.mk 1)) d' = 0 := by
      rw [hd', map_sub, ← hNc, ← hNc, hδ, hδ, hNc, hNc]
      exact sub_eq_zero.mpr hy
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : N.map ((X.obj k).δ (n := 0) 0) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') =
        N.map ((X.obj k).δ (n := 0) 1) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') := by
      rw [← sub_eq_zero, ← hNc, ← hNc, ← hδ, ← hδ, hNc, hNc, ← map_sub]
      exact hf
    obtain ⟨x, hx⟩ := (hW k).2.1 _ h2
    refine ⟨N.map (cU.ι.app k) x, ?_⟩
    rw [← hNc, ← hab', hNc]
    simp only [Functor.comp_obj] at hx
    rw [hx, ← hNc, hXι]
  · intro n
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
    intro z hz
    obtain ⟨j, z', rfl⟩ := (feX _).1 z
    have h1 : (altM (cX.ι.app j) N).f (n + 2) ((altC (X.obj j) N).d (n + 1) (n + 2) z') = 0 := by
      exact (altM_d (cX.ι.app j) N (n + 1) (n + 2) z').symm.trans hz
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : (altC (X.obj k) N).d (n + 1) (n + 2) ((altM (X.map f) N).f (n + 1) z') = 0 := by
      exact (altM_d (X.map f) N (n + 1) (n + 2) z').trans hf
    obtain ⟨v, hv⟩ := exact_elt _ N n ((hW k).2.2 n) _ h2
    refine ⟨(altM (cX.ι.app k) N).f n v, ?_⟩
    show (altC cX.pt N).d n (n + 1) ((altM (cX.ι.app k) N).f n v) = (altM (cX.ι.app j) N).f (n + 1) z'
    rw [altM_d, hv]
    exact altM_comp' (X.map f) (cX.ι.app k) (cX.ι.app j) (cX.w f) N (n + 1) z'

end GlobalTheory.EtC.WExactColim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitLeftFuncAndCechConerveLevels
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isColimit_leftFunc_and_cechConerve_levels :
    ∀ (J : Type) [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) (c : Cocone D), IsColimit c →
      Nonempty (IsColimit (Arrow.leftFunc.mapCocone c)) ∧
      ∀ k : SimplexCategory, Nonempty (IsColimit ((CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k).mapCocone c)) := by
  intro J _ D c hc
  refine ⟨⟨isColimitOfPreserves Arrow.leftFunc hc⟩, fun k => ⟨?_⟩⟩
  have e : (CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory CommRingCat.{0}).obj k) =
      CosimplicialObject.augmentedCechConerve ⋙ CosimplicialObject.Augmented.drop ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k := rfl
  rw [e]
  have h1 : PreservesColimitsOfSize.{0, 0} (CosimplicialObject.augmentedCechConerve (C := CommRingCat.{0})) :=
    CosimplicialObject.cechConerveAdjunction.leftAdjoint_preservesColimits
  have h0 : PreservesColimitsOfShape J (CosimplicialObject.const CommRingCat.{0}) :=
    preservesColimitsOfShape_of_evaluation _ J fun m => by
      have : PreservesColimitsOfShape J (𝟭 CommRingCat.{0}) := inferInstance
      exact this
  have h2 : PreservesColimitsOfShape J (CosimplicialObject.Augmented.drop (C := CommRingCat.{0})) :=
    Comma.preservesColimitsOfShape_snd
  have h3 : PreservesColimitsOfShape J ((evaluation SimplexCategory CommRingCat.{0}).obj k) := inferInstance
  exact @isColimitOfPreserves _ _ _ _ _ _ _ ((evaluation SimplexCategory CommRingCat.{0}).obj k) _
    (isColimitOfPreserves CosimplicialObject.Augmented.drop
      (isColimitOfPreserves CosimplicialObject.augmentedCechConerve hc)) h3.preservesColimit

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveObjFiniteTypeInt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem widePushout_finiteType_int {J : Type} [Finite J] [Nonempty J] (A B : CommRingCat.{0})
    (g : A ⟶ B) (hB : Algebra.FiniteType ℤ B) :
    Algebra.FiniteType ℤ ((widePushout A (fun _ : J => B) (fun _ => g) : CommRingCat.{0})) := by
  classical
  obtain ⟨s, hs⟩ := hB.out
  set W := widePushout A (fun _ : J => B) (fun _ => g) with hW
  let T : Set W := ⋃ j : J, (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)
  have hTfin : T.Finite := Set.finite_iUnion fun j => s.finite_toSet.image _
  let S : Subring W := Subring.closure T
  have hB' : ∀ b : B, b ∈ Subring.closure (s : Set B) := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := hs ▸ Algebra.mem_top
    rw [Algebra.adjoin_int] at hb
    exact hb
  have hmem : ∀ (j : J) (b : B), (WidePushout.ι (fun _ : J => g) j).hom b ∈ S := by
    intro j b
    have hle : (Subring.closure (s : Set B)).map (WidePushout.ι (fun _ : J => g) j).hom ≤ S := by
      rw [RingHom.map_closure]
      exact Subring.closure_mono (Set.subset_iUnion (fun j => (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)) j)
    exact hle ⟨b, hB' b, rfl⟩
  let ιS : J → (B ⟶ CommRingCat.of S) := fun j =>
    CommRingCat.ofHom ((WidePushout.ι (fun _ : J => g) j).hom.codRestrict S (hmem j))
  let j₀ : J := Classical.arbitrary J
  have hw : ∀ j : J, g ≫ ιS j = g ≫ ιS j₀ := by
    intro j
    ext a
    change (g ≫ WidePushout.ι (fun _ : J => g) j) a = (g ≫ WidePushout.ι (fun _ : J => g) j₀) a
    rw [WidePushout.arrow_ι (fun _ : J => g) j, WidePushout.arrow_ι (fun _ : J => g) j₀]
  let d : W ⟶ CommRingCat.of S := WidePushout.desc (g ≫ ιS j₀) ιS hw
  let incl : CommRingCat.of S ⟶ W := CommRingCat.ofHom S.subtype
  have hid : d ≫ incl = 𝟙 W := by
    apply WidePushout.hom_ext
    · intro j
      rw [← Category.assoc, WidePushout.ι_desc]
      ext b <;> rfl
    · rw [← Category.assoc, WidePushout.head_desc, ← WidePushout.arrow_ι (fun _ : J => g) j₀]
      ext a <;> rfl
  have htop : ∀ w : W, w ∈ S := by
    intro w
    have : (d ≫ incl) w = w := by rw [hid]; rfl
    rw [← this]
    exact (d w).2
  refine ⟨⟨hTfin.toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset, Algebra.adjoin_int]
  ext w
  simp only [Algebra.mem_top, iff_true]
  exact htop w

end GlobalTheory

theorem GlobalTheory.cechConerve_obj_finiteType_int : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), Algebra.FiniteType ℤ B →
    ∀ k : SimplexCategory, Algebra.FiniteType ℤ ((Arrow.mk g).cechConerve.obj k) := by
  intro A B g hB k
  exact GlobalTheory.widePushout_finiteType_int (J := Fin (k.len + 1)) A B g hB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactCongr
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactCongr

variable {T : Type 1} [Category.{0} T]

theorem exactAt_iff {N M : T ⥤ AddCommGrpCat.{1}} (ε : N ⟶ M) {X : CosimplicialObject T}
    (hX : ∀ k, IsIso (ε.app (X.obj k))) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ N)).ExactAt (n + 1) ↔
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1) := by
  haveI : ∀ k, IsIso ((Functor.whiskerLeft X ε).app k) := fun k => hX k
  have hw : IsIso (Functor.whiskerLeft X ε) := NatIso.isIso_of_isIso_app _
  let e := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).mapIso (@asIso _ _ _ _ (Functor.whiskerLeft X ε) hw)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

theorem wExact_iff (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M) (hU : IsIso (ε.app U)) (hX : ∀ k, IsIso (ε.app (X.obj k))) :
    WExact N a ↔ WExact M a := by
  have nat : ∀ {P Q : T} (f : P ⟶ Q) (x : N.obj P), M.map f (ε.app P x) = ε.app Q (N.map f x) := by
    intro P Q f x
    exact (ConcreteCategory.congr_hom (ε.naturality f) x).symm
  have surj : ∀ (P : T), IsIso (ε.app P) → ∀ (x : M.obj P), ∃ x', ε.app P x' = x := by
    intro P hP x
    refine ⟨inv (ε.app P) x, ?_⟩
    have := ConcreteCategory.congr_hom (IsIso.inv_hom_id (ε.app P)) x
    simpa using this
  have inj : ∀ (P : T), IsIso (ε.app P) → ∀ (x y : N.obj P), ε.app P x = ε.app P y → x = y := by
    intro P hP x y hxy
    have h := congrArg (inv (ε.app P)) hxy
    have hx := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) x
    have hy := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) y
    simp only [ConcreteCategory.comp_apply] at hx hy
    rw [hx, hy] at h
    simpa using h
  have h0 := hX (SimplexCategory.mk 0)
  have h1 := hX (SimplexCategory.mk 1)
  constructor
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).1 (i3 n)⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := surj _ hU x
      obtain ⟨y, rfl⟩ := surj _ hU y
      erw [nat, nat] at hxy
      rw [i1 (inj _ h0 _ _ hxy)]
    · intro y hy
      obtain ⟨y, rfl⟩ := surj _ h0 y
      erw [nat, nat] at hy
      obtain ⟨x, hx⟩ := i2 y (inj _ h1 _ _ hy)
      exact ⟨ε.app U x, (nat _ x).trans (congrArg _ hx)⟩
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).2 (i3 n)⟩
    · intro x y hxy
      have h := congrArg (ε.app _) hxy
      erw [← nat, ← nat] at h
      exact inj _ hU _ _ (i1 h)
    · intro y hy
      have h := congrArg (ε.app _) hy
      erw [← nat, ← nat] at h
      obtain ⟨x, hx⟩ := i2 _ h
      obtain ⟨x, rfl⟩ := surj _ hU x
      erw [nat] at hx
      exact ⟨x, inj _ h0 _ _ hx⟩

end GlobalTheory.EtC.WExactCongr

theorem GlobalTheory.EtC.wExact_congr : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M),
    IsIso (ε.app U) → (∀ k, IsIso (ε.app (X.obj k))) → (WExact N a ↔ WExact M a) :=
  fun _ _ U X a N M ε hU hX => GlobalTheory.EtC.WExactCongr.wExact_iff U X a N M ε hU hX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

noncomputable def coAugNat {J : Type} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) :
    (D ⋙ Arrow.leftFunc) ⋙ CosimplicialObject.const CommRingCat.{0} ⟶ D ⋙ CosimplicialObject.cechConerve where
  app j := coAug (D.obj j).hom
  naturality i j f := by
    have h := (CosimplicialObject.augmentedCechConerve.map (D.map f)).w
    exact h

theorem wExact_of_finiteType_iso (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M)
    (hN : PreservesFilteredColimitsOfSize.{0, 0} N)
    (hε : ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A))
    (hM : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) :
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  intro A B g hg
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType A B g hg
  obtain ⟨⟨hU⟩, hX⟩ := GlobalTheory.EtC.isColimit_leftFunc_and_cechConerve_levels J D _ hc
  refine GlobalTheory.EtC.WExactColim.wExact_colimit CommRingCat.{0} N hN J (D ⋙ Arrow.leftFunc)
    (D ⋙ CosimplicialObject.cechConerve) (coAugNat D) (Arrow.leftFunc.mapCocone (Cocone.mk (Arrow.mk g) ι))
    (CosimplicialObject.cechConerve.mapCocone (Cocone.mk (Arrow.mk g) ι)) (coAug g) hU (fun k => hX k) ?_ ?_
  · intro j
    have h := (CosimplicialObject.augmentedCechConerve.map (ι.app j)).w
    exact h.symm
  · intro j
    obtain ⟨hj, hl, hr⟩ := hD j
    refine (GlobalTheory.EtC.wExact_congr CommRingCat.{0} _ _ (coAug (D.obj j).hom) N M ε (hε _ hl) (fun k => hε _ ?_)).2
      (hM _ _ _ hj)
    exact GlobalTheory.cechConerve_obj_finiteType_int _ _ (D.obj j).hom hr k

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits : ∀ (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) → ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  first | (exact @GlobalTheory.EtC.wExact_of_finiteType_iso) | (exact GlobalTheory.EtC.wExact_of_finiteType_iso) | (intros; apply GlobalTheory.EtC.wExact_of_finiteType_iso  <;> assumption)
end

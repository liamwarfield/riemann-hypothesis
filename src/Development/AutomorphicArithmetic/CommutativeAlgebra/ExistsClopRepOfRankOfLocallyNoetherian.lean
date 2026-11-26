module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExistsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePrope
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def IsHilbRep {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) : Prop :=
  ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧
    IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v →
      IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) →
      ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U,
        IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u

end GlobalTheory.HilbertSch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

def IsFinFlatRk {X Y : Scheme.{0}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ ∀ y, f.finrank y = r

lemma IsFinFlatRk.of_isPullback {P X Y T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ Y}
    {g : T ⟶ Y} (h : IsPullback fst snd f g) {r : ℕ} (hf : IsFinFlatRk f r) : IsFinFlatRk snd r := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h h1,
    MorphismProperty.of_isPullback (P := @Flat) h h2, fun y => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback fst snd f g h y, h3]

lemma IsFinFlatRk.iso_comp {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y} {r : ℕ}
    (hf : IsFinFlatRk f r) : IsFinFlatRk (e ≫ f) r :=
  IsFinFlatRk.of_isPullback (IsPullback.of_horiz_isIso (fst := e) (g := 𝟙 Y) ⟨by simp⟩) hf

lemma isPullback_comap {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (Scheme.IdealSheafData.subschemeMap _ _ f (I.le_map_comap f))
      f I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by simp [Scheme.IdealSheafData.ker_subschemeι])

variable {S Z : Scheme.{0}} (z : Z ⟶ S)

def bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    pullback z k ⟶ pullback z g :=
  pullback.map z k z g (𝟙 Z) c (𝟙 S) (by simp) (by rw [Category.comp_id, w])

lemma isPullback_bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    IsPullback (bc z c g k w) (pullback.snd z k) (pullback.snd z g) c := by
  subst w
  refine IsPullback.of_right ?_ (by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]) (IsPullback.of_hasPullback z g)
  have e : bc z c g (c ≫ g) rfl ≫ pullback.fst z g = pullback.fst z (c ≫ g) := by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]
  rw [e]
  exact IsPullback.of_hasPullback z (c ≫ g)

lemma bc_id {T : Scheme.{0}} (g : T ⟶ S) (w : 𝟙 T ≫ g = g) : bc z (𝟙 T) g g w = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [bc]

lemma bc_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (m : R ⟶ S)
    (w : a ≫ g = k) (w' : b ≫ k = m) (w'' : (b ≫ a) ≫ g = m) :
    bc z (b ≫ a) g m w'' = bc z b k m w' ≫ bc z a g k w := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]

variable (r : ℕ)

abbrev HIdeal {T : Scheme.{0}} (g : T ⟶ S) : Type :=
  {I : (pullback z g).IdealSheafData // IsFinFlatRk (I.subschemeι ≫ pullback.snd z g) r}

abbrev HPt (T : Scheme.{0}) : Type := Σ g : T ⟶ S, HIdeal z r g

variable {z r}

def HIdeal.pull {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HIdeal z r k :=
  ⟨I.1.comap (bc z c g k w), IsFinFlatRk.of_isPullback
    ((isPullback_comap I.1 (bc z c g k w)).flip.paste_vert (isPullback_bc z c g k w)) I.2⟩

def HPt.map {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) : HPt z r T' :=
  ⟨c ≫ x.1, x.2.pull c rfl⟩

lemma HPt.map_mk {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HPt.map c ⟨g, I⟩ = ⟨k, I.pull c w⟩ := by
  subst w; rfl

lemma HPt.mk_eq_mk_iff {T : Scheme.{0}} {g : T ⟶ S} (I J : HIdeal z r g) :
    (⟨g, I⟩ : HPt z r T) = ⟨g, J⟩ ↔ I.1 = J.1 := by
  rw [Sigma.mk.inj_iff, heq_iff_eq, Subtype.ext_iff]
  simp

lemma HPt.map_eq_mk_iff {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) {k : T' ⟶ S}
    (w : c ≫ x.1 = k) (J : HIdeal z r k) :
    HPt.map c x = ⟨k, J⟩ ↔ x.2.1.comap (bc z c x.1 k w) = J.1 := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk c w, HPt.mk_eq_mk_iff]
  rfl

lemma HPt.map_id {T : Scheme.{0}} (x : HPt z r T) : HPt.map (𝟙 T) x = x := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (𝟙 T) (Category.id_comp g), HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (𝟙 T) g g _) = I.1
  rw [bc_id, Scheme.IdealSheafData.comap_id]

lemma HPt.map_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (x : HPt z r T) :
    HPt.map (b ≫ a) x = HPt.map b (HPt.map a x) := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (b ≫ a) (Category.assoc b a g), HPt.map_mk a rfl, HPt.map_mk b rfl, HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (b ≫ a) g _ _) = (I.1.comap (bc z a g _ rfl)).comap (bc z b (a ≫ g) _ rfl)
  rw [← Scheme.IdealSheafData.comap_comp, bc_comp z b a g (a ≫ g) (b ≫ a ≫ g) rfl rfl]

variable (z r)

def hilbFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := HPt z r T.unop
  map c := TypeCat.ofHom (HPt.map c.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun x => HPt.map_id x
  map_comp a b := ConcreteCategory.hom_ext _ _ fun x => HPt.map_comp _ _ x

def hilbProj : hilbFunctor z r ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun x => x.1

variable {z r}

lemma IsFinFlatRk.ker_subschemeι {T V : Scheme.{0}} {g : T ⟶ S} (v : V ⟶ pullback z g)
    [IsClosedImmersion v] (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) :
    IsFinFlatRk (v.ker.subschemeι ≫ pullback.snd z g) r := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [e, Category.assoc]
  exact hv.iso_comp _

def mkPt {T V : Scheme.{0}} (g : T ⟶ S) (v : V ⟶ pullback z g) [IsClosedImmersion v]
    (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) : HPt z r T :=
  ⟨g, v.ker, hv.ker_subschemeι v⟩

theorem comap_eq_ker_iff {X Y V : Scheme.{0}} (m : X ⟶ Y) (I : Y.IdealSheafData) (v : V ⟶ X)
    [IsClosedImmersion v] : I.comap m = v.ker ↔ ∃ w : V ⟶ I.subscheme, IsPullback v w m I.subschemeι := by
  constructor
  · intro h
    have H : I.subschemeι.ker ≤ (v ≫ m).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, h]
    refine ⟨IsClosedImmersion.lift I.subschemeι (v ≫ m) H,
      isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm ?_⟩
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
  · rintro ⟨w, hP⟩
    rw [← hP.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

end GlobalTheory.HilbGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

namespace GlobalTheory.FiniteFlatLocal

theorem exists_finFree_local : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  intro S Z z h1 h2 h3 s
  obtain ⟨V, hV, hsV, -, hF⟩ := GlobalTheory.FiniteAmpleFP.exists_finFree_app_fp z (x := s) (U := ⊤) trivial
  have hZ : IsAffineOpen (z ⁻¹ᵁ V) := hV.preimage z
  letI : Algebra Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := (z.app V).hom.toAlgebra
  have hfin : Module.Finite Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.1
  have hfree : Module.Free Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.2
  refine ⟨V, Γ(S, V), Γ(Z, z ⁻¹ᵁ V), inferInstance, inferInstance, inferInstance, hfree, hfin,
    hV.isoSpec, hZ.isoSpec, hsV, ?_⟩
  have e := IsAffineOpen.SpecMap_appLE_fromSpec z hV hZ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at e
  rw [← cancel_mono (hV.isoSpec.inv ≫ V.ι)]
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, ← IsAffineOpen.isoSpec_hom_fromSpec hZ, Category.assoc, ← e]
  rfl

end GlobalTheory.FiniteFlatLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlatStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  first | exact @GlobalTheory.FiniteFlatLocal.exists_finFree_local | exact GlobalTheory.FiniteFlatLocal.exists_finFree_local | (intros; apply GlobalTheory.FiniteFlatLocal.exists_finFree_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocal
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

theorem isProper_of_represents_of_local_proper : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  intro S Z z r H u hu hloc
  choose W hsW T y π hπ hy hT using hloc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) W ?_ ?_
  · rw [eq_top_iff]
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hsW s⟩
  intro s
  set V : H.Opens := u.1 ⁻¹ᵁ W s
  have hx1 : (HPt.map V.ι u).1 = (u.1 ∣_ W s) ≫ (W s).ι := by
    change V.ι ≫ u.1 = _
    rw [morphismRestrict_ι]
  obtain ⟨φ, hφ, -⟩ := hT s V (HPt.map V.ι u) (u.1 ∣_ W s) hx1
  obtain ⟨ψ, hψ, -⟩ := hu (T s) (y s)
  have hψ1 : ψ ≫ u.1 = π s ≫ (W s).ι := by
    rw [← hy s, ← hψ]; rfl
  have hrange : Set.range ψ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change u.1 (ψ t) ∈ W s
    have : u.1 (ψ t) = (W s).ι (π s t) := by
      rw [← Scheme.Hom.comp_apply, hψ1, Scheme.Hom.comp_apply]
    rw [this]
    exact ((π s) t).2
  let ψ' : T s ⟶ V := IsOpenImmersion.lift V.ι ψ hrange
  have hψ' : ψ' ≫ V.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have h1 : ψ' ≫ φ = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hT s (T s) (y s) (π s) (hy s)
    have e1 : HPt.map (ψ' ≫ φ) (y s) = y s := by
      rw [HPt.map_comp, hφ, ← HPt.map_comp, hψ', hψ]
    have e2 : HPt.map (𝟙 (T s)) (y s) = y s := HPt.map_id _
    exact (hc _ e1).trans (hc _ e2).symm
  have h2 : φ ≫ ψ' = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hu V (HPt.map V.ι u)
    have e1 : HPt.map ((φ ≫ ψ') ≫ V.ι) u = HPt.map V.ι u := by
      rw [Category.assoc, hψ', HPt.map_comp, hψ, hφ]
    have e2 := (hc _ e1).trans (hc _ rfl).symm
    rw [← cancel_mono V.ι, e2, Category.id_comp]
  have hiso : IsIso φ := ⟨⟨ψ', h2, h1⟩⟩
  have hcomp : φ ≫ π s = u.1 ∣_ W s := by
    rw [← cancel_mono (W s).ι, Category.assoc, ← hy s, ← hx1, ← hφ]
    rfl
  rw [← hcomp]
  haveI := hπ s
  infer_instance

end GlobalTheory.HilbGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocalStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  first | (exact @GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (exact GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (intros; apply GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrict
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem ker_comap_eq_ker_iff {X X' V V' : Scheme.{0}} (m : X' ⟶ X) (v : V ⟶ X) [IsClosedImmersion v]
    (v' : V' ⟶ X') [IsClosedImmersion v'] :
    v.ker.comap m = v'.ker ↔ ∃ w : V' ⟶ V, IsPullback v' w m v := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [comap_eq_ker_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ inv v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso (inv v.toImage)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso v.toImage) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]

variable {S Z : Scheme.{0}} (z : Z ⟶ S) (W : S.Opens)

lemma isPullback_restrict {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    IsPullback (pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι) (pullback.snd (z ∣_ W) b) z (b ≫ W.ι) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback (z ∣_ W) b) (isPullback_morphismRestrict z W).flip

def restrictIso {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) : pullback (z ∣_ W) b ≅ pullback z (b ≫ W.ι) :=
  (isPullback_restrict z W b).isoPullback

@[reassoc (attr := simp)]
lemma restrictIso_hom_fst {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.fst z (b ≫ W.ι) = pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι :=
  (isPullback_restrict z W b).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma restrictIso_hom_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.snd z (b ≫ W.ι) = pullback.snd (z ∣_ W) b :=
  (isPullback_restrict z W b).isoPullback_hom_snd

lemma restrictIso_inv_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).inv ≫ pullback.snd (z ∣_ W) b = pullback.snd z (b ≫ W.ι) := by
  rw [Iso.inv_comp_eq, restrictIso_hom_snd]

lemma restrictIso_natural {Y H : Scheme.{0}} (b : Y ⟶ W.toScheme) (h : H ⟶ W.toScheme) (c : Y ⟶ H)
    (hc : c ≫ h = b) (w : c ≫ h ≫ W.ι = b ≫ W.ι) :
    pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp) (by rw [Category.comp_id, hc]) ≫
      (restrictIso z W h).hom = (restrictIso z W b).hom ≫ bc z c (h ≫ W.ι) (b ≫ W.ι) w := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_fst_assoc, restrictIso_hom_fst]
  · simp only [bc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_snd_assoc, restrictIso_hom_snd]

theorem isHilbRep_restrict_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens),
    GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  intro S Z z r W hR
  obtain ⟨H, h, U, u, hprop, hcl, hfin, hflat, hrk, huniv⟩ := hR
  haveI := hcl
  have hv : IsFinFlatRk ((u ≫ (restrictIso z W h).hom) ≫ pullback.snd z (h ≫ W.ι)) r := by
    rw [Category.assoc, restrictIso_hom_snd]
    exact ⟨hfin, hflat, hrk⟩
  set y := mkPt (h ≫ W.ι) (u ≫ (restrictIso z W h).hom) hv with hy
  refine ⟨H, y, h, hprop, rfl, ?_⟩
  intro Y x b hx
  obtain ⟨g, J⟩ := x
  change g = b ≫ W.ι at hx
  subst hx
  set v' := J.1.subschemeι ≫ (restrictIso z W b).inv with hv'
  have e : v' ≫ pullback.snd (z ∣_ W) b = J.1.subschemeι ≫ pullback.snd z (b ≫ W.ι) := by
    rw [hv', Category.assoc, restrictIso_inv_snd]
  have key : ∀ c : Y ⟶ H, HPt.map c y = ⟨b ≫ W.ι, J⟩ ↔ ∃ hf : c ≫ h = b, ∃ w : J.1.subscheme ⟶ U,
      IsPullback v' w (pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf])) u := by
    intro c
    constructor
    · intro hc
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := congrArg Sigma.fst hc
      have hf : c ≫ h = b := by
        rw [← cancel_mono W.ι, Category.assoc]
        exact h1
      refine ⟨hf, ?_⟩
      rw [HPt.map_eq_mk_iff c y h1] at hc
      have hc' : (u ≫ (restrictIso z W h).hom).ker.comap (bc z c (h ≫ W.ι) (b ≫ W.ι) h1) =
          J.1.subschemeι.ker := hc.trans (Scheme.IdealSheafData.ker_subschemeι _).symm
      obtain ⟨w, hw⟩ := (ker_comap_eq_ker_iff _ _ _).1 hc'
      refine ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b).symm (Iso.refl _) (restrictIso z W h).symm
        ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · simp only [Iso.symm_hom]
        rw [Iso.comp_inv_eq, Category.assoc, restrictIso_natural z W b h c hf h1, Iso.inv_hom_id_assoc]
      · simp
    · rintro ⟨hf, w, hw⟩
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := by rw [← Category.assoc, hf]
      rw [HPt.map_eq_mk_iff c y h1]
      refine (?_ : _ = J.1.subschemeι.ker).trans (Scheme.IdealSheafData.ker_subschemeι _)
      refine (ker_comap_eq_ker_iff _ (u ≫ (restrictIso z W h).hom) _).2 ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b) (Iso.refl _) (restrictIso z W h) ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · exact restrictIso_natural z W b h c hf h1
      · simp
  have hJ := J.2
  rw [← e] at hJ
  obtain ⟨f, hfP, huniq⟩ := huniv Y b _ v' inferInstance hJ.1 hJ.2.1 hJ.2.2
  exact ⟨f, (key f).2 hfP, fun c hc => huniq c ((key c).1 hc)⟩

end GlobalTheory.HilbGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrictStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens), GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  first | exact @GlobalTheory.HilbGlue.isHilbRep_restrict_local | exact GlobalTheory.HilbGlue.isHilbRep_restrict_local | (intros; apply GlobalTheory.HilbGlue.isHilbRep_restrict_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCover
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

set_option autoImplicit false

namespace GlobalTheory.HilbGlue

theorem idealSheaf_ext_of_openImmersions {P : Scheme.{0}} {ι : Type*} {X : ι → Scheme.{0}}
    (f : ∀ i, X i ⟶ P) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : P, ∃ i y, f i y = x)
    (I J : P.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Σ i, (X i).affineOpens)
    (fun a => ⟨f a.1 ''ᵁ a.2.1, a.2.2.image_of_isOpenImmersion (f a.1)⟩) ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨W, hW, hyW⟩ : ∃ W : (X i).Opens, IsAffineOpen W ∧ y ∈ W := by
      obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ := (X i).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ y) isOpen_univ
      exact ⟨W, hW, hy⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, W, hW⟩, ⟨y, hyW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun K : (X i).IdealSheafData => K.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbGlue

theorem GlobalTheory.HilbGlue.HPt.ext_openCover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  intro S Z z r Y 𝒰 x x' e
  obtain ⟨g, I⟩ := x
  obtain ⟨g', I'⟩ := x'
  obtain rfl : g = g' := 𝒰.hom_ext _ _ fun i => congrArg Sigma.fst (e i)
  rw [HPt.mk_eq_mk_iff]
  have hP : ∀ i : 𝒰.I₀, IsPullback (pullback.snd z (𝒰.f i ≫ g)) (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) (𝒰.f i)
      (pullback.snd z g) := fun i => (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).flip
  haveI : ∀ i : 𝒰.I₀, IsOpenImmersion (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i) inferInstance
  refine idealSheaf_ext_of_openImmersions (ι := 𝒰.I₀) (X := fun i => pullback z (𝒰.f i ≫ g)) (fun i => bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) ?_ I.1 I'.1 fun i => ?_
  · intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (pullback.snd z g x)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd z g)
      (g := 𝒰.f i) x y hy.symm
    refine ⟨i, (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]
  · have := (HPt.mk_eq_mk_iff _ _).1 (e i)
    exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCoverStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_point_eq_of_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  first | exact @GlobalTheory.HilbGlue.HPt.ext_openCover | exact GlobalTheory.HilbGlue.HPt.ext_openCover | (intros; apply GlobalTheory.HilbGlue.HPt.ext_openCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCover
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

section
variable {S Z : Scheme.{0}} (z : Z ⟶ S)

theorem bc_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.fst z g = pullback.fst z k := by
  simp only [bc, pullback.map, pullback.lift_fst, Category.comp_id]

theorem bc_snd {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.snd z g = pullback.snd z k ≫ c := by
  simp only [bc, pullback.map, pullback.lift_snd]

end

theorem isFinFlatRk_of_cover {V Y : Scheme.{0}} (g : V ⟶ Y) (𝒰 : Y.OpenCover) (r : ℕ)
    (h : ∀ i, ∃ (Q : Scheme.{0}) (p : Q ⟶ V) (q : Q ⟶ 𝒰.X i), IsPullback p q g (𝒰.f i) ∧ IsFinFlatRk q r) :
    IsFinFlatRk g r := by
  choose Q p q hP hq using h
  have i1 : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have i2 : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have hq' : ∀ i, IsFinFlatRk (pullback.snd g (𝒰.f i)) r := fun i => by
    rw [← (hP i).isoPullback_inv_snd]
    exact (hq i).iso_comp _
  have hF : IsFinite g := IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰 fun i => (hq' i).1
  have hL : Flat g := IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰 fun i => (hq' i).2.1
  refine ⟨hF, hL, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
  rw [← Scheme.Hom.finrank_of_isPullback (p i) (q i) g (𝒰.f i) (hP i) y', (hq i).2.2]

theorem HPt.exists_glue : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  intro S Z z r Y 𝒰 x hx
  obtain ⟨f, hf⟩ : ∃ f : Y ⟶ S, ∀ i, 𝒰.f i ≫ f = (x i).1 :=
    ⟨𝒰.glueMorphisms (fun i => (x i).1) fun i j =>
      congrArg Sigma.fst (hx i j _ _ _ pullback.condition), fun i => 𝒰.ι_glueMorphisms _ _ i⟩
  let e : ∀ i, pullback z (x i).1 ⟶ pullback z f := fun i => bc z (𝒰.f i) f (x i).1 (hf i)
  have hP : ∀ i, IsPullback (e i) (pullback.snd z (x i).1) (pullback.snd z f) (𝒰.f i) :=
    fun i => isPullback_bc z _ _ _ (hf i)
  have he : ∀ i, IsOpenImmersion (e i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i).flip inferInstance
  have hcov : ∀ p : ↥(pullback z f), ∃ i, p ∈ Set.range (e i) := by
    intro p
    obtain ⟨i, y', hy'⟩ := 𝒰.exists_eq (pullback.snd z f p)
    obtain ⟨q, hq⟩ : p ∈ Set.range (pullback.fst (pullback.snd z f) (𝒰.f i)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y', hy'⟩
    refine ⟨i, (hP i).isoPullback.inv q, ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, (hP i).isoPullback_inv_fst]
  have fi : ∀ i, e i ≫ pullback.fst z f = pullback.fst z (x i).1 := fun i => by
    simp only [e, bc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hK : ∀ i j (Q : Scheme.{0}) (a : Q ⟶ pullback z (x i).1) (b : Q ⟶ pullback z (x j).1),
      a ≫ e i = b ≫ e j → (x i).2.1.comap a = (x j).2.1.comap b := by
    intro i j Q a b hab
    have hbc : (a ≫ pullback.snd z (x i).1) ≫ 𝒰.f i = (b ≫ pullback.snd z (x j).1) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← (hP i).w, ← (hP j).w, reassoc_of% hab]
    have H := hx i j Q _ _ hbc
    have w : (a ≫ pullback.snd z (x i).1) ≫ (x i).1 = (b ≫ pullback.snd z (x j).1) ≫ (x j).1 :=
      congrArg Sigma.fst H
    have H' := (HPt.map_eq_mk_iff _ (x i) w ((x j).2.pull _ rfl)).1 H
    have hs : (a ≫ pullback.fst z (x i).1) ≫ z = 𝟙 Q ≫ (b ≫ pullback.snd z (x j).1) ≫ (x j).1 := by
      rw [Category.id_comp, ← w, Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨s, hs1, hs2⟩ : ∃ s : Q ⟶ pullback z ((b ≫ pullback.snd z (x j).1) ≫ (x j).1),
        s ≫ pullback.fst _ _ = a ≫ pullback.fst z (x i).1 ∧ s ≫ pullback.snd _ _ = 𝟙 Q :=
      ⟨pullback.lift _ _ hs, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hfst : a ≫ pullback.fst z (x i).1 = b ≫ pullback.fst z (x j).1 := by
      rw [← fi i, ← fi j, reassoc_of% hab]
    have ha : a = s ≫ bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have hb : b = s ≫ bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1, hfst]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have e1 : (x i).2.1.comap a = ((x i).2.1.comap (bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← ha]
    have e2 : (x j).2.1.comap b = ((x j).2.1.comap (bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← hb]
    rw [e1, e2, H']
    rfl
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions GlobalTheory.T.exists_idealSheafData_of_compatible_ideals (ι := 𝒰.I₀) (fun i : 𝒰.I₀ => pullback z (x i).1) e he hcov (fun i : 𝒰.I₀ => (x i).2.1) hK
  have hfr : IsFinFlatRk (I.subschemeι ≫ pullback.snd z f) r := by
    refine isFinFlatRk_of_cover _ 𝒰 r fun i => ⟨(I.comap (e i)).subscheme, _, _,
      (isPullback_comap I (e i)).flip.paste_vert (hP i), ?_⟩
    have := (x i).2.2
    rw [← hI i] at this
    exact this
  refine ⟨⟨f, I, hfr⟩, fun i => ?_⟩
  exact (HPt.map_eq_mk_iff (𝒰.f i) ⟨f, I, hfr⟩ (hf i) (x i).2).2 (hI i)

end GlobalTheory.HilbGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCoverStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_point_glue_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  first | (exact @GlobalTheory.HilbGlue.HPt.exists_glue) | (exact GlobalTheory.HilbGlue.HPt.exists_glue) | (intros; apply GlobalTheory.HilbGlue.HPt.exists_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue Opposite

theorem GlobalTheory.HilbGlue.isSheaf_hilbFunctor {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbFunctor z r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (GlobalTheory.T.hilbert_point_glue_open_cover z r Y 𝒰 x fun i j R b c h => hx i j R b c h)
    fun y y' h h' => GlobalTheory.T.hilbert_point_eq_of_open_cover z r Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem GlobalTheory.HilbGlue.isHilbRep_of_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z →
    LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) →
    IsHilbRep z r := by
  intro S Z z _ _ _ r hS
  have hloc : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, HPt.map c y = x := fun s => by
    obtain ⟨W, hs, hW⟩ := hS s
    exact ⟨W, hs, GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict z r W hW⟩
  have hloc' := hloc
  choose W hsW T y π _ hπ huniq using hloc
  have hrep : (hilbFunctor z r).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover (hilbFunctor z r) (GlobalTheory.HilbGlue.isSheaf_hilbFunctor z r) (hilbProj z r) W
      (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsW s⟩) T y π hπ huniq
  obtain ⟨H, u, hu⟩ : ∃ (H : Scheme.{0}) (u : HPt z r H), ∀ (T : Scheme.{0}) (x : HPt z r T),
      ∃! c : T ⟶ H, HPt.map c u = x := by
    obtain ⟨H, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {T : Scheme.{0}} (c : T ⟶ H), HPt.map c (e.homEquiv (𝟙 H)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨H, e.homEquiv (𝟙 H), fun T x => ⟨e.homEquiv.symm x, (h _).trans (e.homEquiv.apply_symm_apply x),
      fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  have hprop : IsProper u.1 := GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local z r H u hu hloc'
  obtain ⟨h, I⟩ := u
  refine ⟨H, h, I.1.subscheme, I.1.subschemeι, hprop, inferInstance, I.2.1, I.2.2.1, I.2.2.2, ?_⟩
  intro T g V v _ h1 h2 h3
  have hv' : IsFinFlatRk (v ≫ pullback.snd z g) r := ⟨h1, h2, h3⟩
  obtain ⟨c, hc, hcu⟩ := hu T (mkPt g v hv')
  have key : ∀ (f : T ⟶ H) (hf : f ≫ h = g), HPt.map f ⟨h, I⟩ = mkPt g v hv' ↔
      ∃ w : V ⟶ I.1.subscheme, IsPullback v w (bc z f h g hf) I.1.subschemeι := by
    intro f hf
    rw [mkPt, HPt.map_eq_mk_iff f ⟨h, I⟩ hf]
    exact GlobalTheory.HilbGlue.comap_eq_ker_iff (bc z f h g hf) I.1 v
  have hcg : c ≫ h = g := congrArg Sigma.fst hc
  exact ⟨c, ⟨hcg, (key c hcg).1 hc⟩, fun f ⟨hf, hw⟩ => hcu f ((key f hf).2 hw)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCoverStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) → IsHilbRep z r := by
  first | (exact @GlobalTheory.HilbGlue.isHilbRep_of_cover) | (exact GlobalTheory.HilbGlue.isHilbRep_of_cover) | (intros; apply GlobalTheory.HilbGlue.isHilbRep_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def transferMap {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ⟶ pullback z g :=
  pullback.map z' g' z g eZ.hom (𝟙 T) eS.hom hsq.symm (by rw [Category.id_comp, hg])

instance {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    IsIso (transferMap z z' eS eZ hsq g' g hg) := by
  unfold transferMap; infer_instance

def transferIso {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ≅ pullback z g :=
  asIso (transferMap z z' eS eZ hsq g' g hg)

lemma transferIso_hom_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).hom ≫ pullback.snd z g = pullback.snd z' g' := by
  simp only [transferIso, asIso_hom, transferMap]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma transferIso_inv_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).inv ≫ pullback.snd z' g' = pullback.snd z g := by
  rw [Iso.inv_comp_eq, transferIso_hom_snd]

lemma transferIso_map {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T H : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g)
    (h' : H ⟶ S') (f : T ⟶ H) (hf' : f ≫ h' = g') (hf : f ≫ (h' ≫ eS.hom) = g) :
    pullback.map z' g' z' h' (𝟙 Z') f (𝟙 S') (by simp) (by rw [Category.comp_id, hf'])
        ≫ (transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl).hom =
      (transferIso z z' eS eZ hsq g' g hg).hom ≫
        pullback.map z g z (h' ≫ eS.hom) (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf]) := by
  simp only [transferIso, asIso_hom, transferMap, pullback.map]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem isHilbRep_transfer : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z),
    eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  intro S Z S' Z' z z' eS eZ hsq r hrep
  obtain ⟨H, h', U, u', hP, hC, hF, hFl, hR, hU⟩ := hrep
  set ΦH := transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl with hΦH
  have eu : (u' ≫ ΦH.hom) ≫ pullback.snd z (h' ≫ eS.hom) = u' ≫ pullback.snd z' h' := by
    rw [Category.assoc, transferIso_hom_snd]
  refine ⟨H, h' ≫ eS.hom, U, u' ≫ ΦH.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [eu]; exact hF
  · rw [eu]; exact hFl
  · rw [eu]; exact hR
  intro T g V v hv hvF hvFl hvR
  have hg : (g ≫ eS.inv) ≫ eS.hom = g := by simp
  set ΦT := transferIso z z' eS eZ hsq (g ≫ eS.inv) g hg with hΦT
  have ev : (v ≫ ΦT.inv) ≫ pullback.snd z' (g ≫ eS.inv) = v ≫ pullback.snd z g := by
    rw [Category.assoc, transferIso_inv_snd]
  have hv' : IsClosedImmersion (v ≫ ΦT.inv) := inferInstance
  obtain ⟨f, ⟨hf', w, hpb⟩, huniq⟩ := hU T (g ≫ eS.inv) V (v ≫ ΦT.inv) hv' (by rw [ev]; exact hvF)
    (by rw [ev]; exact hvFl) (by rw [ev]; exact hvR)
  have hf : f ≫ (h' ≫ eS.hom) = g := by rw [← Category.assoc, hf', hg]
  refine ⟨f, ⟨hf, w, ?_⟩, ?_⟩
  · refine hpb.of_iso (Iso.refl _) ΦT (Iso.refl _) ΦH ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f hf' hf
    · simp
  · rintro f₂ ⟨hf₂, w₂, hpb₂⟩
    have hf₂' : f₂ ≫ h' = g ≫ eS.inv := by rw [← hf₂]; simp
    apply huniq f₂ ⟨hf₂', w₂, ?_⟩
    refine hpb₂.of_iso (Iso.refl _) ΦT.symm (Iso.refl _) ΦH.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
        transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f₂ hf₂' hf₂, Iso.inv_hom_id_assoc]
    · simp [hΦH]

end GlobalTheory.HilbertSch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIsoStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_iso : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z), eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  first | exact @GlobalTheory.HilbertSch.isHilbRep_transfer | exact GlobalTheory.HilbertSch.isHilbRep_transfer | (intros; apply GlobalTheory.HilbertSch.isHilbRep_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePrope
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem main : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro S Z z hfin hflat hlfp r
  refine GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover S Z z hfin hflat hlfp r fun s => ?_
  obtain ⟨W, A, B, _, _, _, _, _, eW, eZ, hs, hc⟩ := GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat S Z z hfin hflat hlfp s
  refine ⟨W, hs, GlobalTheory.T.isHilbertSchemeRepresentable_of_iso (z ∣_ W) (Spec.map (CommRingCat.ofHom (algebraMap A B))) eW.symm eZ.symm ?_ r
    (GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists A B r)⟩
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end GlobalTheory.HilbertSch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePropeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbertSch.main) | (exact GlobalTheory.HilbertSch.main) | (intros; apply GlobalTheory.HilbertSch.main <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsOpenImmersionOfClosedImmersionFlatEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale :
    ∀ {V X T : Scheme.{0}} (v : V ⟶ X) (p : X ⟶ T), Etale p → IsClosedImmersion v → Flat (v ≫ p) → LocallyOfFinitePresentation (v ≫ p) → IsOpenImmersion v := by
  intro V X T v p hp hv hf hl
  have hv' : FormallyUnramified v := inferInstance
  have hu : FormallyUnramified (v ≫ p) :=
    MorphismProperty.comp_mem @FormallyUnramified v p hv' inferInstance
  have he : Etale (v ≫ p) := Etale.of_formallyUnramified_of_flat (v ≫ p)
  have hev : Etale v := Etale.of_comp v p
  exact IsOpenImmersion.of_flat_of_mono v
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.exists_isPullback_iff_preimage {V₀ X' U₀ X : Scheme.{0}} (v : V₀ ⟶ X') (m : X' ⟶ X) (u : U₀ ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion u] :
    (∃ w, IsPullback v w m u) ↔ m ⁻¹ᵁ u.opensRange = v.opensRange := by
  constructor
  · rintro ⟨w, hw⟩
    ext x
    change x ∈ m ⁻¹' Set.range u ↔ x ∈ Set.range v
    rw [← Scheme.Pullback.range_fst]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨hw.isoPullback.inv b, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_inv_fst]
    · rintro ⟨a, rfl⟩
      refine ⟨hw.isoPullback.hom a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_hom_fst]
  · intro h
    have hr : Set.range v = Set.range (pullback.fst m u) := by
      rw [Scheme.Pullback.range_fst]
      have := congrArg (fun O : X'.Opens => (O : Set X')) h
      exact this.symm
    let e := IsOpenImmersion.isoOfRangeEq v (pullback.fst m u) hr
    refine ⟨e.hom ≫ pullback.snd m u, IsPullback.of_iso_pullback ⟨?_⟩ e ?_ rfl⟩
    · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr, Category.assoc,
        pullback.condition, Category.assoc]
    · exact IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr

private lemma UpperTheory.pullback_map_symmetry_whisker {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y) :
    pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp) ≫
        (pullbackSymmetry G.hom Y.hom).hom =
      (pullbackSymmetry G.hom T.hom).hom ≫ (y ▷ G).left := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_snd]
    simp
  · erw [pullback.lift_fst]
    simp

private lemma UpperTheory.isPullback_transport_symmetry {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y)
    (V : (T ⊗ G).left.Opens) {U₀ : Scheme.{0}} (u : U₀ ⟶ pullback G.hom Y.hom) (w : (V : Scheme.{0}) ⟶ U₀) :
    IsPullback (V.ι ≫ (pullbackSymmetry G.hom T.hom).inv) w
        (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp)) u ↔
      IsPullback V.ι w (y ▷ G).left (u ≫ (pullbackSymmetry G.hom Y.hom).hom) := by
  have hsq := UpperTheory.pullback_map_symmetry_whisker (G := G) y
  constructor
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom) (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact hsq
    · simp
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom).symm (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom).symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp

theorem UpperTheory.exists_clopRepOfRank_of_locallyNoetherian :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∀ r : ℕ, ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.RepOfRank r G Y U := by
  intro S _ G hfin het r
  obtain ⟨H, h, U₀, u, hprop, hcl, hfin', hflat', hrk, huniv⟩ :=
    GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper S G.left G.hom hfin inferInstance inferInstance r
  haveI := hprop
  haveI := hcl
  haveI := hfin'
  haveI := hflat'
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : Etale (pullback.snd G.hom h) := inferInstance
  haveI : IsOpenImmersion u :=
    UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale u (pullback.snd G.hom h) inferInstance hcl hflat' inferInstance
  let Y : Over S := Over.mk h
  let ι₀ : U₀ ⟶ (Y ⊗ G).left := u ≫ (pullbackSymmetry G.hom Y.hom).hom
  haveI : IsOpenImmersion ι₀ := by dsimp [ι₀]; infer_instance
  haveI : IsClosedImmersion ι₀ := by dsimp [ι₀]; infer_instance
  refine ⟨Y, ι₀.opensRange, ?_, ?_, ?_⟩
  · exact ι₀.isClosedEmbedding.isClosed_range
  · intro y
    have hp : UpperTheory.RepresentationRank.proj ι₀.opensRange = ι₀.isoOpensRange.inv ≫ (u ≫ pullback.snd G.hom h) := by
      rw [Iso.eq_inv_comp]
      change ι₀.isoOpensRange.hom ≫ (ι₀.opensRange.ι ≫ pullback.fst Y.hom G.hom) = _
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      simp [ι₀, Y]
    rw [hp, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk y
  · intro T V hV hVr
    obtain ⟨hVF, hVE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV
    haveI := hVF
    haveI := hVE
    let v : (V : Scheme.{0}) ⟶ pullback G.hom T.hom := V.ι ≫ (pullbackSymmetry G.hom T.hom).inv
    haveI : IsClosedImmersion V.ι :=
      IsClosedImmersion.of_isPreimmersion V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
    haveI : IsClosedImmersion v := by dsimp [v]; infer_instance
    have hvp : v ≫ pullback.snd G.hom T.hom = UpperTheory.RepresentationRank.proj V := by
      simp [v, UpperTheory.RepresentationRank.proj]
    haveI : IsFinite (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; exact hVF
    haveI : Flat (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; infer_instance
    obtain ⟨f, ⟨hf, w, hw⟩, huniq⟩ := huniv T.left T.hom V v inferInstance inferInstance
      inferInstance (fun t => by rw [hvp]; exact hVr t)
    have key : ∀ y' : T ⟶ Y, ((y' ▷ G).left ⁻¹ᵁ ι₀.opensRange = V ↔
        ∃ w, IsPullback v w
          (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y'.left (𝟙 S) (by simp) (by simp)) u) := by
      intro y'
      have h1 := UpperTheory.exists_isPullback_iff_preimage V.ι (y' ▷ G).left ι₀
      rw [Scheme.Opens.opensRange_ι] at h1
      rw [← h1]
      exact exists_congr fun w => (UpperTheory.isPullback_transport_symmetry y' V u w).symm
    refine ⟨Over.homMk f hf, (key _).mpr ⟨w, hw⟩, ?_⟩
    intro y' hy'
    obtain ⟨w', hw'⟩ := (key y').mp hy'
    exact Over.OverMorphism.ext (huniq y'.left ⟨Over.w y', w', hw'⟩)

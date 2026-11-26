module

public import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
public import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChasePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.StepSPf

namespace LateralTheory.E.ChasePf

theorem pp_comp {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (hfg : f ≫ g = h) (y : H R (sch.obj C) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map h) F n y := by
  rw [← pull_comp, ← Functor.map_comp, hfg]

theorem pp_id {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A : Scheme.{0}} {f : A ⟶ A} (hf : f = 𝟙 A)
    (y : H R (sch.obj A) F n) : pull R (sch.map f) F n y = y := by
  rw [hf, CategoryTheory.Functor.map_id, pull_id]

def psi {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) : pullback A.ι B.ι ≅ C.toScheme :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst A.ι B.ι ≫ A.ι) C.ι (by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hC]; rfl)

@[reassoc (attr := simp)]
theorem psi_hom_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).hom ≫ C.ι = pullback.fst A.ι B.ι ≫ A.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem psi_inv_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.fst A.ι B.ι ≫ A.ι = C.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc (attr := simp)]
theorem psi_inv_snd {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.snd A.ι B.ι ≫ B.ι = C.ι := by
  rw [← pullback.condition, psi_inv_fst]

theorem cover2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) (hAB : A ⊔ B = ⊤) :
    Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ A)).ι ∪ Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ B)).ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  refine Set.eq_univ_of_forall fun y => ?_
  have : ψ.base (φ.base y) ∈ A ⊔ B := by rw [hAB]; trivial
  simpa using this

theorem inf2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) :
    φ ⁻¹ᵁ (ψ ⁻¹ᵁ (A ⊓ B)) = φ ⁻¹ᵁ (ψ ⁻¹ᵁ A) ⊓ φ ⁻¹ᵁ (ψ ⁻¹ᵁ B) := by
  ext; simp

section
variable {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens)

abbrev rL {k : J} (f : k ⟶ j0) : (c.π.app j0 ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, c.w])

abbrev rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    (D.map f' ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map f' ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, h])

theorem rL_rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    rL D c j0 W f' ≫ rT D j0 W g f f' h = rL D c j0 W f := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp [rL, rT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

end

theorem pp3' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' C' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g' ≫ k') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n (pull R (sch.map k') F n y)) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp3 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {l : A ⟶ E} (h : f ≫ g ≫ k = l) (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) = pull R (sch.map l) F n y := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp2' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp32 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp24 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' C' E' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E'} {l' : E' ⟶ E} (h : f ≫ g = f' ≫ g' ≫ k' ≫ l')
    (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n
      (pull R (sch.map k') F n (pull R (sch.map l') F n y))) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem Chase_of : DiagramChase₂ := by
  intro hH hmv q J _ _ D c hc ha hcs hqs hu j0 X e U V hUV pU pV pW n i
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  intro x
  obtain ⟨δ, hex, hnat⟩ := hmv hH (ZMod q) (tw q i)
  have cov : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι ∪ Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι = Set.univ :=
    fun φ => cover2 φ e.hom U V hUV
  have hinf : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      φ ⁻¹ᵁ (e.hom ⁻¹ᵁ (U ⊓ V)) = φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U) ⊓ φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V) :=
    fun φ => inf2 φ e.hom U V

  obtain ⟨k1, f1, a1, ha1⟩ := (pU (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x)
  obtain ⟨k2, f2, b1, hb1⟩ := (pV (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x)
  obtain ⟨k3, g1, g2, hg⟩ := IsCofiltered.cospan f1 f2

  obtain ⟨a2, ha2d⟩ : ∃ a2, a2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g1 f1 (g1 ≫ f1) rfl)) (tw q i) (m + 1) a1 :=
    ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b2, b2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g2 f2 (g1 ≫ f1) hg.symm)) (tw q i) (m + 1) b1 :=
    ⟨_, rfl⟩
  have ha2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1))) (tw q i) (m + 1) a2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x := by
    rw [ha2d, pp_comp (rL_rT D c j0 _ g1 f1 _ rfl)]; exact ha1
  have hb2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1))) (tw q i) (m + 1) b2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x := by
    rw [hb2d, pp_comp (rL_rT D c j0 _ g2 f2 _ hg.symm)]; exact hb1

  obtain ⟨dC, hdC⟩ : ∃ dC, dC = pull _ (sch.map (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv) (tw q i) (m + 1)
      (pull _ (sch.map (pullback.fst _ _)) _ _ a2 - pull _ (sch.map (pullback.snd _ _)) _ _ b2) := ⟨_, rfl⟩
  have hd : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) (g1 ≫ f1))) (tw q i) (m + 1) dC = 0 := by
    rw [hdC, map_sub, map_sub,
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.fst _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1)) (by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
        all_goals simp [← Category.assoc, psi_inv_fst, pullback.condition]),
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.snd _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1)) (by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
        all_goals simp [← Category.assoc, psi_inv_fst, pullback.condition]),
      ha2, hb2, pp3 (psi_inv_fst _ _ _ _), pp3 (psi_inv_snd _ _ _ _), sub_self]
  obtain ⟨k4, g4, hk4⟩ := (pW (m + 1) i).2 k3 (g1 ≫ f1) dC hd

  obtain ⟨a3, ha3d⟩ : ∃ a3, a3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) a2 := ⟨_, rfl⟩
  obtain ⟨b3, hb3d⟩ : ∃ b3, b3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) b2 := ⟨_, rfl⟩
  have hab : pull _ (sch.map (pullback.fst _ _)) _ _ a3 = pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
      (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 := by
    have key : pull _ (sch.map (pullback.fst _ _)) _ _ a3 - pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
        (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 =
        pull _ (sch.map (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom) _ _
          (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl)) _ _ dC) := by
      have E3 : (pullback.fst (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.fst (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
      have E4 : (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.snd (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
      rw [hdC, ha3d, hb3d]; simp only [map_sub]; rw [pp24 E3, pp24 E4]
    rw [hk4, map_zero] at key
    exact sub_eq_zero.mp key
  obtain ⟨xk, hxa, hxb⟩ := (hex (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (cov _) (m + 1)).1 a3 b3 hab

  obtain ⟨x', hx'⟩ : ∃ x' : Ht q (sch.obj c.pt) (m + 1) i, x' = x -
      (show Ht q (sch.obj c.pt) (m + 1) i from pull _ (sch.map (c.π.app k4)) (tw q i) (m + 1) xk) := ⟨_, rfl⟩
  have h1 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) (by simp [rL]), hxa, ha3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), ha2, sub_self]
  have h2 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) (by simp [rL]), hxb, hb3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), hb2, sub_self]
  obtain ⟨w, hw⟩ := ((hex (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) m).2.2 x').mp
    ⟨h1, h2⟩

  obtain ⟨k5, f5, w5, hw5⟩ := (pW m i).1 (pull _ (sch.map (psi _ _ _ (hinf (c.π.app j0))).inv) _ _ w)
  obtain ⟨k6, h4, h5, hh⟩ := IsCofiltered.cospan (g4 ≫ g1 ≫ f1) f5
  obtain ⟨w6, hw6⟩ : ∃ w6, w6 = pull _ (sch.map (psi _ _ _ (hinf (D.map (h4 ≫ g4 ≫ g1 ≫ f1)))).hom) (tw q i) m
      (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) h5 f5 (h4 ≫ g4 ≫ g1 ≫ f1) hh.symm)) _ _ w5) := ⟨_, rfl⟩
  have hn := hnat (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) (cov _)
    (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6)
    (by simp [rL]) (by simp [rL]) m w6
  have hpb : pull _ (sch.map (pullback.map _ _ _ _ (rL D c j0 (e.hom ⁻¹ᵁ U) (h4 ≫ g4 ≫ g1 ≫ f1))
      (rL D c j0 (e.hom ⁻¹ᵁ V) (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6) (by simp [rL]) (by simp [rL]))) (tw q i) m w6 = w := by
    rw [hw6, pp32 (f' := (psi _ _ _ (hinf (c.π.app j0))).hom) (g' := rL D c j0 _ f5) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp only [Category.assoc, rT, rL, Scheme.Hom.resLE_comp_ι, psi_hom_fst_assoc]
      simp [Scheme.Hom.resLE_comp_ι_assoc, Cone.w]), hw5,
      pp_comp (Iso.hom_inv_id _), pp_id rfl]
  refine ⟨k6, δ _ _ m w6 + pull _ (sch.map (D.map h4)) _ _ xk, ?_⟩
  rw [map_add (f := _), ← hn, hpb, hw, pp_comp (c.w h4), hx', sub_add_cancel]

end LateralTheory.E.ChasePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntegralSurjectiveRingCechAugmentationEtaleEqv
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf LateralTheory.E.CechSqPf

namespace LateralTheory.E.CechSqPf

def lev0Iso {C D : CommRingCat.{0}} (g : C ⟶ D) : D ≅ widePushout C (fun _ : Fin 1 => D) (fun _ => g) where
  hom := WidePushout.ι (fun _ => g) 0
  inv := WidePushout.desc g (fun _ => 𝟙 D) (fun _ => by simp)
  hom_inv_id := by apply WidePushout.ι_desc
  inv_hom_id := by
    apply WidePushout.hom_ext
    · intro j
      rw [Subsingleton.elim j 0, ← Category.assoc, WidePushout.ι_desc, Category.comp_id, Category.id_comp]
    · rw [← Category.assoc, WidePushout.head_desc, Category.comp_id]
      convert WidePushout.arrow_ι (fun _ : Fin 1 => g) (0 : Fin 1) using 1

theorem Level0_of (h : LevelPush) : Level0 := by
  intro q i A Y C D Y' φ c w φ' g hpo
  have hp := h φ c w φ' g hpo (SimplexCategory.mk 0)
  refine ⟨_, w ≫ (coAug (pushout.inr g φ')).app (SimplexCategory.mk 0),
    (lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0), ?_, fun m hm => ?_⟩
  · refine hp.of_iso (Iso.refl _) (Iso.refl _) (lev0Iso g).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Iso.symm_hom, Category.assoc]
      change c ≫ WidePushout.head _ ≫ (lev0Iso g).inv = c ≫ g
      rw [← WidePushout.arrow_ι (fun _ : Fin 1 => g) 0]
      change c ≫ (g ≫ (lev0Iso g).hom) ≫ (lev0Iso g).inv = c ≫ g
      simp
    · simp
    · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc (lev0Iso g) _).symm
  · have key : sch.map (Spec.map ((lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))) ≫
        sch.map (Spec.map (lev0Iso g).inv) =
        𝟙 _ ≫ sch.map (Spec.map ((Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))) := by
      have hring : (lev0Iso g).inv ≫ (lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0) =
          (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0) := Iso.inv_hom_id_assoc _ _
      rw [← sch.map_comp, ← Spec.map_comp, Category.id_comp]
      exact congrArg (fun f => sch.map (Spec.map f)) hring
    exact RelZS.of_iso (ZMod q) (tw q i) _ _ (Iso.refl _) (sch.mapIso (asIso (Spec.map (lev0Iso g).inv))) key m hm

theorem arrowι {C D : CommRingCat.{0}} (g : C ⟶ D) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    g ≫ (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) = (coAug g).app n :=
  @WidePushout.arrow_ι _ _ _ C (fun _ => D) (fun _ => g) _ j

theorem basePush {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') (n : SimplexCategory) :
    IsPushout φ' ((coAug g).app n) ((coAug (pushout.inr g φ')).app n)
      ((Arrow.mapCechConerve (sqHom g φ')).app n) := by
  have hw : φ' ≫ (coAug (pushout.inr g φ')).app n =
      (coAug g).app n ≫ (Arrow.mapCechConerve (sqHom g φ')).app n := by
    simp [coAug, sqHom]
    symm; apply WidePushout.head_desc
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => WidePushout.desc s.inl
      (fun j => pushout.desc ((WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫ s.inr) s.inl (by
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s.inr) (arrowι g n j)).trans s.condition.symm)))
      (fun j => pushout.inr_desc _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePushout.head_desc
  · intro s
    apply WidePushout.hom_ext
    · intro j
      have key : (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫
          (Arrow.mapCechConerve (sqHom g φ')).app n = pushout.inl g φ' ≫
          (WidePushout.ι (fun _ : Fin (n.len + 1) => pushout.inr g φ') j :
            _ ⟶ (Arrow.mk (pushout.inr g φ')).cechConerve.obj n) := by
        apply WidePushout.ι_desc
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) key).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      erw [WidePushout.ι_desc]
      exact pushout.inl_desc _ _ _
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) hw.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      erw [WidePushout.head_desc]
      exact s.condition
  · intro s m h1 h2
    apply WidePushout.hom_ext
    · intro j
      apply pushout.hom_ext
      · erw [WidePushout.ι_desc, pushout.inl_desc]
        rw [← h2]
        have key : (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫
            (Arrow.mapCechConerve (sqHom g φ')).app n = pushout.inl g φ' ≫
            (WidePushout.ι (fun _ : Fin (n.len + 1) => pushout.inr g φ') j :
              _ ⟶ (Arrow.mk (pushout.inr g φ')).cechConerve.obj n) := by
          apply WidePushout.ι_desc
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m) key.symm).trans (Category.assoc _ _ _))
      · erw [WidePushout.ι_desc, pushout.inr_desc]
        rw [← h1]
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) (arrowι (pushout.inr g φ') n j))
    · erw [WidePushout.head_desc]
      rw [← h1]
      rfl

theorem LevelPush_of : LevelPush := by
  intro A Y C D Y' φ c w φ' g hpo n
  exact hpo.paste_vert (basePush g φ' n)

theorem integral_surjective_ring_cech_augmentation_etale_eqv : IntegralSurjectiveRingCechAugmentationEtaleEqv := by
  intro hB4 q i C D g hgi hgs hq
  haveI : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hgi
  haveI : Surjective (Spec.map g) := ⟨fun x => by
    obtain ⟨Q, hQ, hQc⟩ := hgs x.asIdeal x.isPrime
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [Spec.map_base]
    exact PrimeSpectrum.ext hQc⟩
  have hq' : IsUnit (q : Γ(Spec C, ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso C).inv.hom
  exact hB4 q (Spec.map g) hq' i

theorem BaseChange_of : BaseChange := by
  intro C D Y' g φ' hgi hgs
  have hp := (isPullback_SpecMap_pushout g φ')
  have hI : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hgi
  have hS : Surjective (Spec.map g) := ⟨fun x => by
    obtain ⟨Q, hQ, hQc⟩ := hgs x.asIdeal x.isPrime
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [Spec.map_base]
    exact PrimeSpectrum.ext hQc⟩
  have hI' : IsIntegralHom (Spec.map (pushout.inr g φ')) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hp hI
  have hS' : Surjective (Spec.map (pushout.inr g φ')) := MorphismProperty.of_isPullback (P := @Surjective) hp hS
  refine ⟨IsIntegralHom.SpecMap_iff.mp hI', fun r hr => ?_⟩
  obtain ⟨y, hy⟩ := hS'.surj ⟨r, hr⟩
  refine ⟨y.asIdeal, y.isPrime, ?_⟩
  have := congrArg PrimeSpectrum.asIdeal hy
  rw [Spec.map_base] at this
  exact this

section helpers
variable {C D : CommRingCat.{0}} (g : C ⟶ D) {J : Type} [HasWidePushout C (fun _ : J => D) (fun _ => g)]

theorem ιd (j : J) {X : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) :
    WidePushout.ι (fun _ : J => g) j ≫ WidePushout.desc f fs w = fs j :=
  WidePushout.ι_desc (arrows := fun _ => g) (f := f) (fs := fs) (w := w) j

theorem hd {X : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) :
    WidePushout.head (fun _ : J => g) ≫ WidePushout.desc f fs w = f :=
  WidePushout.head_desc (arrows := fun _ => g) (f := f) (fs := fs) (w := w)

theorem ar (j : J) : g ≫ WidePushout.ι (fun _ : J => g) j = WidePushout.head (fun _ : J => g) :=
  WidePushout.arrow_ι (arrows := fun _ : J => g) j

theorem ιd_assoc (j : J) {X Y : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) (h : X ⟶ Y) :
    WidePushout.ι (fun _ : J => g) j ≫ WidePushout.desc f fs w ≫ h = fs j ≫ h := by
  rw [← Category.assoc, ιd]

theorem hd_assoc {X Y : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) (h : X ⟶ Y) :
    WidePushout.head (fun _ : J => g) ≫ WidePushout.desc f fs w ≫ h = f ≫ h := by
  rw [← Category.assoc, hd]

end helpers

abbrev up {C D : CommRingCat.{0}} (g : C ⟶ D) (k : ℕ) :
    widePushout C (fun _ : Fin (k + 1) => D) (fun _ => g) ⟶ widePushout C (fun _ : Fin (k + 2) => D) (fun _ => g) :=
  WidePushout.desc (WidePushout.head _) (fun i => WidePushout.ι (fun _ : Fin (k + 2) => g) i.castSucc)
    (fun i => ar g i.castSucc)

theorem wp {C D : CommRingCat.{0}} (g : C ⟶ D) (k : ℕ) :
    IsPushout (WidePushout.head (fun _ : Fin (k + 1) => g)) g (up g k)
      (WidePushout.ι (fun _ : Fin (k + 2) => g) (Fin.last _)) := by
  have hw : WidePushout.head (fun _ : Fin (k + 1) => g) ≫ up g k =
      g ≫ WidePushout.ι (fun _ : Fin (k + 2) => g) (Fin.last _) := by
    simp [up, hd, ar]
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => WidePushout.desc (g ≫ s.inr)
      (fun i => Fin.lastCases s.inr (fun i => WidePushout.ι (fun _ : Fin (k + 1) => g) i ≫ s.inl) i)
      (fun i => by
        induction i using Fin.lastCases with
        | last => simp
        | cast i =>
          simp only [Fin.lastCases_castSucc]
          rw [← Category.assoc, ar]
          exact s.condition)) ?_ ?_ ?_)
  · intro s
    apply WidePushout.hom_ext
    · intro j
      simp [up, ιd, ιd_assoc, hd, hd_assoc]
    · simp [up, ιd, ιd_assoc, hd, hd_assoc]
      exact s.condition.symm
  · intro s
    simp [ιd]
  · intro s m h1 h2
    apply WidePushout.hom_ext
    · intro j
      induction j using Fin.lastCases with
      | last => simpa [ιd] using h2
      | cast i =>
        simp only [WidePushout.ι_desc, Fin.lastCases_castSucc]
        rw [← h1]
        simp [up, ιd, ιd_assoc]
    · simp only [WidePushout.head_desc]
      rw [← h2, ← Category.assoc]
      exact congrArg (· ≫ m) (WidePushout.arrow_ι (fun _ : Fin (k + 2) => g) (Fin.last _)).symm

theorem cechConerve_levelwise : LevelP := by
  intro A P hP C D c g hCc hDc
  have Q : ∀ k : ℕ, P _ (c ≫ WidePushout.head (fun _ : Fin (k + 1) => g)) := by
    intro k
    induction k with
    | zero =>
      have hsq : IsPushout g (𝟙 C) (WidePushout.ι (fun _ : Fin 1 => g) 0) (WidePushout.head (fun _ : Fin 1 => g)) := by
        have : IsIso (WidePushout.ι (fun _ : Fin 1 => g) 0) := (lev0Iso g).isIso_hom
        exact IsPushout.of_vert_isIso ⟨(WidePushout.arrow_ι (fun _ : Fin 1 => g) 0).trans (Category.id_comp _).symm⟩
      have := hP c g (𝟙 C) _ _ hsq hCc hDc (by simpa using hCc)
      rw [WidePushout.arrow_ι (fun _ : Fin 1 => g) 0] at this
      exact this
    | succ k ih =>
      have := hP c _ g _ _ (wp g k) hCc ih hDc
      have e : WidePushout.head (fun _ : Fin (k + 1) => g) ≫ up g k = WidePushout.head (fun _ : Fin (k + 2) => g) :=
        hd g _ _ _
      rw [e] at this
      exact this
  intro n
  exact Q n.len

end LateralTheory.E.CechSqPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DescEqvPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafKunEmptyPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafKunEmptyPf

variable {R : Type} [CommRing R]

theorem sec_sub (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover F U (Scheme.bot_mem_grothendieckTopology U)).isZero

theorem subsingleton_freePresheaf_hom_of_isEmpty (Z : Scheme.{0}) [IsEmpty Z] (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (hM : ∀ U : Scheme.{0}, IsEmpty U → Subsingleton (M.obj (op U))) :
    Subsingleton ((freeP R).obj (yoneda.obj Z) ⟶ M) := by
  constructor; intro α β
  apply NatTrans.ext; funext U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  by_cases h : IsEmpty ((Opposite.unop U : Scheme.{0}) : Type)
  · haveI := hM _ h; exact Subsingleton.elim _ _
  · haveI : IsEmpty (Opposite.unop U ⟶ Z) := ⟨fun f => h ⟨fun y => isEmptyElim (f.base y)⟩⟩
    have hs : Subsingleton (((freeP R).obj (yoneda.obj Z)).obj U) := by
      change Subsingleton (ULift.{1} (Opposite.unop U ⟶ Z) →₀ ULift.{1} R); infer_instance
    rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem free_zero (Z : Scheme.{0}) [IsEmpty Z] : IsZero ((free R).obj (yoneda.obj Z)) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 := subsingleton_freePresheaf_hom_of_isEmpty (R := R) Z ((sheafToPresheaf Scheme.etaleTopology _).obj ((free R).obj (yoneda.obj Z)))
    (fun U hU => by haveI := hU; exact sec_sub _ U)
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv ((freeP R).obj (yoneda.obj Z))
    ((free R).obj (yoneda.obj Z))).injective
  exact h1.elim _ _

theorem chains_zero (Z : Scheme.{0}) [IsEmpty Z] (p : ℤ) : IsZero (((chains R).obj (sch.obj Z)).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have hz : IsZero (((chainsN R).obj (sch.obj Z)).X j) := free_zero (R := R) Z
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat p h

theorem H_sub (Z : Scheme.{0}) [IsEmpty Z] (F : Shv R) (n : ℤ) : Subsingleton (H R (sch.obj Z) F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (chains_zero (R := R) Z p).eq_of_src _ _

end LateralTheory.E.LeafKunEmptyPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.DescEqvPf

variable {R : Type} [CommRing R]

theorem mono_sch {X Y : Scheme.{0}} (j : X ⟶ Y) [Mono j] : Mono (sch.map j) := by
  rw [NatTrans.mono_iff_mono_app]; intro n
  rw [NatTrans.mono_iff_mono_app]; intro T
  rw [mono_iff_injective]; intro a b h
  exact (cancel_mono j).1 h

theorem sub_of_iso {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) [Subsingleton (H R E' F n)] :
    Subsingleton (H R E F n) := by
  constructor; intro x y
  have hx : x = pull R i.hom F n (pull R i.inv F n x) := by rw [← pull_comp, i.hom_inv_id, pull_id]
  have hy : y = pull R i.hom F n (pull R i.inv F n y) := by rw [← pull_comp, i.hom_inv_id, pull_id]
  rw [hx, hy, Subsingleton.elim (pull R i.inv F n x) (pull R i.inv F n y)]

theorem sub_of_zero (E : Spc) (h : ∀ p, IsZero (((chains R).obj E).X p)) (F : Shv R) (n : ℤ) :
    Subsingleton (H R E F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (h p).eq_of_src _ _

theorem bij_of_sub {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) [Subsingleton (H R E F n)]
    [Subsingleton (H R E' F n)] : Function.Bijective (pull R f F n) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

instance freeModPresE : PreservesColimitsOfShape (Discrete PEmpty.{1}) (ModuleCat.free.{1} (ULift.{1} R)) := by
  have := (ModuleCat.adj.{1} (ULift.{1} R)).leftAdjoint_preservesColimits
  infer_instance

instance freePresE : PreservesColimitsOfShape (Discrete PEmpty.{1}) (free R) := by unfold free freeP; infer_instance

theorem chains_zero_of_initial (E : Spc) (hE : IsInitial E) (p : ℤ) : IsZero (((chains R).obj E).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have h1 : IsInitial (E.obj (op (SimplexCategory.mk j))) :=
      IsInitial.isInitialObj ((evaluation _ _).obj (op (SimplexCategory.mk j))) _ hE
    have h2 : IsInitial ((free R).obj (E.obj (op (SimplexCategory.mk j)))) := IsInitial.isInitialObj (free R) _ h1
    have hz : IsZero (((chainsN R).obj E).X j) := h2.isZero
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p h

end LateralTheory.E.DescEqvPf

namespace LateralTheory.E.DescEqvPf

variable {A R0 R1 : Type} [CommRing A] [CommRing R0] [CommRing R1] (e : A ≃+* R0 × R1)

def psi : Spec (.of R0) ⨿ Spec (.of R1) ⟶ Spec (.of A) :=
  coprodSpec R0 R1 ≫ Spec.map (CommRingCat.ofHom e.toRingHom)

instance : IsIso (psi e) := by
  unfold psi
  have : IsIso (CommRingCat.ofHom e.toRingHom) := (e.toCommRingCatIso).isIso_hom
  infer_instance

theorem inl_psi : coprod.inl ≫ psi e = Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) := by
  rw [psi, coprodSpec_inl_assoc, ← Spec.map_comp]; rfl

theorem inr_psi : coprod.inr ≫ psi e = Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) := by
  rw [psi, coprodSpec_inr_assoc, ← Spec.map_comp]; rfl

instance oi0 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))) := by
  rw [← inl_psi]; infer_instance

instance oi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom))) := by
  rw [← inr_psi]; infer_instance

theorem empty_pb : IsEmpty ↥(Limits.pullback (C := Scheme.{0}) (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) := by
  refine ⟨fun z => ?_⟩
  have h := pullback.condition (f := Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (g := Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))
  have k0 : Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) ≫ inv (psi e) = coprod.inl := by
    rw [← inl_psi]; simp
  have k1 : Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) ≫ inv (psi e) = coprod.inr := by
    rw [← inr_psi]; simp
  have h2 := congrArg (fun f => (f ≫ inv (psi e)).base z) h
  simp only [Category.assoc] at h2
  rw [k0, k1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
  exact Set.disjoint_left.mp (isCompl_range_inl_inr (Spec (.of R0)) (Spec (.of R1))).disjoint ⟨_, rfl⟩ ⟨_, h2.symm⟩

end LateralTheory.E.DescEqvPf

namespace LateralTheory.E.DescEqvPf

variable {R : Type} [CommRing R]

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance

theorem eqv_id (E : Spc) (F : Shv R) : Eqv R (𝟙 E) F := fun n =>
  ⟨fun a b h => by rwa [pull_id, pull_id] at h, fun y => ⟨y, pull_id R E F n y⟩⟩

theorem loc_coprod (U V : Spc) : LateralTheory.E.D2.LocCover (coprod.inl : U ⟶ U ⨿ V) coprod.inr := by
  intro n X x
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
  intro Y k _
  let G : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op X)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (isColimitOfPreserves G (coprodIsCoprod U V)) x
  rcases j with ⟨(_ | _)⟩
  · left
    refine ⟨(U.obj _).map k.op y, ?_⟩
    rw [← hy]
    exact NatTrans.naturality_apply ((coprod.inl : U ⟶ U ⨿ V).app (op (SimplexCategory.mk n))) k.op y
  · right
    refine ⟨(V.obj _).map k.op y, ?_⟩
    rw [← hy]
    exact NatTrans.naturality_apply ((coprod.inr : V ⟶ U ⨿ V).app (op (SimplexCategory.mk n))) k.op y

theorem cover_coprod (U V : Spc) : Cover2 R (coprod.inl : U ⟶ U ⨿ V) coprod.inr :=
  LateralTheory.E.LeafCover2Pf.LeafCover2_of R _ _ inferInstance inferInstance (loc_coprod U V)

theorem sub_pb_coprod (U V : Spc) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (pullback (coprod.inl : U ⟶ U ⨿ V) coprod.inr) F n) := by
  have hP := FinitaryExtensive.isPullback_initial_to_binaryCofan (coprodIsCoprod U V)
  have hI : IsInitial (pullback (coprod.inl : U ⟶ U ⨿ V) coprod.inr) :=
    by
      set_option synthInstance.maxHeartbeats 200000 in
        exact IsInitial.ofIso initialIsInitial hP.isoPullback
  exact sub_of_zero _ (chains_zero_of_initial _ hI) F n

variable {A R0 R1 : Type} [CommRing A] [CommRing R0] [CommRing R1] (e : A ≃+* R0 × R1)

theorem loc_sch : LateralTheory.E.D2.LocCover (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
    (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) := by
  intro n X x
  let x' : X ⟶ Spec (.of A) := x
  let C : Scheme.OpenCover.{0} X := (coprodOpenCover.{0} (Spec (.of R0)) (Spec (.of R1))).pullback₁ (x' ≫ inv (psi e))
  refine ⟨Sieve.ofArrows C.X C.f, Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨i, h, rfl⟩ := hk
  rcases i with (_ | _)
  · left
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    have c := pullback.condition (f := x' ≫ inv (psi e)) (g := (coprod.inl : Spec (.of R0) ⟶ _))
    have c' : pullback.fst (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _) ≫ x' =
        pullback.snd (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _) ≫
          Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) := by
      rw [← inl_psi, ← Category.assoc, ← c]; simp
    change (h ≫ pullback.snd (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _)) ≫
        Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) =
      (h ≫ pullback.fst (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _)) ≫ x'
    exact (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) c'.symm).trans (Category.assoc _ _ _).symm)
  · right
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    have c := pullback.condition (f := x' ≫ inv (psi e)) (g := (coprod.inr : Spec (.of R1) ⟶ _))
    have c' : pullback.fst (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _) ≫ x' =
        pullback.snd (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _) ≫
          Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) := by
      rw [← inr_psi, ← Category.assoc, ← c]; simp
    change (h ≫ pullback.snd (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _)) ≫
        Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) =
      (h ≫ pullback.fst (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _)) ≫ x'
    exact (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) c'.symm).trans (Category.assoc _ _ _).symm)

theorem cover_sch : Cover2 R (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
    (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) :=
  LateralTheory.E.LeafCover2Pf.LeafCover2_of R _ _ (mono_sch _) (mono_sch _) (loc_sch e)

theorem sub_pb_sch (F : Shv R) (n : ℤ) :
    Subsingleton (H R (pullback (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
      (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom))))) F n) := by
  have := empty_pb e
  have := LateralTheory.E.LeafKunEmptyPf.H_sub (R := R) (Limits.pullback (C := Scheme.{0})
    (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) F n
  exact sub_of_iso (PreservesPullback.iso sch _ _).symm F n

end LateralTheory.E.DescEqvPf

theorem LateralTheory.E.BinPf.DescEqv_of : LateralTheory.E.BinPf.DescEqv := by
  intro H q A R0 R1 _ _ _ e i
  open LateralTheory.E.DescEqvPf in
  exact H.a4 (ZMod q) (coprod.inl : sp R0 ⟶ sp R0 ⨿ sp R1) coprod.inr
    (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom)) _ (𝟙 _) (𝟙 _) (by rw [Category.id_comp]; exact coprod.inl_desc _ _)
    (by rw [Category.id_comp]; exact coprod.inr_desc _ _) (tw q i)
    (cover_coprod _ _) (cover_sch e) (eqv_id _ _) (eqv_id _ _)
    (fun n => by
      have := sub_pb_coprod (R := ZMod q) (sp R0) (sp R1) (tw q i) n
      have := sub_pb_sch (R := ZMod q) e (tw q i) n
      exact bij_of_sub _ _ n)
end
end

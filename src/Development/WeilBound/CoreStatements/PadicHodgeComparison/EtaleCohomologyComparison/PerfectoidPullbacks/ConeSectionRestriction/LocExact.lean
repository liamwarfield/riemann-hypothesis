module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactC
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactA
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

theorem range_sub_awayι {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Set.range z ⊆ Set.range (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd) := by
  rintro _ ⟨x, rfl⟩
  have hx : z x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f := h (Set.mem_univ x)
  rw [← Proj.opensRange_awayι _ f hf hd] at hx
  exact hx

def liftA {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A :=
  (Spec.preimage (IsOpenImmersion.lift (Proj.awayι _ f hf hd) z (range_sub_awayι z hf hd h))).hom

theorem liftA_spec {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z := by
  unfold liftA
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem liftA_unique {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ f hf hd = z) : φ = liftA z hf hd h := by
  have h1 : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (liftA z hf hd h)) := by
    rw [← cancel_mono (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd), hφ, liftA_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem liftA_comp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ) ≫ z) ⁻¹ᵁ Proj.basicOpen _ f) :
    liftA (Spec.map (CommRingCat.ofHom ρ) ≫ z) hf hd h' = ρ.comp (liftA z hf hd h) := by
  symm
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, liftA_spec]

theorem liftA_awayMap {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d d' : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (d + d')) (hdd : 0 < d + d')
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x) :
    (liftA z hxd hdd h').comp (HomogeneousLocalization.awayMap _ hg hx) = liftA z hf hd h := by
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
  exact liftA_spec z hxd hdd h'

theorem awayToSection_appLE {A : CommRingCat.{0}}
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d)
    (φ : CommRingCat.of (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) ⟶ A)
    (h : ⊤ ≤ (Spec.map φ ≫ Proj.awayι _ f hf hd) ⁻¹ᵁ Proj.basicOpen _ f) :
    Proj.awayToSection _ f ≫ (Spec.map φ ≫ Proj.awayι _ f hf hd).appLE (Proj.basicOpen _ f) ⊤ h ≫
      (Scheme.ΓSpecIso A).hom = φ := by
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.map φ ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd).inv := ⟨_, rfl⟩
  have e1 : Spec.map φ ≫ Proj.awayι _ f hf hd = w ≫ (Proj.basicOpen _ f).ι := by
    rw [hw, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have e2 : w ≫ Proj.basicOpenToSpec _ f = Spec.map φ := by
    rw [hw, ← Proj.basicOpenIsoSpec_hom _ f hf hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have e3 : ∀ (z : Spec A ⟶ PSpace K N) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hz : z = w ≫ (Proj.basicOpen _ f).ι),
      z.appLE (Proj.basicOpen _ f) ⊤ h = (Proj.basicOpen _ f).topIso.inv ≫ w.appTop := by
    intro z h hz
    subst hz
    rw [← Scheme.Hom.appLE_comp_appLE w _ _ ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [e3 _ h e1]
  have e4 := Scheme.ΓSpecIso_naturality φ
  rw [← e2, Scheme.Hom.comp_appTop] at e4
  have e5 := Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f
  change (Proj.basicOpenToSpec _ f).appTop = _ at e5
  rw [e5] at e4
  simp only [Category.assoc] at e4
  simpa only [Category.assoc] using (cancel_epi _).1 e4

theorem liftA_eval {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) = liftA z hf hd h a := by
  have key : ∀ (z' : Spec (CommRingCat.of A) ⟶ PSpace K N) (h' : ⊤ ≤ z' ⁻¹ᵁ Proj.basicOpen _ f)
      (hz : Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z'),
      Proj.awayToSection _ f ≫ z'.appLE (Proj.basicOpen _ f) ⊤ h' ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (liftA z hf hd h) := by
    intro z' h' hz
    subst hz
    exact awayToSection_appLE hf hd _ h'
  exact congrArg (fun ψ => CommRingCat.Hom.hom ψ a) (key z h (liftA_spec z hf hd h))

theorem le_basicOpen_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g : MvPolynomial (Fin (N + 1)) K}
    (hf : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hg : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ g) :
    ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (f * g) := by
  rw [Proj.basicOpen_mul]
  intro p hp
  exact ⟨hf hp, hg hp⟩

theorem liftA_eval_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d' n : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K n) (hn : 0 < n)
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) =
      liftA z hxd hn h' (HomogeneousLocalization.awayMap _ hg hx a) := by
  rw [← liftA_eval]
  have e : Proj.awayToSection _ f ≫ z.appLE (Proj.basicOpen _ f) ⊤ h =
      CommRingCat.ofHom (HomogeneousLocalization.awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        z.appLE (Proj.basicOpen _ x) ⊤ h' := by
    rw [← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (CommRingCat.Hom.hom ψ a)) e

def yx {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1))
    (k : Fin m) : ChartR K N j :=
  HomogeneousLocalization.Away.mk _ (X_mem K N j) e (y k)
    (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k))

theorem liftA_yx_isUnit {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k)) :
    IsUnit (liftA z (X_mem K N j) one_pos hj (yx y hy j k)) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have hxd : MvPolynomial.X j * y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk
  rw [← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx, RingHom.comp_apply]
  apply IsUnit.map
  have hX : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ^ (1 + e) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • (1 + e)) := by
    simpa using SetLike.pow_mem_graded (1 + e) (X_mem K N j)
  refine IsUnit.of_mul_eq_one (HomogeneousLocalization.Away.mk _ hxd 1 _ hX) ?_
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  ring

theorem liftA_yx_change {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j j' : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hj' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j') one_pos hj' (yx y hy j' k) * liftA z (X_mem K N j) one_pos hj (ratio K N j j') ^ e := by
  have hxd : (MvPolynomial.X j * MvPolynomial.X j' : MvPolynomial (Fin (N + 1)) K) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + 1) :=
    SetLike.mul_mem_graded (X_mem K N j) (X_mem K N j')
  have hx := le_basicOpen_mul z hj hj'
  rw [← liftA_awayMap z (X_mem K N j) one_pos (X_mem K N j') rfl hxd (by omega) hj hx,
    ← liftA_awayMap z (X_mem K N j') one_pos (X_mem K N j) (mul_comm _ _) hxd (by omega) hj' hx]
  simp only [RingHom.comp_apply]
  rw [← map_pow, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx ratio
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

theorem liftA_yx_quot {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k k' : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j) one_pos hj (yx y hy j k') *
        GlobalTheory.Cris.evalAt z (Proj.basicOpen _ (y k')) hk'
          ((Proj.awayToSection _ (y k')).hom
            (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
              (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hxd : MvPolynomial.X j * y k' ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk'
  rw [liftA_eval_mul z (X_mem K N j) (mul_comm _ _) hxd (by omega) hk' hx,
    ← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx]
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

end CrystallineSemistableComparison.Pb.LX
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.ConeZcls (ub ub_mul ub_nat ub_isUnit exists_unit_lift pt_map)

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

section Pts
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem inU_map_c {V : X.Opens} {T T' : Thick (smFun X q)} (f : T ⟶ T') (h : InU V T) : InU V T' := by
  intro x _
  have e := pt_map f
  have hx : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) x) ∈ pt T ⁻¹ᵁ V := h (Set.mem_univ _)
  change (pt T') x ∈ V
  rw [← e]
  exact hx

theorem inU_inf_left {V W : X.Opens} {T : Thick (smFun X q)} (h : InU (V ⊓ W) T) : InU V T :=
  inU_mono q inf_le_left h

theorem inU_inf_right {V W : X.Opens} {T : Thick (smFun X q)} (h : InU (V ⊓ W) T) : InU W T :=
  inU_mono q inf_le_right h

end Pts

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)

theorem wK_tf {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : TF 1 s T := h.1

theorem wK_uy {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : InU (uy i y k) T := by
  obtain ⟨-, V, ⟨j, rfl⟩, hV⟩ := h
  exact inU_inf_left hV

theorem wK_wch {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : ∃ j, InU (wch i j) T := by
  obtain ⟨-, V, ⟨j, rfl⟩, hV⟩ := h
  exact ⟨j, inU_inf_right hV⟩

theorem wK_le_wU (k : Fin m) : wK q i y s k ≤ wU q i y s := fun _ h => ⟨k, h⟩

theorem wU_wch {T : Thick (smFun X q)} (h : wU q i y s T) : ∃ j, InU (wch i j) T := by
  obtain ⟨k, hk⟩ := h
  exact wK_wch i y s hk

def lj (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) : ChartR K N j →+* T.B ⧸ T.J :=
  liftA (pt T ≫ i) (X_mem K N j) one_pos h

theorem lj_spec (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    pt T ≫ i = Spec.map (CommRingCat.ofHom (lj i T j h)) ≫ chart K N j :=
  (liftA_spec (pt T ≫ i) (X_mem K N j) one_pos h).symm

def az (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ pullback i (chart K N j) :=
  pullback.lift (pt T) (Spec.map (CommRingCat.ofHom (lj i T j h))) (lj_spec i T j h)

theorem lj_comp {T T' : Thick (smFun X q)} (f : T ⟶ T') (j : Fin (N + 1)) (h : InU (wch i j) T) (h' : InU (wch i j) T') :
    lj i T' j h' = (Ideal.quotientMap T'.J f.φ f.hle).comp (lj i T j h) := by
  have e : pt T' ≫ i = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ (pt T ≫ i) := by
    rw [← Category.assoc, pt_map f]
  unfold lj
  have key := liftA_comp (Ideal.quotientMap T'.J f.φ f.hle) (pt T ≫ i) (X_mem K N j) one_pos h (e ▸ h')
  refine Eq.trans ?_ key
  congr 1

section O1
variable {D : E.LineData X}

def sO (hD : IsTautologicalLineAt D N i) (j : Fin (N + 1)) : pullback i (chart K N j) ⟶ D.Y := hD.2.choose j

theorem sO_f (hD : IsTautologicalLineAt D N i) (j : Fin (N + 1)) : sO i hD j ≫ D.f = pullback.fst _ _ :=
  hD.2.choose_spec.choose j

theorem sO_u (hD : IsTautologicalLineAt D N i) {V : Scheme.{0}} (j k : Fin (N + 1)) (a : V ⟶ pullback i (chart K N j))
    (b : V ⟶ pullback i (chart K N k)) (h : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _)
    (h' : (a ≫ sO i hD j) ≫ D.f = (b ≫ sO i hD k) ≫ D.f) :
    ((D.u (a ≫ sO i hD j) (b ≫ sO i hD k) h' : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
      (a ≫ pullback.snd _ _).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR K N j))).inv.hom (ratio K N j k)) :=
  hD.2.choose_spec.choose_spec V j k a b h

theorem ub_congr {A : Type} [CommRing A] {a a' b b' : Spec (CommRingCat.of A) ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : ub (D := D) a b h = ub (D := D) a' b' h' := by
  subst ha hb; rfl

theorem az_f (hD : IsTautologicalLineAt D N i) (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    (az i T j h ≫ sO i hD j) ≫ D.f = pt T := by
  rw [Category.assoc, sO_f]
  exact pullback.lift_fst _ _ _

theorem az_f' (hD : IsTautologicalLineAt D N i) (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    az i T j h ≫ sO i hD j ≫ D.f = pt T := by
  rw [sO_f]
  exact pullback.lift_fst _ _ _

def jc (c : (wU q i y s).FullSubcategory) : Fin (N + 1) := (wU_wch i y s c.property).choose

theorem hjc (c : (wU q i y s).FullSubcategory) : InU (wch i (jc i y s c)) c.obj := (wU_wch i y s c.property).choose_spec

def AU (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (c : (wU q i y s).FullSubcategory) : (c.obj.B ⧸ c.obj.J)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (c.obj.B ⧸ c.obj.J))).hom.hom.toMonoidHom
    (D.u (az i c.obj (jc i y s c) (hjc i y s c) ≫ sO i hD (jc i y s c)) (Λ.p c) ((az_f i hD _ _ _).trans (Λ.hp c).symm))

def μ (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory) : c.obj.B ⧸ c.obj.J :=
  lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) *
    (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J)

theorem μ_isUnit (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) : IsUnit (μ i y hy s hD Λ k c) :=
  (liftA_yx_isUnit (pt c.obj ≫ i) y hy _ k (hjc i y s c) hk).mul (Units.isUnit _)

def vv (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) : c.obj.Bˣ :=
  (exists_unit_lift c.obj _ (μ_isUnit i y hy s hD Λ k c hk)).choose

theorem vv_spec (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) :
    Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k c hk : c.obj.Bˣ) : c.obj.B) = μ i y hy s hD Λ k c :=
  (exists_unit_lift c.obj _ (μ_isUnit i y hy s hD Λ k c hk)).choose_spec

end O1

section E
variable {D : E.LineData X}

theorem gamma_specMap {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ψ r := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((Spec.map (CommRingCat.ofHom ψ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom).hom _ = _
  rw [e]
  simp

theorem eps_mem (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) {c c' : (wU q i y s).FullSubcategory}
    (φ : c ⟶ c') (hk : InU (uy i y k) c.obj) (hk' : InU (uy i y k) c'.obj) :
    (((show c'.obj.Bˣ from Λ.w φ) ^ e * vv i y hy s hD Λ k c' hk' *
        (Units.map (show c.obj ⟶ c'.obj from (wU q i y s).ι.map φ).φ.toMonoidHom (vv i y hy s hD Λ k c hk))⁻¹ :
          c'.obj.Bˣ) : c'.obj.B) - 1 ∈ c'.obj.J := by
  set f : c.obj ⟶ c'.obj := (wU q i y s).ι.map φ with hf
  set Q := Ideal.quotientMap c'.obj.J f.φ f.hle with hQ
  have hj : InU (wch i (jc i y s c)) c.obj := hjc i y s c
  have hj' : InU (wch i (jc i y s c')) c'.obj := hjc i y s c'
  have hjT : InU (wch i (jc i y s c)) c'.obj := inU_map_c f hj
  have hpt : Spec.map (CommRingCat.ofHom Q) ≫ pt c.obj = pt c'.obj := pt_map f

  have h1 : (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp]; exact hpt
  have ew : Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) =
      ub (D := D) (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) (Λ.p c') h1 := Λ.hw φ h1

  have h2 : (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c))) ≫ D.f =
      (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) ≫ D.f := by
    simp only [Category.assoc, az_f']
    rw [Λ.hp]
    rfl
  have eA : Q (((AU i y s hD Λ c : (c.obj.B ⧸ c.obj.J)ˣ)) : c.obj.B ⧸ c.obj.J) =
      ub (D := D) (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c)))
        (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) h2 :=
    (ub_nat Q _ _ _ h2).symm

  have h3 : (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c))) ≫ D.f =
      (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f := by
    simp only [Category.assoc, az_f']
    exact hpt
  have h4 : (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [az_f, Λ.hp]
    rfl
  have hcoc : ub (D := D) _ _ h2 * ub (D := D) _ _ h1 = ub (D := D) _ _ h3 * ub (D := D) _ _ h4 := by
    rw [ub_mul, ub_mul]

  have h5 : (Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ pullback.fst _ _ = az i c'.obj _ hj' ≫ pullback.fst _ _ := by
    rw [Category.assoc]
    unfold az
    rw [pullback.lift_fst, pullback.lift_fst, hpt]
  have h3' : ((Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ sO i hD (jc i y s c)) ≫ D.f =
      (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f := by
    rw [Category.assoc]; exact h3
  have eR : ub (D := D) _ _ h3 = lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) := by
    rw [ub_congr (Category.assoc _ _ _).symm rfl h3 h3']
    unfold ub
    rw [sO_u i hD _ _ _ _ h5 h3']
    have e6 : (Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (lj i c'.obj _ hjT)) := by
      rw [Category.assoc]
      unfold az
      rw [pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ)) (lj_comp i f _ hj hjT).symm
    rw [e6]
    exact gamma_specMap _ _

  have hY : lj i c'.obj _ hjT (yx y hy (jc i y s c) k) =
      lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) ^ e :=
    liftA_yx_change (pt c'.obj ≫ i) y hy (jc i y s c) (jc i y s c') k hjT hj'
  have eY : Q (lj i c.obj _ hj (yx y hy (jc i y s c) k)) = lj i c'.obj _ hjT (yx y hy (jc i y s c) k) :=
    (RingHom.congr_fun (lj_comp i f _ hj hjT) _).symm

  have key : Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) ^ e * μ i y hy s hD Λ k c' =
      Q (μ i y hy s hD Λ k c) := by
    set U := Units.map Q.toMonoidHom (AU i y s hD Λ c) with hU
    have hUv : (U : c'.obj.B ⧸ c'.obj.J) = ub (D := D) _ _ h2 := eA
    set A' := AU i y s hD Λ c' with hA'
    have hA'v : (A' : c'.obj.B ⧸ c'.obj.J) = ub (D := D) _ _ h4 := rfl
    set W := Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) with hWdef
    set R := lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) with hR
    have hc : (U : c'.obj.B ⧸ c'.obj.J) * W = R * A' := by
      rw [hUv, hA'v, ew, ← eR]; exact hcoc
    have hW : W = ((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) * (R * A') := by
      rw [← hc, ← mul_assoc, Units.inv_mul, one_mul]
    have hQμ : Q (μ i y hy s hD Λ k c) = lj i c'.obj _ hjT (yx y hy (jc i y s c) k) *
        (((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J)) ^ e := by
      unfold μ
      rw [map_mul, eY, Units.val_pow_eq_pow_val, map_pow]
      rfl
    rw [hQμ]
    unfold μ
    rw [← hA', hY, hW, Units.val_pow_eq_pow_val]
    have hA : (A' : c'.obj.B ⧸ c'.obj.J) ^ e * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    calc (((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) * (R * A')) ^ e *
          (lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e)
        = lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * R ^ e * ((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e *
          ((A' : c'.obj.B ⧸ c'.obj.J) ^ e * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e) := by ring
      _ = _ := by rw [hA, mul_one]

  have hv := vv_spec i y hy s hD Λ k c hk
  have hv' := vv_spec i y hy s hD Λ k c' hk'
  have hfv : Ideal.Quotient.mk c'.obj.J
      ((Units.map f.φ.toMonoidHom (vv i y hy s hD Λ k c hk) : c'.obj.Bˣ) : c'.obj.B) = Q (μ i y hy s hD Λ k c) := by
    rw [← hv]; rfl
  have hinv : Ideal.Quotient.mk c'.obj.J
      (((Units.map f.φ.toMonoidHom (vv i y hy s hD Λ k c hk))⁻¹ : c'.obj.Bˣ) : c'.obj.B) * Q (μ i y hy s hD Λ k c) = 1 := by
    rw [← hfv, ← map_mul, Units.inv_mul, map_one]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, Units.val_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_mul, map_pow, hv', key, mul_comm]
  exact hinv

end E

end CrystallineSemistableComparison.Pb.LX
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactB
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LX

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C]
  {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def epsE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').Bˣ :=
  Λ.w φ ^ e * v c' * (Units.map (g.map φ).φ.toMonoidHom (v c))⁻¹

def bE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) : CH.Cn (g ⋙ O (smFun X q)) 1 :=
  fun τ => (show (g.obj (τ.obj (Fin.last 1))).B from
    plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
      (g.obj (τ.obj (Fin.last 1))).B) - 1))

theorem grpE_add {G : Type} [AddCommGroup G] (a b c x y z : G) (e : ℕ) :
    e • a + y + -z + (e • b + x + -y) + -(e • c + x + -z) = e • (a + b + -c) := by
  simp only [smul_add, smul_neg]; abel

theorem grpE {G : Type} [CommGroup G] (a b c x y z : G) (e : ℕ) :
    a ^ e * y * z⁻¹ * (b ^ e * x * y⁻¹) * (c ^ e * x * z⁻¹)⁻¹ = (a * b * c⁻¹) ^ e :=
  @grpE_add (Additive G) _ a b c x y z e

theorem grpS_add {G : Type} [AddCommGroup G] (a x x' y y' : G) :
    (a + x + -y) + -(a + x' + -y') = (x + -x') + -(y + -y') := by abel

theorem grpS {G : Type} [CommGroup G] (a x x' y y' : G) :
    (a * x * y⁻¹) * (a * x' * y'⁻¹)⁻¹ = (x * x'⁻¹) * (y * y'⁻¹)⁻¹ :=
  @grpS_add (Additive G) _ a x x' y y'

theorem plog_pow [CharZero K] (T : Thick (smFun X q)) (s : ℕ) (hs : T.pdPow s = ⊥) (a : T.Bˣ)
    (ha : (a : T.B) - 1 ∈ T.J) (n : ℕ) :
    ((a ^ n : T.Bˣ) : T.B) - 1 ∈ T.J ∧
      plogK T.δ s (((a ^ n : T.Bˣ) : T.B) - 1) = n • plogK T.δ s ((a : T.B) - 1) := by
  induction n with
  | zero => simp [GlobalTheory.CompanionTheory.ConeZcls.plogK_zero, T.J.zero_mem]
  | succ n ih =>
    rw [pow_succ]
    refine ⟨GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem T _ _ ih.1 ha, ?_⟩
    rw [GlobalTheory.CompanionTheory.ConeZcls.plog_mul T s hs _ _ ih.1 ha, ih.2, succ_nsmul]

theorem epsE_rr (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂)
    (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ) :
    Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) * epsE Λ v e ψ * (epsE Λ v e χ)⁻¹ =
      GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ ^ e := by
  subst hχ
  have h : Units.map (g.map (φ ≫ ψ)).φ.toMonoidHom (v c₀) =
      Units.map (g.map ψ).φ.toMonoidHom (Units.map (g.map φ).φ.toMonoidHom (v c₀)) := by
    rw [g.map_comp]; rfl
  unfold epsE GlobalTheory.CompanionTheory.ConeZcls.rr
  rw [h]
  simp only [map_mul, map_inv, map_pow]
  exact grpE _ _ _ _ _ _ e

def lE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').B :=
  plogK (g.obj c').δ s (((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1)

theorem log_rr [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ)
    (hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J) :
    e • plogK (g.obj c₂).δ s (((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) =
      (g.map ψ).φ (lE Λ v e s φ) + lE Λ v e s ψ - lE Λ v e s χ := by
  have e0 := hε φ
  have e1 := hε ψ
  have e2 := hε χ
  have e0' : ((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J := by
    have := (g.map ψ).hle e0
    simpa using this
  have hm : plogK (g.obj c₂).δ s (((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) :
      (g.obj c₂).B) - 1) = (g.map ψ).φ (lE Λ v e s φ) := by
    unfold lE
    rw [GlobalTheory.CompanionTheory.ConeZcls.plogK_map (g.map ψ) s e0]
    simp
  rw [← (plog_pow (g.obj c₂) s (hs _) _ hr e).2, ← epsE_rr Λ v e φ ψ χ hχ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ (GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem _ _ _ e0' e1)
      (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e0' e1, GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, hm]
  unfold lE
  ring

theorem epsE_div (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') :
    epsE Λ v e φ * (epsE Λ v' e φ)⁻¹ =
      (v c' * (v' c')⁻¹) * (Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ := by
  unfold epsE
  simp only [map_mul, map_inv]
  exact grpS _ _ _ _ _

theorem lE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    {c c' : C} (φ : c ⟶ c')
    (e1 : ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (e2 : ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    lE Λ v e s φ - lE Λ v' e s φ =
      plogK (g.obj c').δ s (((v c' * (v' c')⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) *
        Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) - 1) := by
  have hR : Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) =
      (((Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) := by
    rw [← Ring.inverse_unit]; rfl
  unfold lE
  rw [hR, ← Units.val_mul, ← epsE_div Λ v v' e φ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e1 (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, sub_eq_add_neg]

theorem zK_smul_eq_d [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    e • zK Λ s = CH.d _ 1 (bE Λ v e s) := by
  funext σ
  have hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) : (g.obj (σ.obj (Fin.last 2))).Bˣ) :
      (g.obj (σ.obj (Fin.last 2))).B) - 1 ∈ (g.obj (σ.obj (Fin.last 2))).J := GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ
  have key := log_rr Λ v e s hs hε (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (GlobalTheory.CompanionTheory.ConeZcls.composable_arrows_map_zero_two σ) hr
  have h0 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 0 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 0 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 1 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h1 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 1 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 1 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 0 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h2 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 2 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 2 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from (g.map (σ.map' 1 2)).φ (lE Λ v e s (σ.map' 0 1))) := rfl
  have hd : CH.d (g ⋙ O (smFun X q)) 1 (bE Λ v e s) σ =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast i σ)).hom
        (bE Λ v e s (GlobalTheory.CatH.face i σ)) := rfl
  rw [Pi.smul_apply, hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  rw [h0, h1, h2]
  refine key.trans ?_
  have fin : ∀ a b c : (g.obj (σ.obj (Fin.last 2))).B, a + b - c = b + -c + a := fun a b c => by abel
  exact fin _ _ _

theorem bE_mem (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) : (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ) ∈ (g.obj (τ.obj (Fin.last 1))).J := by
  change plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
    (g.obj (τ.obj (Fin.last 1))).B) - 1) ∈ _
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ((g.obj (τ.obj (Fin.last 1))).δ.dpow_mem (Nat.succ_ne_zero k)
    (hε (τ.map' 0 1)))

theorem bE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (hε' : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) :
    (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ - bE Λ v' e s τ) =
      plogK (g.obj (τ.obj (Fin.last 1))).δ s
        (((v (τ.obj (Fin.last 1)) * (v' (τ.obj (Fin.last 1)))⁻¹ : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
            (g.obj (τ.obj (Fin.last 1))).B) *
          Ring.inverse (show (g.obj (τ.obj (Fin.last 1))).B from (g.map (τ.map' 0 1)).φ
            (((v (τ.obj 0) * (v' (τ.obj 0))⁻¹ : (g.obj (τ.obj 0)).Bˣ) : (g.obj (τ.obj 0)).B))) - 1) :=
  lE_sub Λ v v' e s hs (τ.map' 0 1) (hε (τ.map' 0 1)) (hε' (τ.map' 0 1))

end CrystallineSemistableComparison.Pb.LX
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

namespace LX

section Fam
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ} {D : E.LineData X}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)
  (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D)

def vV (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s) (hk : ∀ T, V T → InU (uy i y k) T) :
    ∀ c : V.FullSubcategory, ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c).Bˣ :=
  fun c => vv i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).obj c) (hk _ c.property)

theorem vV_eps (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s)
    (hk : ∀ T, V T → InU (uy i y k) T) {c c' : V.FullSubcategory} (φ : c ⟶ c') :
    ((epsE (Λ.precomp (ObjectProperty.ιOfLE hV)) (vV i y hy s hD Λ k V hV hk) e φ :
        ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').Bˣ) : ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').B) - 1 ∈
      ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').J :=
  eps_mem i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).map φ) (hk _ c.property) (hk _ c'.property)

end Fam

theorem evalAt_comp_appLE {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Spec (CommRingCat.of A) ⟶ Y) (f : Y ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    GlobalTheory.Cris.evalAt (x ≫ f) U h' a = GlobalTheory.Cris.evalAt x (f ⁻¹ᵁ U) h (f.appLE U (f ⁻¹ᵁ U) le_rfl a) := by
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE x f U (f ⁻¹ᵁ U) ⊤ le_rfl h]
  rfl

theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have h := dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at h

theorem mem_thFil_one {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {T : Thick (smFun X q)} {x : T.B} (hx : x ∈ T.J) :
    (show (thA (smFun X q)).obj T from x) ∈ (thFil (smFun X q) 1).S T :=
  mem_pdP_one T.δ hx

end LX

open LX

theorem firstChern_local_exact [CharZero K] (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (i : X ⟶ PSpace K N)
    (hD : IsTautologicalLineAt D N i) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (s : ℕ) (Λ : CLiftK (ObjectProperty.ι fun T : Thick (smFun X q) => ∃ k, wK q i y s k T) D) :
    ∃ b : ∀ k, CH.Cn (CH.modF ((wK q i y s k).ι ⋙ thA (smFun X q))) 1,
      (∀ k σ, b k σ ∈ (thFil (smFun X q) 1).S _) ∧
      (∀ k, resB (thA (smFun X q)) (fun T h => ⟨k, h⟩ : wK q i y s k ≤ fun T : Thick (smFun X q) => ∃ k', wK q i y s k' T)
        (e • zK Λ s) = CH.d _ 1 (b k)) ∧
      ∀ k k', ∃ ĝ : ∀ T : (capS (wK q i y s) {k, k'}).FullSubcategory, T.obj.B,
        (∀ T (h : InU (uy i y k') T.obj),
          Ideal.Quotient.mk _ (ĝ T) = ev T.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))) ∧
        resB (thA (smFun X q)) (fun T h => h k (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k) (b k) -
          resB (thA (smFun X q)) (fun T h => h k' (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k') (b k') =
          dlogC (capS (wK q i y s) {k, k'}) s ĝ := by
  classical
  have hsk : ∀ k (c : (wK q i y s k).FullSubcategory), c.obj.pdPow s = ⊥ := fun k c => (wK_tf i y s c.property).1
  refine ⟨fun k => bE (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s, ?_, ?_, ?_⟩
  · intro k σ
    exact mem_thFil_one (bE_mem (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) σ)
  · intro k
    exact zK_smul_eq_d (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s (hsk k)
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h))
  · intro k k'
    have hkk : k ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hkk' : k' ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hcU : capS (wK q i y s) {k, k'} ≤ wU q i y s := fun T h => wK_le_wU i y s k T (h k hkk)
    have hc1 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k) T := fun T h => wK_uy i y s (h k hkk)
    have hc2 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k') T := fun T h => wK_uy i y s (h k' hkk')
    refine ⟨fun T => (show T.obj.B from ((vV i y hy s hD Λ k _ hcU hc1 T * (vV i y hy s hD Λ k' _ hcU hc2 T)⁻¹ :
        ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).Bˣ) : ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).B)),
      ?_, ?_⟩
    · intro T h
      set c : (wU q i y s).FullSubcategory := (ObjectProperty.ιOfLE hcU).obj T
      have h1 := vv_spec i y hy s hD Λ k c (hc1 _ T.property)
      have h2 := vv_spec i y hy s hD Λ k' c (hc2 _ T.property)
      have hq : lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) =
          lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
            ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) := by
        refine (liftA_yx_quot (pt c.obj ≫ i) y hy (jc i y s c) k k' (hjc i y s c) h).trans ?_
        congr 1
        exact evalAt_comp_appLE (pt c.obj) i _ h h _
      change Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k c (hc1 _ T.property) *
        (vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) = _
      rw [Units.val_mul, map_mul, h1]
      have h3 : Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k' c (hc2 _ T.property) : c.obj.Bˣ) : c.obj.B) *
          Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [h2] at h3
      unfold μ at h3 ⊢
      rw [hq]
      calc lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)
          = ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
            (lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) := by ring
        _ = _ := by rw [h3, mul_one]; rfl
    · funext τ
      exact bE_sub (Λ.precomp (ObjectProperty.ιOfLE hcU)) (vV i y hy s hD Λ k _ hcU hc1) (vV i y hy s hD Λ k' _ hcU hc2)
        e s (fun c => (wK_tf i y s (c.property k hkk)).1)
        (vV_eps i y hy s hD Λ k _ hcU hc1) (vV_eps i y hy s hD Λ k' _ hcU hc2) τ

end CrystallineSemistableComparison.Pb

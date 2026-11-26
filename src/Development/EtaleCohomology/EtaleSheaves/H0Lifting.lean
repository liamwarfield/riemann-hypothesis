module

public import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
public import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
public import Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.H0Lifting
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.H0Lifting
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem exists_epi {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (M : DerivedCategory A) :
    ∃ (Z : A) (φ : (DerivedCategory.singleFunctor A 0).obj Z ⟶ M),
      Epi ((DerivedCategory.homologyFunctor A 0).map φ) := by
  let K := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  let φ0 : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.cycles 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (K.iCycles 0) (fun k _ => K.iCycles_d 0 k)
  have h1 : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (K.cycles 0)).inv ≫
      HomologicalComplex.cyclesMap φ0 0 = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles 0)]
    simp [φ0]
  have h2 : Epi (HomologicalComplex.cyclesMap φ0 0) := epi_of_epi_fac h1
  have h3 : Epi (HomologicalComplex.homologyMap φ0 0) :=
    epi_of_epi_fac (HomologicalComplex.homologyπ_naturality φ0 0)
  have h4 : Epi ((DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map φ0)) := by
    have h := (DerivedCategory.homologyFunctorFactors A 0).inv.naturality φ0
    have h5 : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).map φ0) := h3
    exact epi_of_epi_fac h.symm
  refine ⟨K.cycles 0, ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).hom ≫ DerivedCategory.Q.map φ0 ≫ e.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h4 _ inferInstance)

theorem transport {A D : Type*} [Category A] [Category D] (S : A ⥤ D) (H : D ⥤ A) (η : S ⋙ H ≅ 𝟭 A)
    {X Y Z : A} {M : D} (a : X ⟶ Y) (s : X ⟶ Z) (t : H.obj (S.obj Y) ⟶ H.obj M) (φ : S.obj Z ⟶ M)
    (h : a ≫ η.inv.app Y ≫ t = s ≫ η.inv.app Z ≫ H.map φ) : H.map (S.map a) ≫ t = H.map (S.map s ≫ φ) := by
  have h1 : a ≫ η.inv.app Y = η.inv.app X ≫ H.map (S.map a) := η.inv.naturality a
  have h2 : s ≫ η.inv.app Z = η.inv.app X ≫ H.map (S.map s) := η.inv.naturality s
  have h3 : η.inv.app X ≫ H.map (S.map a) ≫ t = η.inv.app X ≫ H.map (S.map s) ≫ H.map φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h1).symm.trans ((Category.assoc _ _ _).trans
      (h.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map φ) h2).trans (Category.assoc _ _ _))))))
  rw [Functor.map_comp]
  exact (cancel_epi _).1 h3

abbrev PF (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ (B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q)))

def gen {B : Scheme.{0}} (q : ℕ) {U V : B.Etale} (a : V ⟶ U) : ((PF B q).obj U).obj (op V) :=
  ModuleCat.freeMk (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem gen_res {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).obj U).map b.op (gen q a) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem gen_map {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).map a).app (op W) (gen q b) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem pf_ext {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (f g : (PF B q).obj U ⟶ F) (h : f.app (op U) (gen q (𝟙 U)) = g.app (op U) (gen q (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
  rintro ⟨a⟩
  change f.app (op V) (gen q a) = g.app (op V) (gen q a)
  have e : gen q a = ((PF B q).obj U).map a.op (gen q (𝟙 U)) := by rw [gen_res, Category.comp_id]
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

theorem pf_exists {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (s : F.obj (op U)) : ∃ f : (PF B q).obj U ⟶ F, f.app (op U) (gen q (𝟙 U)) = s := by
  let c : ∀ V : B.Etaleᵒᵖ, ((PF B q).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V.unop ⟶ U))
      (TypeCat.ofHom (fun a => F.map a.down.op s))
  have hc : ∀ (V : B.Etale) (a : V ⟶ U), c (op V) (gen q a) = F.map a.op s := fun V a =>
    ModuleCat.freeDesc_apply (R := ULift.{1} (ZMod q)) _ _
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
    refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
    rintro ⟨a⟩
    change c (op W) (((PF B q).obj U).map (Quiver.Hom.op b) (gen q a)) = F.map (Quiver.Hom.op b) (c (op V) (gen q a))
    rw [gen_res, hc, hc, op_comp, Functor.map_comp]
    rfl
  · change c (op U) _ = _
    rw [hc]
    simp

theorem loc_lift {B : Scheme.{0}} {q : ℕ} {F G : SShv B q} (π : F ⟶ G) [Epi π] (U : B.Etale)
    (t : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U) ⟶ G) :
    Cov U (fun U' a => ∃ s : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U') ⟶ F,
      (presheafToSheaf (EtTop B) _).map ((PF B q).map a) ≫ t = s ≫ π) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  have hπ : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  let adj := sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let t' : (PF B q).obj U ⟶ G.obj := adj.homEquiv _ _ t
  refine ⟨_, Presheaf.imageSieve_mem (EtTop B) π.hom (t'.app (op U) (gen q (𝟙 U))), ?_⟩
  rintro U' a ⟨z, hz⟩
  obtain ⟨f, hf⟩ := pf_exists (F := F.obj) z
  refine ⟨(adj.homEquiv _ F).symm f, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply pf_ext
  change t'.app (op U') (((PF B q).map a).app (op U') (gen q (𝟙 U'))) = π.hom.app (op U') (f.app (op U') (gen q (𝟙 U')))
  rw [hf, hz, gen_map, ← NatTrans.naturality_apply, gen_res, Category.id_comp, Category.comp_id]

theorem etale_sheaf_epi_lifts_degree_zero_derived_maps_locally : EtaleDerivedDegreeZeroHomologyLocallyLifts := by
  intro B q M U t
  obtain ⟨Z, φ, hφ⟩ := exists_epi M
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0
  let X : B.Etale ⥤ SShv B q := PF B q ⋙ presheafToSheaf (EtTop B) _
  let π : Z ⟶ (H0 B q).obj M := η.inv.app Z ≫ (H0 B q).map φ
  have hπ : Epi π := epi_comp _ _
  let t0 : X.obj U ⟶ (H0 B q).obj M := η.inv.app (X.obj U) ≫ t
  refine (loc_lift π U t0).mono ?_
  rintro U' a ⟨s, hs⟩
  refine ⟨(DerivedCategory.singleFunctor _ 0).map s ≫ φ, ?_⟩
  exact transport _ _ η (X.map a) s t φ hs

end LateralTheory.E.H0Lifting
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSecRepPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafSecRepPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

section General
universe u
variable {C : Type u} [Category.{0} C] (R : Type 1) [Ring R]

def FP : C ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} R) :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type 0) (ModuleCat.{1} R)).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)

def gen {U V : C} (a : V ⟶ U) : ((FP R).obj U).obj (op V) :=
  ModuleCat.freeMk (R := R) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem map_gen {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    ((FP R).obj U).map b.op (gen R a) = gen R (b ≫ a) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem app_gen {U U' V : C} (a : V ⟶ U') (b : U' ⟶ U) :
    ((FP R).map b).app (op V) (gen R a) = gen R (a ≫ b) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem freePresheaf_hom_ext {U V : C} {M : ModuleCat.{1} R} {f g : ((FP R).obj U).obj (op V) ⟶ M}
    (h : ∀ a : V ⟶ U, f (gen R a) = g (gen R a)) : f = g :=
  ModuleCat.free_hom_ext (R := R) (X := ULift.{1} (V ⟶ U)) (fun x => h x.down)

def desc (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) (V : C) :
    ((FP R).obj U).obj (op V) ⟶ G.obj (op V) :=
  ModuleCat.freeDesc (R := R) (X := ULift.{1} (V ⟶ U)) (↾fun x => G.map x.down.op s)

theorem desc_gen (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) {V : C} (a : V ⟶ U) :
    desc R G U s V (gen R a) = G.map a.op s :=
  ModuleCat.freeDesc_apply (R := R) _ _

theorem nat_gen {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U V : C} (η : (FP R).obj U ⟶ G) (a : V ⟶ U) :
    η.app (op V) (gen R a) = G.map a.op (η.app (op U) (gen R (𝟙 U))) := by
  have h := ConcreteCategory.congr_hom (η.naturality a.op) (gen R (𝟙 U))
  simp only [ConcreteCategory.comp_apply] at h
  rw [map_gen, Category.comp_id] at h
  exact h

def yE (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) : ((FP R).obj U ⟶ G) ≃ G.obj (op U) where
  toFun η := η.app (op U) (gen R (𝟙 U))
  invFun s :=
    { app := fun V => desc R G U s V.unop
      naturality := by
        rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
        apply freePresheaf_hom_ext
        intro a
        simp only [ConcreteCategory.comp_apply]
        have h := map_gen R a b
        erw [h, desc_gen, desc_gen]
        rw [op_comp, G.map_comp, ConcreteCategory.comp_apply]
        rfl }
  left_inv η := by
    ext1
    funext ⟨V⟩
    apply freePresheaf_hom_ext
    intro a
    exact (desc_gen R G U _ a).trans (nat_gen R η a).symm
  right_inv s := by
    refine (desc_gen R G U s (𝟙 U)).trans ?_
    simp

theorem yE_res {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U U' : C} (a : U' ⟶ U) (η : (FP R).obj U ⟶ G) :
    yE R G U' ((FP R).map a ≫ η) = G.map a.op (yE R G U η) := by
  change η.app (op U') (((FP R).map a).app (op U') (gen R (𝟙 U'))) = _
  rw [app_gen, Category.id_comp]
  exact nat_gen R η a

theorem yE_sub {G : Cᵒᵖ ⥤ ModuleCat.{1} R} (U : C) (η η' : (FP R).obj U ⟶ G) :
    yE R G U (η - η') = yE R G U η - yE R G U η' := rfl

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{1} R)]

theorem general (T : C ⥤ Sheaf J (ModuleCat.{1} R)) (i : FP R ⋙ presheafToSheaf J _ ≅ T) :
    ∃ e : ∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C), (T.obj U ⟶ F) ≃ F.obj.obj (op U),
  (∀ (F G : Sheaf J (ModuleCat.{1} R)) (g : F ⟶ G) (U : C) (t : T.obj U ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U U' : C) (a : U' ⟶ U) (t : T.obj U ⟶ F),
    e F U' (T.map a ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C) (t t' : T.obj U ⟶ F), e F U (t - t') = e F U t - e F U t') := by
  let adj := sheafificationAdjunction J (ModuleCat.{1} R)
  refine ⟨fun F U => ((Iso.homCongr (i.app U).symm (Iso.refl F)).trans
    (adj.homEquiv ((FP R).obj U) F)).trans (yE R F.obj U), ?_, ?_, ?_⟩
  · intro F G g U t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  · intro F U U' a t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    have h : (i.app U').hom ≫ T.map a ≫ t =
        (presheafToSheaf J _).map ((FP R).map a) ≫ (i.app U).hom ≫ t := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact (i.hom.naturality a).symm
    rw [h]
    erw [Adjunction.homEquiv_naturality_left]
    exact yE_res R a _
  · intro F U t t'
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [Preadditive.comp_sub, ← yE_sub]
    congr 1

end General

theorem LeafSecRep_of : LeafSecRep := by
  intro B q
  let i : FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _ ≅ OU B q ⋙ H0 B q :=
    (Functor.isoWhiskerLeft (FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0)).symm
  exact general (ULift.{1} (ZMod q)) (EtTop B) (OU B q ⋙ H0 B q) i

end LateralTheory.E.LeafSecRepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.H1FiniteCoefficients
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.NoetherianChartOverlapFiniteComplement

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem exists_pow_mul_mem (S : Subalgebra A K) (u : K) (hu : u ≠ 0) (hv : u⁻¹ ∈ S) {x : K}
    (hx : x ∈ Algebra.adjoin A ((S : Set K) ∪ {u})) : ∃ n : ℕ, u⁻¹ ^ n * x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hu]; exact S.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using S.algebraMap_mem r⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x + y) = u⁻¹ ^ m * (u⁻¹ ^ n * x) + u⁻¹ ^ n * (u⁻¹ ^ m * y) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem (S.pow_mem hv _) hn) (S.mul_mem (S.pow_mem hv _) hm)
  | mul x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x * y) = (u⁻¹ ^ n * x) * (u⁻¹ ^ m * y) := by ring
    rw [this]; exact S.mul_mem hn hm

theorem pow_inv_mul_pow (t : K) (ht : t ≠ 0) (n j : ℕ) :
    (n ≤ j ∧ t⁻¹ ^ n * t ^ j = t ^ (j - n)) ∨ (j < n ∧ t⁻¹ ^ n * t ^ j = t⁻¹ ^ (n - j)) := by
  rcases le_or_gt n j with h | h
  · left
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]
  · right
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, mul_comm (t⁻¹ ^ j), mul_assoc, ← mul_pow, inv_mul_cancel₀ ht,
      one_pow, mul_one]

theorem noetherian_local_chart_overlap_finite_complement : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := by
  intro A _ _ _ K _ _ B C t hc hB _
  obtain ⟨S, hS⟩ := hB
  set R := Algebra.adjoin A ({t} : Set K)
  have hfg : (Algebra.adjoin R (S : Set K)).toSubmodule.FG :=
    fg_adjoin_of_finite S.finite_toSet (fun x hx => hc.intB x (hS ▸ Algebra.subset_adjoin hx))
  obtain ⟨G, hG⟩ := hfg
  have hRB : ∀ r : R, (r : K) ∈ B := by
    intro r
    have : R ≤ B := Algebra.adjoin_le (by simpa using hc.tB)
    exact this r.2
  have hAB : ∀ y ∈ Algebra.adjoin R (S : Set K), y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hS ▸ Algebra.subset_adjoin hx
    | algebraMap r => exact hRB r
    | add x y _ _ hx hy => exact B.add_mem hx hy
    | mul x y _ _ hx hy => exact B.mul_mem hx hy
  have hGB : ∀ g ∈ G, g ∈ B := by
    intro g hg
    have : g ∈ (Algebra.adjoin R (S : Set K)).toSubmodule := hG ▸ Submodule.subset_span hg
    exact hAB g this
  have hBR : ∀ x ∈ B, x ∈ Submodule.span R (G : Set K) := by
    intro x hx
    rw [hG]
    rw [← hS] at hx
    show x ∈ Algebra.adjoin R (S : Set K)
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap a => exact ((Algebra.adjoin R (S : Set K)).restrictScalars A).algebraMap_mem a
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  have hLex : ∀ g ∈ G, ∃ n : ℕ, t⁻¹ ^ n * g ∈ C := by
    intro g hg
    have : g ∈ Algebra.adjoin A ((C : Set K) ∪ {t}) := by
      rw [← hc.glue]; exact Algebra.subset_adjoin (Or.inl (hGB g hg))
    exact exists_pow_mul_mem C t hc.ne hc.tC this
  classical
  let Lf : K → ℕ := fun g => if h : ∃ n : ℕ, t⁻¹ ^ n * g ∈ C then Classical.choose h else 0
  let L := G.sup Lf
  have hL : ∀ g ∈ G, t⁻¹ ^ L * g ∈ C := by
    intro g hg
    have h := hLex g hg
    have hle : Lf g ≤ L := Finset.le_sup hg
    have hspec : t⁻¹ ^ Lf g * g ∈ C := by
      simp only [Lf, dif_pos h]; exact Classical.choose_spec h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm (t⁻¹ ^ Lf g), mul_assoc]
    exact C.mul_mem (C.pow_mem hc.tC _) hspec
  let N : Submodule A K := Submodule.span A ↑((G ×ˢ Finset.range L).image (fun p => t⁻¹ ^ p.2 * p.1))
  refine ⟨N, ⟨_, rfl⟩, ?_⟩
  set T := Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N with hT
  have hCT : ∀ x ∈ C, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have hBT : ∀ x ∈ B, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have core : ∀ g ∈ G, ∀ m : ℕ, t⁻¹ ^ m * g ∈ T := by
    intro g hg m
    rcases lt_or_ge m L with h | h
    · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(g, m), Finset.mem_product.mpr ⟨hg, Finset.mem_range.mpr h⟩, rfl⟩)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk, pow_add, mul_comm (t⁻¹ ^ L), mul_assoc]
      exact hCT _ (C.mul_mem (C.pow_mem hc.tC _) (hL g hg))
  have core2 : ∀ g ∈ G, ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * g ∈ T := by
    intro g hg n j
    rcases pow_inv_mul_pow t hc.ne n j with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact hBT _ (B.mul_mem (B.pow_mem hc.tB _) (hGB g hg))
    · rw [h]; exact core g hg _
  have hspan : ∀ x ∈ Submodule.span R (G : Set K), ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * x ∈ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg => exact core2 g hg
    | zero => intro n j; simp
    | add x y _ _ hx hy => intro n j; rw [mul_add]; exact T.add_mem (hx n j) (hy n j)
    | smul r x _ hx =>
      intro n j
      have hr : (r : K) ∈ (Polynomial.aeval (R := A) t).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval A t]; exact r.2
      obtain ⟨p, hp⟩ := hr
      have hp' : Polynomial.aeval t p = (r : K) := hp
      have this : r • x = (r : K) * x := rfl
      rw [this, ← hp']
      clear hp hp' this
      induction p using Polynomial.induction_on' with
      | add p q hp' hq' =>
        rw [map_add (f := _), add_mul, mul_add]
        exact T.add_mem hp' hq'
      | monomial i a =>
        rw [Polynomial.aeval_monomial]
        have : t⁻¹ ^ n * t ^ j * (algebraMap A K a * t ^ i * x) = a • (t⁻¹ ^ n * t ^ (j + i) * x) := by
          rw [Algebra.smul_def, pow_add]; ring
        rw [this]; exact T.smul_mem a (hx n (j + i))
  intro x hx
  have hx' : x ∈ Algebra.adjoin A ((B : Set K) ∪ {t⁻¹}) := hx
  obtain ⟨n, hn⟩ := exists_pow_mul_mem B t⁻¹ (inv_ne_zero hc.ne) (by rw [inv_inv]; exact hc.tB) hx'
  rw [inv_inv] at hn
  have := hspan _ (hBR _ hn) n 0
  have e : t⁻¹ ^ n * t ^ 0 * (t ^ n * x) = x := by
    rw [pow_zero, mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne, one_pow, one_mul]
  rwa [e] at this

end LateralTheory.E.NoetherianChartOverlapFiniteComplement
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BoundaryKernel
section -- merged from Development.EtaleCohomology.EtaleSheaves.BoundaryKernel.Formal
noncomputable section
open CategoryTheory Limits Opposite

namespace LateralTheory.E.H0Kernel
universe w v u

section Hom
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
open DerivedCategory HomologicalComplex

lemma Q_map_zero_of_boundary {P : C} {N : CochainComplex C ℤ} (g : (single C (.up ℤ) 0).obj P ⟶ N)
    (y : P ⟶ N.X (-1)) (hy : (singleObjXSelf (.up ℤ) 0 P).inv ≫ g.f 0 = y ≫ N.d (-1) 0) :
    Q.map g = 0 := by
  have h : Homotopy g 0 := (CochainComplex.HomComplex.Cochain.equivHomotopy g 0).symm
    ⟨CochainComplex.HomComplex.Cochain.fromSingleMk (p := 0) (n := -1) y (by simp), by
      erw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk y _ 0 0 (by simp)]
      rw [← hy, CochainComplex.HomComplex.Cochain.ofHom_zero]
      refine Eq.trans ?_ (add_zero _).symm
      ext p
      by_cases hp : p = 0
      · subst hp
        erw [CochainComplex.HomComplex.Cochain.fromSingleMk_v]
        simp
      · exact (isZero_single_obj_X (.up ℤ) 0 P p hp).eq_of_src _ _⟩
  rw [Q_map_eq_of_homotopy _ h, Functor.map_zero]

lemma exists_epi_of_chain {P : C} {N : CochainComplex C ℤ} (g : (single C (.up ℤ) 0).obj P ⟶ N)
    (hg : homologyMap g 0 = 0) : ∃ (T : C) (e : T ⟶ P) (_ : Epi e), ∀ (P' : C) (c : P' ⟶ T),
      Q.map ((single C (.up ℤ) 0).map (c ≫ e) ≫ g) = 0 := by
  have h0 : ((singleObjCyclesSelfIso (.up ℤ) 0 P).inv ≫ cyclesMap g 0) ≫ N.homologyπ 0 = 0 := by
    rw [Category.assoc, ← homologyπ_naturality, hg, comp_zero, comp_zero]
  obtain ⟨T, e, he, y, hy⟩ := (N.comp_homologyπ_eq_zero_iff_up_to_refinements (-1) 0 (by simp) _).1 h0
  refine ⟨T, e, he, fun P' c => Q_map_zero_of_boundary _ (c ≫ y) ?_⟩
  have := hy =≫ N.iCycles 0
  simp only [Category.assoc, cyclesMap_i, toCycles_i, singleObjCyclesSelfIso_inv_iCycles_assoc] at this
  simp [single_map_f_self, ← this]

lemma exists_epi {P : C} {M : DerivedCategory C} (x : (singleFunctor C 0).obj P ⟶ M)
    (hx : (DerivedCategory.homologyFunctor C 0).map x = 0) : ∃ (T : C) (e : T ⟶ P) (_ : Epi e), ∀ (P' : C) (c : P' ⟶ T),
      (singleFunctor C 0).map (c ≫ e) ≫ x = 0 := by
  let i := Q.objObjPreimageIso M
  obtain ⟨N, g, s, hs, h⟩ := left_fac (X := (single C (.up ℤ) 0).obj P) (x ≫ i.inv)
  have hg : Q.map g = x ≫ i.inv ≫ Q.map s := by
    exact ((IsIso.comp_inv_eq (Q.map s)).1 h.symm).trans (Category.assoc _ _ _)
  have h1 : homologyMap g 0 = 0 := by
    have := homologyFunctorFactors_hom_naturality g 0
    rw [hg] at this
    erw [Functor.map_comp, hx, zero_comp, zero_comp] at this
    exact zero_of_epi_comp ((homologyFunctorFactors C 0).hom.app _) this.symm
  obtain ⟨T, e, he, H⟩ := exists_epi_of_chain g h1
  refine ⟨T, e, he, fun P' c => ?_⟩
  have := H P' c
  rw [Functor.map_comp, hg] at this
  rw [← cancel_mono (i.inv ≫ Q.map s), zero_comp, Category.assoc]
  exact this
end Hom

section Sh
variable {S : Type u} [Category.{0} S] (J : GrothendieckTopology S) (R : Type 1) [Ring R]

abbrev FP : S ⥤ Sᵒᵖ ⥤ ModuleCat.{1} R :=
  yoneda ⋙ (Functor.whiskeringRight Sᵒᵖ (Type 0) (ModuleCat.{1} R)).obj (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)


variable {R} in
def gen {U V : S} (a : V ⟶ U) : ((FP R).obj U).obj (op V) := ModuleCat.freeMk (R := R) (ULift.up a)

variable {R} in
lemma gen_map {U V W : S} (a : V ⟶ U) (b : W ⟶ V) : ((FP R).obj U).map b.op (gen a) = gen (b ≫ a) :=
  ModuleCat.free_map_apply _ _

variable {R} in
lemma map_gen {U V W : S} (a : V ⟶ U) (b : W ⟶ V) : ((FP R).map a).app (op W) (gen b) = gen (b ≫ a) :=
  ModuleCat.free_map_apply _ _

variable {R} in
lemma freePresheaf_hom_ext {U : S} {F : Sᵒᵖ ⥤ ModuleCat.{1} R} (f g : (FP R).obj U ⟶ F)
    (h : f.app (op U) (gen (𝟙 U)) = g.app (op U) (gen (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨b⟩
  change f.app (op V) (gen b) = g.app (op V) (gen b)
  have hb : gen (R := R) b = ((FP R).obj U).map b.op (gen (𝟙 U)) := by rw [gen_map, Category.comp_id]
  rw [hb, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

variable {R} in
lemma freePresheaf_exists_desc {U : S} {F : Sᵒᵖ ⥤ ModuleCat.{1} R} (t : F.obj (op U)) :
    ∃ f : (FP R).obj U ⟶ F, f.app (op U) (gen (𝟙 U)) = t := by
  let φ : ∀ V : Sᵒᵖ, ((FP R).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (X := ULift.{1} (V.unop ⟶ U)) (M := F.obj V) (TypeCat.ofHom fun b => F.map b.down.op t)
  have hφ : ∀ (V : S) (b : V ⟶ U), φ (op V) (gen b) = F.map b.op t := fun V b => ModuleCat.freeDesc_apply _ _
  refine ⟨⟨φ, ?_⟩, by simpa using hφ U (𝟙 U)⟩
  rintro ⟨V⟩ ⟨W⟩ ⟨c⟩
  apply ModuleCat.free_hom_ext
  rintro ⟨b⟩
  change φ (op W) (((FP R).obj U).map (Quiver.Hom.op c) (gen b)) = F.map (Quiver.Hom.op c) (φ (op V) (gen b))
  rw [gen_map, hφ, hφ, op_comp, Functor.map_comp]
  rfl

lemma locally_factors [HasWeakSheafify J (ModuleCat.{1} R)] {U : S} {T : Sheaf J (ModuleCat.{1} R)}
    (e : T ⟶ (presheafToSheaf J _).obj ((FP R).obj U)) [he : Sheaf.IsLocallySurjective e] :
    ∃ Z ∈ J U, ∀ (U' : S) (a : U' ⟶ U), Z a → ∃ c : (presheafToSheaf J _).obj ((FP R).obj U') ⟶ T,
      (presheafToSheaf J _).map ((FP R).map a) = c ≫ e := by
  refine ⟨_, Presheaf.imageSieve_mem J e.hom ((toSheafify J ((FP R).obj U)).app (op U) (gen (𝟙 U))), ?_⟩
  rintro U' a ⟨t, ht⟩
  obtain ⟨f, hf⟩ := freePresheaf_exists_desc t
  refine ⟨⟨sheafifyLift J f T.property⟩, ?_⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((presheafToSheaf J _).obj ((FP R).obj U)).property
  change toSheafify J _ ≫ sheafifyMap J _ = toSheafify J _ ≫ sheafifyLift J f T.property ≫ e.hom
  rw [← toSheafify_naturality, toSheafify_sheafifyLift_assoc]
  apply freePresheaf_hom_ext
  change (toSheafify J ((FP R).obj U)).app (op U') (((FP R).map a).app (op U') (gen (𝟙 U'))) =
    e.hom.app (op U') (f.app (op U') (gen (𝟙 U')))
  rw [hf, map_gen]
  erw [ht]
  have hb : gen (R := R) (𝟙 U' ≫ a) = ((FP R).obj U).map a.op (gen (𝟙 U)) := by
    rw [gen_map, Category.comp_id, Category.id_comp]
  rw [hb, NatTrans.naturality_apply]
end Sh

end LateralTheory.E.H0Kernel
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace LateralTheory.E.H0Kernel
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem locSurj (B : Scheme.{0}) (q : ℕ) {F G : SShv B q} (e : F ⟶ G) [Epi e] : Sheaf.IsLocallySurjective e := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  exact (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance

theorem etale_sheaf_zeroth_cohomology_kernel_exact : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := by
  intro B q M U x hx
  obtain ⟨T, e, he, H⟩ := exists_epi (C := SShv B q)
    (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx
  have := locSurj B q e
  obtain ⟨Z, hZ, hc⟩ := locally_factors (EtTop B) (ULift.{1} (ZMod q)) e
  refine ⟨Z, hZ, fun U' a ha => ?_⟩
  obtain ⟨c, hc⟩ := hc U' a ha
  have h := H _ c
  rw [← hc] at h
  exact h

end LateralTheory.E.H0Kernel
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PointEvaluationWitness
section -- merged from Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ClosedLift
section -- merged from Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ProperBaseChangeClosedFiberStrictlyHenselianEqui
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafPtWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling

def LeafHrelZero : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E), Eqv R f F →
  ∀ n, Subsingleton (Hrel R f F n)

def LeafClosedLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {B W : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (s : Sp A ⟶ B), (∃ x, s.base x ∈ Set.range ι.base) →
  ∃ w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W, w ≫ ι = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s

def ProperBaseChangeClosedFiberStrictlyHenselianEquivalence : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ B), SH A →
  ∀ w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W,
    w ≫ ι = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s →
  Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i)

theorem LeafPtW_of (hZ : LeafHrelZero) (hL : LeafClosedLift) (hE : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence) : LateralTheory.E.SecondDegreeKilling.LeafPtW := by
  intro hH q _ k _ hq i B W Y toK ι _ V hV p hp A _ s hA hs m
  obtain ⟨hh, _⟩ := hA
  have hx : ∃ x, s.base x ∈ Set.range ι.base := by
    by_contra hc
    push Not at hc
    apply hs
    rintro _ ⟨x, rfl⟩
    have : s.base x ∈ (V : Set B) := by
      rw [hV]; exact hc x
    exact this
  obtain ⟨w, hw⟩ := hL A ι s hx
  exact hZ (ZMod q) (tw q i) (sch.map (prS p ι s)) (hE hH q k hq i toK ι p hp A s ⟨hh, ‹_›⟩ w hw) m

end LateralTheory.E.LeafPtWPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafPtWPf

theorem closedLift : LeafClosedLift := by
  intro A _ _ B W ι _ s hx
  set t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s with ht
  have hcl : IsClosed (s.base ⁻¹' Set.range ι.base) :=
    (ι.isClosedEmbedding.isClosed_range).preimage s.continuous
  obtain ⟨x, hx⟩ := hx
  have hc : s.base (IsLocalRing.closedPoint A) ∈ Set.range ι.base :=
    (IsLocalRing.specializes_closedPoint (R := A) x).mem_closed hcl hx
  have : Surjective (pullback.fst t ι) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro y
    simp only [Set.mem_preimage]
    have hy : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).base y = IsLocalRing.closedPoint A := by
      have : y = IsLocalRing.closedPoint (IsLocalRing.ResidueField A) := Subsingleton.elim _ _
      subst this
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    rw [ht, Scheme.Hom.comp_base, TopCat.comp_app, hy]
    exact hc
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst t ι)
  refine ⟨inv (pullback.fst t ι) ≫ pullback.snd t ι, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

end LateralTheory.E.LeafPtWPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.PointEvaluationWitness
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling LateralTheory.E.LeafPtWPf

theorem hrelZero : LeafHrelZero := by
  intro R _ F U E f hf n
  exact LateralTheory.E.E8.ExciseCut.LeafConeZero_of R ((chains R).map f) F (fun m => hf m) n

theorem eqv_of_iso' {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_square {R : Type} [CommRing R] {Z X Z0 X0 : Spc} (f : Z ⟶ X) (a : Z0 ⟶ Z) (g : Z0 ⟶ X0) (b : X0 ⟶ X)
    [IsIso g] (w : a ≫ f = g ≫ b) (F : Shv R) (ha : Eqv R a F) (hb : Eqv R b F) : Eqv R f F := fun n => by
  have h1 : Function.Bijective (pull R (g ≫ b) F n) := by
    have e : ⇑(pull R (g ≫ b) F n) = pull R g F n ∘ pull R b F n := funext (pull_comp R g b F n)
    rw [e]; exact (eqv_of_iso' g F n).comp (hb n)
  rw [← w] at h1
  have e : ⇑(pull R (a ≫ f) F n) = pull R a F n ∘ pull R f F n := funext (pull_comp R a f F n)
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff' (ha n) _).1 h1

theorem unit_of {k A : Type} [Field k] [CommRing A] {B : Scheme.{0}} (toK : B ⟶ Sp k) (s : Sp A ⟶ B) (q : ℕ)
    (hq : IsUnit (q : k)) : IsUnit (q : A) := by
  have := hq.map (Spec.preimage (s ≫ toK)).hom
  simpa using this

section geo
variable {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B) {A : Type} [CommRing A] [IsLocalRing A]
  (s : Sp A ⟶ B)

abbrev rA (A : Type) [CommRing A] [IsLocalRing A] : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Sp A :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

def gF : pullback (prS p ι s ≫ pullback.snd p s) (rA A) ⟶ pullback (pullback.snd p s) (rA A) :=
  pullback.lift (pullback.fst _ _ ≫ prS p ι s) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])


variable {ι p s} in
def hF (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    pullback (pullback.snd p s) (rA A) ⟶ pullback (prS p ι s ≫ pullback.snd p s) (rA A) :=
  pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w)
      (by simp only [Category.assoc]; rw [hw, pullback.condition_assoc]))
    (pullback.snd _ _) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition])

theorem eZ : pullback.fst (prS p ι s ≫ pullback.snd p s) (rA A) ≫ pullback.snd (pullback.snd p s ≫ s) ι ≫ ι =
    pullback.snd (prS p ι s ≫ pullback.snd p s) (rA A) ≫ rA A ≫ s := by
  have c : pullback.snd (pullback.snd p s ≫ s) ι ≫ ι = prS p ι s ≫ pullback.snd p s ≫ s := pullback.condition.symm
  rw [c]
  have := pullback.condition_assoc (f := prS p ι s ≫ pullback.snd p s) (g := rA A) s
  simpa only [Category.assoc] using this

theorem gF_iso (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    IsIso (gF ι p s) := by
  refine ⟨⟨hF w hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      · rw [← cancel_mono ι]
        simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
        rw [hw, eZ]
    · simp only [hF, gF, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext <;> simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]
end geo

theorem proper_base_change_closed_fiber_strictly_henselian_equivalence_holds : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp A _ _ s hA w hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  have hqA := unit_of toK s q hq
  have := hp
  have : IsProper (pullback.snd p s) := inferInstance
  have : IsProper (prS p ι s ≫ pullback.snd p s) := inferInstance
  have h1 := hE2 q A hA hqA (pullback.snd p s) i
  have h2 := hE2 q A hA hqA (prS p ι s ≫ pullback.snd p s) i
  have := gF_iso ι p s w hw
  exact eqv_of_square (sch.map (prS p ι s)) (sch.map (pullback.fst _ (rA A))) (sch.map (gF ι p s))
    (sch.map (pullback.fst _ (rA A)))
    (by rw [← Functor.map_comp, ← Functor.map_comp, gF, pullback.lift_fst]) _ h2 h1

theorem LeafPtW_of : LateralTheory.E.SecondDegreeKilling.LeafPtW :=
  LateralTheory.E.LeafPtWPf.LeafPtW_of hrelZero closedLift proper_base_change_closed_fiber_strictly_henselian_equivalence_holds

end LateralTheory.E.PointEvaluationWitness
end
end

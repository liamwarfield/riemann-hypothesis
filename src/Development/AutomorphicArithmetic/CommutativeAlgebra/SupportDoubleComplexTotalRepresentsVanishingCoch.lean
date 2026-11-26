module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_res' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map j).res g = (z.res g).map j := by
  exact (ConcreteCategory.congr_hom ((j.app _).naturality g.op) z).symm

private theorem map_face' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (z : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (z.map j).face i = (z.face i).map j :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (j.naturality (SimplexCategory.δ i).op) (op U)) z).symm

private theorem ev_delta_zero {R : Type} [CommRing R] {E : Spc} {I : Cx R} {N M s t : ℤ} (hm : N + 1 = M)
    (α : Cochain ((chains R).obj E) I N) (U : Scheme.{0}) (x : Sx E 0 U)
    (ht : -((0 : ℕ) : ℤ) + M = t) (hs : -((0 : ℕ) : ℤ) + N = s) :
    ev (R := R) (δ N M α) 0 t ht U x = Sec.map (I.d s t) (ev (R := R) α 0 s hs U x) := by
  obtain rfl : t = M := by omega
  obtain rfl : s = N := by omega
  exact (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).1 x

private theorem fam_smul_apply {R : Type} [CommRing R] {E : Spc} {Z : Sub E} {p : ℕ} {M : Shv R} (u : ℤˣ) (a : Fam Z p M)
    (U : Scheme.{0}) (z : Sx E p U) : (u • a).1 U z = u • a.1 U z := by
  rfl

theorem UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain :
    ∀ (R : Type) [CommRing R] {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m n N : ℤ), n + m = N →
    (∀ γ : Cochain ((chains R).obj E') K N, (∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx E p U), Z.mem p U z → ev (R := R) γ p s h U (z.map j) = 0) → ∃ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x ∧ Comp j γ x) ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), (famDC Z K m).Deg n x → (famDC Z K m).Deg n x' → Comp j γ x → Comp j γ x' → x = x') ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x : (famDC Z K m).Tot), Comp j γ x → Comp j (δ N (N + 1) γ) ((famDC Z K m).D n x)) ∧
    (∀ (γ γ' : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), Comp j γ x → Comp j γ' x' → Comp j (γ - γ') (x - x')) ∧
    ∀ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x → (famDC Z K m).Deg (n + 1) ((famDC Z K m).D n x) := by
  intro R _ E E' j Z K m n N hN
  have ev_nat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    let x : (famDC Z K m).Tot := fun p s =>
      if h : -(p : ℤ) + N = s + m then
        (⟨fun U z => ev (R := R) γ p (s + m) h U (z.map j),
          ⟨fun V U g z => (ev_nat γ p (s + m) h V U g (z.map j)).trans (by rw [map_res']),
           fun U z hz => hγ p (s + m) h U z hz⟩⟩ : Fam Z p (K.X (s + m)))
      else 0
    refine ⟨x, fun p s hps => ?_, fun p s h U z => ?_⟩
    · have h : ¬ (-(p : ℤ) + N = s + m) := by omega
      exact dif_neg h
    · exact congrArg (fun a : Fam Z p (K.X (s + m)) =>
        (a : (U : Scheme.{0}) → Sx E p U → Sec (K.X (s + m)) U) U z) (dif_pos h)
  · intro γ x x' hx hx' cx cx'
    funext p s
    by_cases hps : (p : ℤ) + s = n
    · have h : -(p : ℤ) + N = s + m := by omega
      change (x p s : Fam Z p (K.X (s + m))) = x' p s
      apply Subtype.ext
      funext U z
      exact (cx p s h U z).trans (cx' p s h U z).symm
    · rw [hx p s hps, hx' p s hps]
  · intro γ x cx p s h U z
    rcases p with _ | p
    · have h0 : -((0 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      rw [ev_delta_zero (s := s - 1 + m) rfl γ U (z.map j) h h0, ← cx 0 (s - 1) h0 U z]
      rfl
    · have hs : -((p + 1 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      have hp : -(p : ℤ) + N = s + m := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (rfl : N + 1 = N + 1) γ U).2 p (s - 1 + m) (s + m) hs h (z.map j),
        ← cx (p + 1) (s - 1) hs U z]
      simp only [map_face']
      rw [Finset.sum_congr rfl (fun i _ => by rw [← cx p s hp U (z.face i)])]
      have eN : (N + 1).negOnePow = (n + 1).negOnePow * m.negOnePow := by
        rw [← Int.negOnePow_add]; congr 1; omega
      have e2 := fam_smul_apply (n + 1).negOnePow
        (Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))) U z
      rw [eN, mul_smul]
      show Sec.map (K.d (s - 1 + m) (s + m)) ((x (p + 1) (s - 1) : Fam Z (p + 1) (K.X (s - 1 + m))).1 U z) +
        ((n + 1).negOnePow • Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))).1 U z = _
      rw [e2]
      rfl
  · intro γ γ' x x' cx cx' p s h U z
    rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).1 γ γ' p (s + m) h U (z.map j)).2.1,
      ← cx p s h U z, ← cx' p s h U z]
    rfl
  · intro x hx p s hps
    rcases p with _ | p
    · have h1 : ((0 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      show (Fam.map Z 0 (K.d (s - 1 + m) (s + m))) (x 0 (s - 1)) = 0
      rw [hx 0 (s - 1) h1]
      exact map_zero _
    · have h1 : ((p + 1 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      have h2 : (p : ℤ) + s ≠ n := by omega
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (x (p + 1) (s - 1)) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (x p s) = 0
      rw [hx _ _ h1, hx _ _ h2]
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (0 : Fam Z (p + 1) (K.X (s - 1 + m))) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (0 : Fam Z p (K.X (s + m))) = 0
      rw [map_zero, map_zero, smul_zero, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.DoubleMappingCylinderCochainExtension
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.PushoutCovers

private noncomputable def Fe (p : ℕ) (U : Scheme.{0}) : Spc ⥤ Type 1 :=
  ((evaluation _ _).obj (op (SimplexCategory.mk p))) ⋙ ((evaluation _ _).obj (op U)) ⋙ uliftFunctor.{1, 0}

private theorem po (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) :
    IsPushout ((Fe p U).map P.hom) ((Fe p U).map P.hom) ((Fe p U).map (dbl.inl P)) ((Fe p U).map (dbl.inr P)) := by
  have : PreservesColimit (span P.hom P.hom) (Fe p U) := by
    unfold Fe
    infer_instance
  exact (IsPushout.of_hasPushout P.hom P.hom).map (Fe p U)

private theorem cover (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U) :
    (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (po P p U).isColimit (ULift.up w)
  rcases j with _ | j
  · left
    exact ⟨Sx.map P.hom y.down, congrArg ULift.down hy⟩
  · cases j
    · left
      exact ⟨y.down, congrArg ULift.down hy⟩
    · right
      exact ⟨y.down, congrArg ULift.down hy⟩

private theorem fn (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) {T : Type 1} [Zero T] (f : Sx P.right p U → T)
    (hf : ∀ y : Sx P.left p U, f (y.map P.hom) = 0) :
    ∃ φ : Sx (dbl P) p U → T, (∀ z : Sx P.right p U, φ (z.map (dbl.inl P)) = f z) ∧ ∀ z : Sx P.right p U, φ (z.map (dbl.inr P)) = 0 := by
  have h := po P p U
  let d : (Fe p U).obj (dbl P) ⟶ T :=
    h.desc (TypeCat.ofHom fun z => f z.down) (TypeCat.ofHom fun _ => 0) (by
      ext y
      exact hf y.down)
  refine ⟨fun w => d (ULift.up w), fun z => ?_, fun z => ?_⟩
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inl_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inr_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))

private theorem res_map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map f).res g = (z.res g).map f := by
  exact (ConcreteCategory.congr_hom (CC := fun X => X) ((f.app _).naturality g.op) z).symm

end UpperTheory.PushoutCovers

open UpperTheory.PushoutCovers in
theorem UpperTheory.doubleMappingCylinder_cochain_extension :
    ∀ (R : Type) [CommRing R] (P : Arrow Spc), (∀ (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U), (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w) ∧
    ∀ (K : Cx R) (m N : ℤ) (x : (famDC (Sub.img P.hom) K m).Tot),
      ∃ γ : Cochain ((chains R).obj (dbl P)) K N, Comp (dbl.inl P) γ x ∧
        ∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx P.right p U),
          ev (R := R) γ p s h U (z.map (dbl.inr P)) = 0 := by
  intro R _ P
  refine ⟨fun p U w => cover P p U w, ?_⟩
  intro K m N x
  have key : ∀ (p : ℕ) (s' : ℤ) (U : Scheme.{0}), ∃ φ : Sx (dbl P) p U → Sec (K.X s') U,
      ∀ (s : ℤ) (e : s + m = s'), ∀ z : Sx P.right p U,
        φ (z.map (dbl.inl P)) = e ▸ (x p s).1 U z ∧ φ (z.map (dbl.inr P)) = 0 := by
    intro p s' U
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    obtain ⟨φ, h1, h2⟩ := fn P p U (T := Sec (K.X (s + m)) U) ((x p s).1 U)
      (fun y => (x p s).2.2 U _ ⟨y, rfl⟩)
    refine ⟨φ, fun s1 e z => ?_⟩
    obtain rfl : s1 = s := by omega
    exact ⟨h1 z, h2 z⟩
  choose φ hφ using key
  have nat : ∀ (p : ℕ) (s' : ℤ) (_ : -(p : ℤ) + N = s') (V U : Scheme.{0}) (g : V ⟶ U)
      (w : Sx (dbl P) p U), Sec.res g (φ p s' U w) = φ p s' V (Sx.res g w) := by
    intro p s' _ V U g w
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    rcases cover P p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [(hφ p (s + m) U s rfl z).1, res_map, (hφ p (s + m) V s rfl _).1]
      exact (x p s).2.1 V U g z
    · rw [(hφ p (s + m) U s rfl z).2, res_map, (hφ p (s + m) V s rfl _).2]
      exact map_zero _
  have components : ∀ (i j : ℤ) (hij : i + N = j), ∃ ψ : ((chains R).obj (dbl P)).X i ⟶ K.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U z,
        Sec.map ((chainsXIso R (dbl P) p).inv ≫ eqToHom (congrArg ((chains R).obj (dbl P)).X hp.symm) ≫ ψ)
          (freeGen R _ U z) = φ p j U z := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨ψ, hψ⟩ := CupSpec.free_exists (R := R) _ _ (φ k j) (nat k j hij)
      refine ⟨(chainsXIso R (dbl P) k).hom ≫ ψ, fun p hp U z => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hψ U z
    · exact ⟨0, fun p hp => by omega⟩
  choose ψ hψ using components
  let γ : Cochain ((chains R).obj (dbl P)) K N := Cochain.mk ψ
  have hγ : ∀ p s h U z, ev γ p s h U z = φ p s U z := by
    intro p s h U z
    have he := hψ _ _ h p rfl U z
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  refine ⟨γ, fun p s h U z => ?_, fun p s h U z => ?_⟩
  · rw [hγ]
    exact ((hφ p (s + m) U s rfl z).1).symm
  · rw [hγ]
    exact (hφ p s U (s - m) (by ring) z).2
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueSectionOfEtaleFaithfullyFlatDescent
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma sec_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

private lemma cover_loc (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [Algebra.Etale A C] :
    Loc (Spec (CommRingCat.of A)) (fun V g => ∃ h : V ⟶ Spec (CommRingCat.of C),
      h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g) := by
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro x
    have hff : (CommRingCat.ofHom (algebraMap A C)).hom.FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
    have hs := ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A C))).mpr hff).2
    have het : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    obtain ⟨y, hy⟩ := hs.surj x
    exact ⟨_, Spec.map (CommRingCat.ofHom (algebraMap A C)), inferInstance, het, ⟨y, hy⟩, 𝟙 _,
      Category.id_comp _⟩
  · rintro V W g k ⟨h, rfl⟩
    exact ⟨k ≫ h, Category.assoc _ _ _⟩

private lemma lift_wd {R : Type} [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
    (w : Sec F (Spec (CommRingCat.of C)))
    (hw : Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom)) w =
          Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom)) w)
    {V : Scheme.{0}} (h h' : V ⟶ Spec (CommRingCat.of C))
    (e : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = h' ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) :
    Sec.res h w = Sec.res h' w := by
  set ψ := pullback.lift h h' e ≫ (pullbackSpecIso A C C).hom with hψ
  have hL : ψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom) = h := by
    rw [hψ, Category.assoc]
    erw [pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  have hR : ψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom) = h' := by
    rw [hψ, Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    exact pullback.lift_snd _ _ _
  rw [← hL, ← hR, ← sec_res_res, hw, sec_res_res]

theorem UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent :
    ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
        [Module.FaithfullyFlat A C] [Algebra.Etale A C] (w : Sec F (Spec (CommRingCat.of C))),
        Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom)) w =
          Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom)) w →
        ∃! y : Sec F (Spec (CommRingCat.of A)), Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y = w := by
  intro R _ F A C _ _ _ _ _ w hw
  obtain ⟨S, hS, hSP⟩ := cover_loc A C
  choose lf hlf using hSP
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue R F _).2 S hS (fun V g hg => Sec.res (lf V g hg) w) (by
    intro V W g k hg
    rw [sec_res_res]
    apply lift_wd F A C w hw
    rw [Category.assoc, hlf, hlf])
  have hex : Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) a = w := by
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F _).1
    have hloc : Loc (Spec (CommRingCat.of C))
        (fun V g => S.arrows (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 _ _ _ (fun V g => S.arrows g) ⟨S, hS, fun _ _ h => h⟩
    refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _ hloc ?_
    intro V g hg
    rw [sec_res_res, ha V _ hg]
    exact lift_wd F A C w hw _ _ (hlf _ _ _)
  refine ⟨a, hex, ?_⟩
  intro y hy
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F _).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _ (cover_loc A C) ?_
  rintro V g ⟨h, rfl⟩
  rw [← sec_res_res, ← sec_res_res, hy, hex]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveClHypercohomologySingletonZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private lemma sec_comp {A B C : Shv ℤ} (p : A ⟶ B) (q : B ⟶ C) {V : Scheme.{0}} (x : Sec A V) :
    Sec.map (p ≫ q) x = Sec.map q (Sec.map p x) := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma exists_lift {M F : Shv ℤ} (g : M ⟶ (res ℤ F).X 0) (hg : g ≫ (res ℤ F).d 0 1 = 0) :
    ∃ f : M ⟶ F, f ≫ resι ℤ F = g := by
  classical
  have hinj : ∀ U : Scheme, Function.Injective (Sec.map (resι ℤ F) (U := U)) :=
    fun U => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).2.1
  have hex : ∀ (U : Scheme) (x : Sec M U), ∃ a : Sec F U, Sec.map (resι ℤ F) a = Sec.map g x := by
    intro U x
    refine ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).1 _).1 ?_
    rw [← sec_comp, hg]
    rfl
  let φ : ∀ U : Scheme, Sec M U → Sec F U := fun U x => (hex U x).choose
  have hφ : ∀ U x, Sec.map (resι ℤ F) (φ U x) = Sec.map g x := fun U x => (hex U x).choose_spec
  let η : M.obj ⟶ F.obj :=
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := fun x y => hinj _ (by
            rw [hφ]
            show (ModuleCat.Hom.hom _) (x + y) = (ModuleCat.Hom.hom _) (φ _ x + φ _ y)
            rw [map_add (f := _), map_add (f := _)]
            exact congrArg₂ (· + ·) (hφ _ x).symm (hφ _ y).symm)
          map_smul' := fun r x => hinj _ (by
            rw [hφ, RingHom.id_apply]
            have e1 := (ModuleCat.Hom.hom (g.hom.app U)).map_smul r x
            have e2 := (ModuleCat.Hom.hom ((resι ℤ F).hom.app U)).map_smul r (φ _ x)
            exact e1.trans ((congrArg _ (hφ _ x).symm).trans e2.symm)) }
      naturality := by
        intro U V h
        ext x
        apply hinj
        have n1 := congrArg (fun k => ModuleCat.Hom.hom k x) (g.hom.naturality h)
        have n2 := congrArg (fun k => ModuleCat.Hom.hom k (φ _ x)) ((resι ℤ F).hom.naturality h)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n1 n2
        show Sec.map (resι ℤ F) (φ _ ((ModuleCat.Hom.hom (M.obj.map h)) x)) =
          Sec.map (resι ℤ F) ((ModuleCat.Hom.hom (F.obj.map h)) (φ _ x))
        rw [hφ]
        refine n1.trans ?_
        refine Eq.trans ?_ n2.symm
        exact congrArg _ (hφ _ x).symm }
  refine ⟨⟨η⟩, (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (⟨η⟩ ≫ resι ℤ F)).2.2.2 g (fun U a => ?_)⟩
  rw [sec_comp]
  exact hφ U a

set_option backward.isDefEq.respectTransparency false in
private lemma sgl_f {M F : Shv ℤ} (f : M ⟶ F) :
    sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F).f 0 = f ≫ resι ℤ F := by
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  have h : sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f).f 0 = f ≫ sglι F := by
    simp [sglι, CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]
  rw [h, Category.assoc, (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.1]

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.bijective_cl_hypercohomology_singleton_zero :
    ∀ (M F : Shv ℤ), Function.Bijective (cl : (M ⟶ F) → HK ℤ (sgl M) F 0) := by
  intro M F
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl M).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hL : IsZero ((res ℤ F).X (-1)) := by
    haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.1
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by norm_num)
  have hβ0 : ∀ β : Cochain (sgl M) (res ℤ F) (-1), β = 0 := by
    intro β
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = -1 := by omega
      exact hL.eq_of_tgt _ _
    · exact (hz p hp).eq_of_src _ _
  have hcob : ∀ x : Cocycle (sgl M) (res ℤ F) 0, x ∈ coboundaries (sgl M) (res ℤ F) 0 → x = 0 := by
    intro x hx
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x (-1) (by norm_num)).1 hx
    apply Cocycle.ext
    rw [← hβ, hβ0 β, δ_zero]
    rfl
  have hmono : Mono (resι ℤ F) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.1
  have hsg : IsIso (sglι M) := by
    dsimp [sglι]
    infer_instance
  constructor
  · intro f f' h
    have h1 : Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F)
        = Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f' ≫ resAug F) := by
      have := hcob _ ((CohomologyClass.mk_eq_zero_iff _).1
        (by rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 h))
      exact sub_eq_zero.1 this
    have h2 := congrArg (fun x : Cocycle (sgl M) (res ℤ F) 0 =>
      (x : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0)) h1
    simp only [Cocycle.ofHom_coe, Cochain.ofHom_v] at h2
    apply (cancel_mono (resι ℤ F)).1
    rw [← sgl_f, ← sgl_f, h2]
  · intro c
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    have hz1 : (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0) ≫ (res ℤ F).d 0 1 = 0 := by
      have e := congrArg (fun w : Cochain (sgl M) (res ℤ F) 1 => w.v 0 1 (zero_add 1))
        ((Cocycle.mem_iff 0 1 (zero_add 1) _).1 z.2)
      simp only [δ_zero_cochain_v, Cochain.zero_v] at e
      rwa [(hz 1 one_ne_zero).eq_of_tgt ((sgl M).d 0 1) 0, zero_comp, sub_zero] at e
    obtain ⟨f, hf⟩ := exists_lift (sglι M ≫ (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0))
      (by rw [Category.assoc, hz1, comp_zero])
    refine ⟨f, ?_⟩
    show CohomologyClass.mk _ = CohomologyClass.mk z
    congr 1
    apply Cocycle.ext
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [add_zero] at hpq
    subst hpq
    by_cases hp : p = 0
    · subst hp
      rw [Cocycle.ofHom_coe, Cochain.ofHom_v, ← cancel_epi (sglι M), sgl_f, hf]
    · exact (hz p hp).eq_of_src _ _
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.DescentOfIntegralDescentTruncation
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyBaseChangeIntegralSurjectiveCech
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

private theorem level_rel {Y X Y₀ S S₀ L : Scheme.{0}} (k : Y ⟶ X) (r : X ⟶ S) (c : S₀ ⟶ S)
    (k₀ : Y₀ ⟶ pullback r c) (m : cech k₀ ⟶ cech k)
    (hm : IsPullback m (cechAug k₀) (cechAug k) (sch.map (pullback.fst r c)))
    (p : SimplexCategoryᵒᵖ) (l : L ⟶ X) (e : yoneda.obj L ≅ (cech k).obj p)
    (he : e.hom ≫ (cechAug k).app p = yoneda.map l) (q : ℕ) (i n : ℤ)
    (h : RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst (l ≫ r) c))) :
    RelZS (ZMod q) (tw q i) n (disc.map (m.app p)) := by
  have hp : IsPullback (m.app p) ((cechAug k₀).app p) ((cechAug k).app p)
      (yoneda.map (pullback.fst r c)) :=
    hm.map ((evaluation _ _).obj p)
  have hB : IsPullback (m.app p ≫ e.inv) ((cechAug k₀).app p) (yoneda.map l)
      (yoneda.map (pullback.fst r c)) := by
    refine hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.refl_hom, Iso.symm_hom, ← he]
      erw [Iso.inv_hom_id_assoc, Category.comp_id]
    · erw [Category.comp_id]
      try erw [Category.id_comp]
  let φ : pullback (l ≫ r) c ⟶ pullback r c :=
    pullback.lift (pullback.fst (l ≫ r) c ≫ l) (pullback.snd (l ≫ r) c)
      (by simp [pullback.condition])
  have hφ₁ : φ ≫ pullback.fst r c = pullback.fst (l ≫ r) c ≫ l := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd r c = pullback.snd (l ≫ r) c := pullback.lift_snd _ _ _
  have hS : IsPullback (pullback.fst (l ≫ r) c) φ l (pullback.fst r c) := by
    refine IsPullback.of_bot ?_ hφ₁.symm (IsPullback.of_hasPullback r c)
    rw [hφ₂]
    exact IsPullback.of_hasPullback (l ≫ r) c
  have hA := hS.map yoneda
  let ι := IsPullback.isoIsPullback _ _ hA hB
  have hι : ι.hom ≫ m.app p ≫ e.inv = yoneda.map (pullback.fst (l ≫ r) c) :=
    IsPullback.isoIsPullback_hom_fst _ _ hA hB
  have key : yoneda.map (pullback.fst (l ≫ r) c) ≫ e.hom = ι.hom ≫ m.app p := by
    rw [← hι]
    simp
  refine RelZS.of_iso (ZMod q) (tw q i) (sch.map (pullback.fst (l ≫ r) c)) (disc.map (m.app p))
    (disc.mapIso ι) (disc.mapIso e) ?_ n h
  have := congrArg (fun f => disc.map f) key
  simp only [Functor.map_comp] at this
  exact this

private noncomputable def wpOne {A B : Scheme.{0}ᵒᵖ ⥤ Type} (f : A ⟶ B) :
    A ≅ widePullback B (fun _ : Fin (0 + 1) => A) (fun _ => f) where
  hom := WidePullback.lift f (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  inv := WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  hom_inv_id := WidePullback.lift_π _ _ _ _ _
  inv_hom_id := by
    apply WidePullback.hom_ext (fun _ : Fin (0 + 1) => f)
    · intro j
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      rw [Category.assoc, WidePullback.lift_π]
      simp
    · rw [Category.assoc, WidePullback.lift_base]
      simp

private noncomputable def cech_zero {Y X : Scheme.{0}} (k : Y ⟶ X) :
    yoneda.obj Y ≅ (cech k).obj (Opposite.op (SimplexCategory.mk 0)) :=
  wpOne (yoneda.map k)

private theorem cech_zero_aug {Y X : Scheme.{0}} (k : Y ⟶ X) :
    (cech_zero k).hom ≫ (cechAug k).app (Opposite.op (SimplexCategory.mk 0)) = yoneda.map k :=
  WidePullback.lift_base _ _ _ _

theorem UpperTheory.cohomology_base_change_integral_surjective_cech :
    B4 → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) [IsIntegralHom k] [Surjective k] (r : X ⟶ S) (c : S₀ ⟶ S), IsUnit (q : Γ(X, ⊤)) → ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (pullback r c)) (a : E ⟶ sch.obj X), u ≫ a = a' ≫ sch.map (pullback.fst r c) ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧ (∀ p : ℕ, ∃ (L : Scheme.{0}) (l : L ⟶ X), IsIntegralHom l ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (l ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (k ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) := by
  intro b4 q i Y X S S₀ k _ _ r c hq
  have hP := IsPullback.of_hasPullback k (pullback.fst r c)
  obtain ⟨u, hu, -⟩ := GlobalTheory.cech_baseChange Y X _ _ _ _ k (pullback.fst r c) hP
  have hq₀ : IsUnit (q : Γ(pullback r c, ⊤)) := by
    simpa using hq.map (pullback.fst r c).appTop.hom
  haveI : IsIntegralHom (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  haveI : Surjective (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  refine ⟨_, _, u, cechAug _, cechAug k, hu.w, b4 q k hq i, b4 q _ hq₀ i, fun p => ?_, fun n h => ?_⟩
  · obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.EtC.cech_level_representable (@IsIntegralHom) Y X k inferInstance
      (Opposite.op (SimplexCategory.mk p))
    haveI : IsIntegralHom π := hπ
    exact ⟨Z, π ≫ k, inferInstance, fun n h =>
      level_rel k r c _ u hu _ (π ≫ k) e he q i n h⟩
  · exact level_rel k r c _ u hu _ k (cech_zero k) (cech_zero_aug k) q i n h
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

theorem UpperTheory.descent_of_integral_descent_truncation :
    LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels → LateralTheory.E.t_E2Cut.Desc := by
  intro hT hH q i A _ _ hq P p hyp
  have neg : ∀ n : ℤ, n < 0 → ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A))) := by
    intro n hn X g
    refine ⟨fun m hm => ?_, fun x y _ => ?_⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1
        (sch.obj (pullback g (LateralTheory.E.t_E2Cut.cpt A))) m (by omega)
      exact fun y => ⟨0, Subsingleton.elim _ _⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj X) n hn
      exact Subsingleton.elim _ _
  let C : ℤ → Prop := fun n => ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      (∃ h : X ⟶ P, IsIntegralHom h ∧ g = h ≫ p) →
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A)))
  have step : ∀ n : ℤ, (∀ m, m < n → C m) → C n := by
    intro n ih X g hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨Y, k, hk, hks, hpb⟩ := hyp X h hh
    haveI := hk
    haveI := hks
    obtain ⟨U, E, u, a', a, hcomm, ha, ha', hall, h0⟩ :=
      UpperTheory.cohomology_base_change_integral_surjective_cech hH.b4 q i k (h ≫ p) (LateralTheory.E.t_E2Cut.cpt A)
        (LateralTheory.E.t_E2Cut.unit_of hq (h ≫ p))
    have hu : RelZS (ZMod q) (tw q i) n u := by
      refine hT (ZMod q) (tw q i) u n (fun p' m hm => ?_) ?_
      · obtain ⟨L, l, hl, hL⟩ := hall p'
        apply hL m
        haveI := hl
        haveI := hh
        exact ih m hm (l ≫ h ≫ p) ⟨l ≫ h, inferInstance, by simp [Category.assoc]⟩
      · apply h0 n
        exact ⟨fun m' _ => (hpb m').2, (hpb n).1⟩
    exact transfer (ZMod q) (tw q i) u _ a' a hcomm ha ha' n hu
  have all : ∀ n, C n := by
    have key : ∀ k : ℕ, ∀ n : ℤ, n < k → C n := by
      intro k
      induction k with
      | zero =>
        intro n hn X g _
        exact neg n (by exact_mod_cast hn) g
      | succ k ihk =>
        intro n hn
        by_cases hn' : n < k
        · exact ihk n hn'
        · exact step n (fun m hm => ihk m (by push_cast at hn ⊢; omega))
    intro n
    exact key (n.toNat + 1) n (by omega)
  have hp : ∃ h : P ⟶ P, IsIntegralHom h ∧ p = h ≫ p := ⟨𝟙 P, inferInstance, by simp⟩
  intro n
  exact ⟨(all n p hp).2, (all (n + 1) p hp).1 n rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsCurvePullbackOfIsCurveBaseChange
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_point {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, ∀ r, φ r = 0 → r ∈ m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := inferInstance
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance
  let e : k ≃ₐ[k] (R ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : e.symm (Ideal.Quotient.mk m r) = 0 := hr
  exact (map_eq_zero_iff e.symm e.symm.injective).mp h0

private theorem dom_fg {k R A ι : Type} [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing A] [IsDomain A] [Algebra k A] (e : Module.Basis ι k A)
    (s t : Finset ι) (a b : ι → R)
    (h : (∑ i ∈ s, a i ⊗ₜ[k] e i) * (∑ j ∈ t, b j ⊗ₜ[k] e j) = 0) :
    (∀ i ∈ s, a i = 0) ∨ (∀ j ∈ t, b j = 0) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨i0, hi0, ha⟩, ⟨j0, hj0, hb⟩⟩ := hcon
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hab : a i0 * b j0 ≠ 0 := mul_ne_zero ha hb
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot_of_noZeroDivisors
  have hnot : a i0 * b j0 ∉ (⊥ : Ideal R).jacobson := by
    rw [hjac]
    simpa using hab
  obtain ⟨m, hm, hnm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ a i0 * b j0 ∉ m := by
    by_contra hne
    push_neg at hne
    apply hnot
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hne J hJ
  haveI := hm
  obtain ⟨φ, hφ⟩ := exists_point (k := k) m
  have hφa : φ (a i0) ≠ 0 := fun h0 => hnm (m.mul_mem_right _ (hφ _ h0))
  have hφb : φ (b j0) ≠ 0 := fun h0 => hnm (m.mul_mem_left _ (hφ _ h0))
  let ψ : R ⊗[k] A →ₐ[k] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId k A).comp φ) (AlgHom.id k A) (fun _ _ => Commute.all _ _)
  have hψ : ∀ (c : ι → R) (u : Finset ι),
      ψ (∑ i ∈ u, c i ⊗ₜ[k] e i) = ∑ i ∈ u, φ (c i) • e i := by
    intro c u
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ψ, map_sum, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  have h2 := congrArg ψ h
  rw [map_mul, hψ, hψ, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφa ((linearIndependent_iff'.mp e.linearIndependent) s (fun i => φ (a i)) h3 i0 hi0)
  · exact hφb ((linearIndependent_iff'.mp e.linearIndependent) t (fun j => φ (b j)) h3 j0 hj0)

private theorem dom_tensor (k K L : Type) [Field k] [IsAlgClosed k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] : IsDomain (L ⊗[k] K) := by
  classical
  let e := Module.Basis.ofVectorSpace k K
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  suffices hnz : NoZeroDivisors (L ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy => ?_⟩
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  have hrep : ∀ z : L ⊗[k] K, z = ∑ i ∈ (E z).support, (E z) i ⊗ₜ[k] e i := by
    intro z
    conv_lhs => rw [← E.symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]
  let S : Finset L := (E x).support.image (E x) ∪ (E y).support.image (E y)
  let R := Algebra.adjoin k (S : Set L)
  haveI : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp (Subalgebra.fg_adjoin_finset S)
  have hmem : ∀ (z : L ⊗[k] K), (z = x ∨ z = y) → ∀ i, (E z) i ∈ R := by
    rintro z hz i
    by_cases hi : i ∈ (E z).support
    · apply Algebra.subset_adjoin
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact R.zero_mem
  let a : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E x) i, hmem x (Or.inl rfl) i⟩
  let b : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E y) i, hmem y (Or.inr rfl) i⟩
  let j : R ⊗[k] K →ₐ[k] L ⊗[k] K := Algebra.TensorProduct.map R.val (AlgHom.id k K)
  have hj : Function.Injective j := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := K) R.val.toLinearMap Subtype.val_injective
    exact this
  have hja : j (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) = x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [hrep x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, a]
  have hjb : j (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [hrep y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, b]
  have hprod : (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) * (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = 0 := by
    apply hj
    rw [map_mul, hja, hjb, hxy, map_zero]
  rcases dom_fg (k := k) e _ _ a b hprod with h0 | h0
  · left
    rw [hrep x]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [a, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]
  · right
    rw [hrep y]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [b, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]

private theorem gi (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI := dom_tensor k K L
  let e : Y ≅ Spec (CommRingCat.of (L ⊗[k] K)) := h.isoPullback ≪≫ pullbackSpecIso k L K
  haveI : Nonempty Y := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

theorem UpperTheory.isCurve_pullback_of_isCurve_baseChange :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → IsCurve (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  intro k L _ _ _ _ C c hc
  obtain ⟨h1, h2, h3⟩ := hc
  haveI := gi k L
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg
  set p := pullback.fst c g with hp
  haveI : GeometricallyIrreducible p := inferInstance
  haveI : GeometricallyReduced p := inferInstance
  haveI : Flat p := inferInstance
  haveI : Finite (irreducibleComponents C) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  haveI hred : IsReduced (pullback c g) :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  set η := genericPoint C
  let ξ : ↥(pullback c g) := p.fiberι η (genericPoint (p.fiber η))
  have hall : ∀ q : ↥(pullback c g), ξ ⤳ q := by
    intro q
    have h0 : η ⤳ p q := genericPoint_specializes _
    obtain ⟨q', hq', hpq'⟩ := hgen h0
    have hmem : q' ∈ Set.range (p.fiberι η) := by
      rw [p.range_fiberι]
      exact hpq'
    obtain ⟨r, rfl⟩ := hmem
    exact ((genericPoint_specializes r).map (p.fiberι η).continuous).trans hq'
  haveI hirr : IrreducibleSpace ↥(pullback c g) := by
    rw [irreducibleSpace_def]
    have hcl : closure ({ξ} : Set ↥(pullback c g)) = Set.univ :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (IsPullback.of_hasPullback c g) h3
end
